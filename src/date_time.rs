//! Date-time processing.

use super::ParseDateTimeError;

const DAYS_IN_MONTH: [u8; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
const DAYS_IN_MONTH_LEAP: [u8; 12] = [31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
const DOY_AT_MONTH: [i32; 12] = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
const DOY_AT_MONTH_LEAP: [i32; 12] = [0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335];

/// Returns whether the year is a leap year for a 64-bit signed year.
///
/// The argument is the proleptic Gregorian year, with the ISO 8601
/// interpretation of year 0 as year 1 BC. Year 0 does not obey the usual rule
/// and is considered a leap year.
///
/// The whole `i64` value range is supported.
pub(crate) const fn is_leap(year: i64) -> bool {
    (year & 0b11) == 0 && (year % 100 != 0 || year % 400 == 0)
}

/// Calculates the number of days in a month.
pub(crate) const fn days_in_month(year: i32, month: u8) -> u8 {
    let month_idx = (month - 1) as usize;

    if is_leap(year as i64) {
        DAYS_IN_MONTH_LEAP[month_idx]
    } else {
        DAYS_IN_MONTH[month_idx]
    }
}

/// Calculates the 0-based day of the year.
pub(crate) const fn day_of_year(year: i32, month: u8, day: u8) -> i32 {
    let month_idx = (month - 1) as usize;
    let table = if is_leap(year as i64) {
        &DOY_AT_MONTH_LEAP
    } else {
        &DOY_AT_MONTH
    };

    (day - 1) as i32 + table[month_idx]
}

/// Calculates the month and the day of the month for a 0-based day of the year.
pub(crate) fn month_and_day_of_month(year: i64, doy: i32) -> (u8, u8) {
    let table = if is_leap(year) {
        &DOY_AT_MONTH_LEAP
    } else {
        &DOY_AT_MONTH
    };

    let idx = table.binary_search(&doy).unwrap_or_else(|e| e - 1);
    let month = idx as u8 + 1;
    let day = (doy - table[idx]) as u8 + 1;

    (month, day)
}

/// Returns the number of elapsed days since the first day of year 0 to the
/// first day of the provided year.
///
/// The argument is the proleptic Gregorian year, with the ISO 8601
/// interpretation of year 0 as year 1 BC.
///
/// The result is negative for negative years.
pub(crate) const fn days_from_year_0(year: i32) -> i64 {
    let year = year as i64;
    let offset = (year > 0) as i64;
    let y = year - offset;
    let m4 = y / 4 + offset;
    let m100 = y / 100;
    let m400 = m100 / 4;

    year * 365 + m4 - m100 + m400
}

/// Returns the year, the day of the year and the second of the day for the
/// provided timestamp.
///
/// This will not overflow provided that the timestamp is in the range ±2^97.
pub(crate) fn secs_to_date_time(secs_from_year_0: i128) -> (i64, i32, i64) {
    // Find the nearest 400-year boundary that is before or at the date. This
    // requires a division with rounding-down behavior even when the timestamp
    // is negative. We also need to unconditionally prevent overflow when
    // translating the timestamp, hence the baroque code...
    let mut n_period = (secs_from_year_0 / (146097 * 86400)) as i64;
    let mut sec = (secs_from_year_0 % (146097 * 86400)) as i64;
    if sec < 0 {
        n_period -= 1;
        sec += 146097 * 86400;
    }

    // -- `sec` is now guaranteed to be positive.

    let mut year = 400 * n_period;
    let mut day = sec / 86400;
    let sec = sec - day * 86400;
    if day < 366 {
        return (year, day as i32, sec);
    }

    // Find the nearest 100-year, 4-year and 1-year boundaries that are before
    // or at the date.
    for (years_in_period, days_in_period, starts_with_non_leap_year) in
        [(100, 36524, 1), (4, 1461, 0), (1, 365, 1)]
    {
        day -= starts_with_non_leap_year;
        let n_period = day / days_in_period;
        year += years_in_period * n_period;
        day -= n_period * days_in_period;
        if day < (366 - starts_with_non_leap_year) {
            return (year, day as i32, sec);
        }
        day += starts_with_non_leap_year;
    }

    unreachable!();
}

/// Parses an RFC3339-like TAI date-time with signed years. Since TAI is
/// timezone-independent, time zones and offsets suffixes are invalid.
///
/// Expected format:
///
/// `[±][Y]...[Y]YYYY-MM-DD hh:mm:ss[.d[d]...[d]]`
///
/// or:
///
/// `[±][Y]...[Y]YYYY-MM-DD'T'hh:mm:ss[.d[d]...[d]]`
///
/// where delimiter `T` between date and time may also be a lowercase `t`.
///
/// The year may take any value within `±i32::MAX`.
#[allow(clippy::type_complexity)]
pub(crate) fn parse_date_time(
    stream: &str,
) -> Result<(i32, u8, u8, u8, u8, u8, u32), ParseDateTimeError> {
    // Expect 2 leading digits optionally followed by one of the provided
    // delimiters, and return them as a single `u8`, together with the remaining part
    // of the stream if a delimiter was found.
    fn pull_two_digits<'a, E>(
        stream: &'a str,
        delimiter: &'a [char],
        missing_delimiter_error: E,
    ) -> Result<(u8, Result<&'a str, E>), ParseDateTimeError> {
        let (token, stream) = stream
            .split_once(delimiter)
            .map(|(t, s)| (t, Ok(s)))
            .unwrap_or((stream, Err(missing_delimiter_error)));

        if token.len() != 2 {
            return Err(ParseDateTimeError::InvalidFieldWidth);
        }

        token
            .parse()
            .map_err(|_| ParseDateTimeError::InvalidFieldValue)
            .map(|token| (token, stream))
    }

    // Pull the leading sign of the year, if any.
    let (stream, sign) = match stream.chars().next() {
        Some('+') => (&stream[1..], 1),
        Some('-') => (&stream[1..], -1),
        _ => (stream, 1),
    };

    // Pull the year.
    let (year, stream) = stream
        .split_once('-')
        .ok_or(ParseDateTimeError::MissingField)?;
    let year_digits = year.len();
    if year_digits < 4 {
        return Err(ParseDateTimeError::InvalidFieldWidth);
    }
    let year = year
        .parse()
        .map(|year: i32| sign * year)
        .map_err(|_| ParseDateTimeError::InvalidFieldValue)?;

    // Pull month, day, hour, minute and second.
    let (month, stream) = pull_two_digits(stream, &['-'], ParseDateTimeError::MissingField)?;
    let (day, stream) =
        pull_two_digits(stream?, &[' ', 'T', 't'], ParseDateTimeError::MissingField)?;
    let (hour, stream) = pull_two_digits(stream?, &[':'], ParseDateTimeError::MissingField)?;
    let (min, stream) = pull_two_digits(stream?, &[':'], ParseDateTimeError::MissingField)?;
    let (sec, stream) = pull_two_digits(stream?, &['.'], ())?;

    // Parse the fraction.
    let mut nano = 0u32;
    match stream {
        Ok("") => return Err(ParseDateTimeError::MissingField),
        Ok(stream) => {
            let mut weight = 100_000_000;
            for c in stream.chars() {
                // All digits are validated even if their weight is 0.
                let digit = c
                    .to_digit(10)
                    .ok_or(ParseDateTimeError::InvalidFieldValue)?;
                nano += digit * weight;
                weight /= 10;
            }
        }
        Err(_) => {}
    }

    Ok((year, month, day, hour, min, sec, nano))
}
