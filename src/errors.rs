//! Error types.

use core::fmt;

/// The error type returned when the result of a conversion to or from a
/// [`TaiTime`](crate::TaiTime) is outside the representable range, or the
/// conversion would cause the result to overflow.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct OutOfRangeError(pub(crate) ());

impl fmt::Display for OutOfRangeError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        "timestamp out of representable range".fmt(fmt)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OutOfRangeError {}

/// The error type returned when date-time components are invalid or correspond
/// to a timestamp outside the representable range.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum DateTimeError {
    /// The month is not between 1 and 12.
    InvalidMonth(u8),
    /// The day of the month is less than 1, or more than the maximum value for
    /// this combination of year and month.
    InvalidDayOfMonth(u8),
    /// The hour field value is not between 0 and 23.
    InvalidHour(u8),
    /// The minute field value is not between 1 and 59.
    InvalidMinute(u8),
    /// The second field value is not between 1 and 59.
    InvalidSecond(u8),
    /// The nanosecond field value is more than 999 999 999.
    InvalidNanosecond(u32),
    /// This date-time value cannot be represented as a TAI timestamp with the
    /// specified epoch.
    OutOfRange,
}

impl fmt::Display for DateTimeError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidMonth(month) => write!(fmt, "month numeral '{}' is not valid", month),
            Self::InvalidDayOfMonth(day) => {
                write!(fmt, "day of month '{}' is not valid for this date", day)
            }
            Self::InvalidHour(hour) => write!(fmt, "hour numeral '{}' is not valid", hour),
            Self::InvalidMinute(min) => write!(fmt, "minute numeral '{}' is not valid", min),
            Self::InvalidSecond(sec) => write!(fmt, "second numeral '{}' is not valid", sec),
            Self::InvalidNanosecond(nanosec) => {
                write!(fmt, "nanosecond value '{}' is not valid", nanosec)
            }
            Self::OutOfRange => "timestamp outside representable range".fmt(fmt),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DateTimeError {}

/// The error type returned when a date-time string is invalid or corresponds to
/// a timestamp outside the representable range.
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ParseDateTimeError {
    /// A field value is either not of the expected numeric type or is out of
    /// range for the expected numeric type.
    InvalidFieldValue,
    /// The width of a fixed-width or minimum-width field is invalid.
    InvalidFieldWidth,
    /// A field is missing.
    MissingField,
    /// One of the field value is out of its expected range, or the
    /// corresponding timestamp is outside the representable range.
    RangeError(DateTimeError),
}

impl fmt::Display for ParseDateTimeError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidFieldValue => "one of the fields is invalid".fmt(fmt),
            Self::InvalidFieldWidth => "the width of one of the fields is invalid".fmt(fmt),
            Self::MissingField => "a fields is missing".fmt(fmt),
            Self::RangeError(err) => err.fmt(fmt),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseDateTimeError {}
