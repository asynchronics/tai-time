//! A nanosecond-precision monotonic clock timestamp based on the TAI time
//! standard.
//!
//! # Overview
//!
//! While Rust's standard library already provides the [`std::time::Instant`]
//! monotonic timestamp, its absolute value is opaque. In many scientific and
//! engineering applications such as simulations, GNSS and synchronized systems,
//! monotonic timestamps based on absolute time references are required.
//!
//! This crate provides a fairly unopinionated timestamp for such applications
//! with a focus on simplicity, adherence to Rust's `std::time` idioms and
//! interoperability with the [`std::time::Duration`] type.
//!
//! A [`TaiTime`] timestamp specifies a [TAI] point in time. It is represented
//! as a 64-bit signed number of seconds and a positive number of nanoseconds,
//! relative to 1970-01-01 00:00:00 TAI or to any arbitrary epoch. This
//! timestamp format has a number of desirable properties:
//!
//! - it is computationally efficient for arithmetic operations involving the
//!   standard [`Duration`] type, which uses a very similar internal
//!   representation,
//! - when a 1970 epoch is chosen (see [`MonotonicTime`]):
//!   * exact conversion to a Unix timestamp is trivial and only requires
//!     subtracting from this timestamp the number of leap seconds between TAI
//!     and UTC time,
//!   * it constitutes a strict 96-bit superset of 80-bit PTP IEEE-1588
//!     timestamps, a widely used standard for high-precision time distribution,
//!   * it is substantially similar (though not strictly identical) to the
//!     [TAI64N] time format,
//! - with a custom epoch, other monotonic clocks such as the Global Position
//!   System clock, the Galileo System Time clock and the BeiDou Time clock can
//!   be represented (see [`GpsTime`], [`GstTime`], [`BdtTime`], [`Tai1958Time`]
//!   and [`Tai1972Time`]).
//!
//! [`MonotonicTime`], an alias for [`TaiTime`] with an epoch set at 1970-01-01
//! 00:00:00 TAI, is the recommended timestamp choice when no specific epoch is
//! mandated.
//!
//! [TAI]: https://en.wikipedia.org/wiki/International_Atomic_Time
//! [TAI64N]: https://cr.yp.to/libtai/tai64.html
//!
//!
//! # Design choices and limitations
//!
//! Leap seconds are never automatically computed during conversion to/from
//! UTC-based timestamps. This is intentional: since leap seconds cannot be
//! predicted far in the future, any attempt to "hide" their existence from user
//! code would lend a false sense of security and, down the line, would make it
//! more difficult to identify failures subsequent to the introduction of new
//! leap seconds.
//!
//!
//! # Features flags
//!
//! ### Support for `no-std`
//!
//! By default, this crate enables the `std` feature to access the operating
//! system clock and allow conversion to/from `time::SystemTime`, but it can be
//! made `no-std`-compatible by specifying `default-features = false`.
//!
//! ### Support for time-related crates
//!
//! Conversion methods to and from UTC date-time stamps from the [chrono] crate
//! are available with the `chrono` feature.
//!
//! [chrono]: https://crates.io/crates/chrono
//!
//! ### Support for the TAI system clock
//!
//! On Linux only, it is possible to directly read the TAI time from the system
//! clock by activating the `tai_clock` feature. Be sure to read about possible
//! caveats in [`TaiTime::now_from_tai_clock`].
//!
//! ### Serialization
//!
//! `TaiTime` and related error types can be (de)serialized with `serde` by
//! activating the `serde` feature.
//!
//!
//! # Examples
//!
//! Basic usage:
//!
//! ```
//! use tai_time::{GpsTime, MonotonicTime};
//!
//! // A timestamp dated 2009-02-13 23:31:30.987654321 TAI.
//! // (same value as Unix timestamp for 2009-02-13 23:31:30.987654321 UTC).
//! let t0 = MonotonicTime::new(1_234_567_890, 987_654_321);
//!
//! // Current TAI time based on system clock, assuming 37 leap seconds.
//! let now = MonotonicTime::now(37).unwrap();
//! println!("Current TAI time: {}", now);
//!
//! // Elapsed time since timestamp.
//! let dt = now.duration_since(t0);
//! println!("Elapsed: {}s, {}ns", dt.as_secs(), dt.subsec_nanos());
//!
//! // Print out the current GPS timestamp.
//! let gps_t0: GpsTime = t0.to_tai_time().unwrap();
//! println!("GPS timestamp: {}s, {}ns", gps_t0.as_secs(), gps_t0.subsec_nanos());
//! ```
//!
//! Conversion to and from date-time representations:
//!
//! ```
//! use tai_time::{MonotonicTime, Tai1958Time};
//!
//! // The `FromStr` implementation accepts date-time stamps with the format:
//! // [±][Y]...[Y]YYYY-MM-DD hh:mm:ss[.d[d]...[d]]
//! // or:
//! // [±][Y]...[Y]YYYY-MM-DD'T'hh:mm:ss[.d[d]...[d]]
//! let t0 = MonotonicTime::from_date_time(2222, 11, 11, 12, 34, 56, 789000000).unwrap();
//! assert_eq!("2222-11-11 12:34:56.789".parse(), Ok(t0));
//!
//! assert_eq!(
//!     Tai1958Time::new(0, 123456789).to_string(),
//!     "1958-01-01 00:00:00.123456789"
//! );
//! ```
//!
//! Reading TAI time directly from the system clock (Linux-only, requires
//! feature `tai_clock`):
//!
//! ```
//! use tai_time::MonotonicTime;
//!
//! let now = MonotonicTime::now_from_tai_clock().unwrap();
//!
//! println!("Current TAI time: {}", now);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

mod date_time;
mod errors;

use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::str::FromStr;
use core::time::Duration;

use date_time::*;
pub use errors::{DateTimeError, OutOfRangeError, ParseDateTimeError};

const NANOS_PER_SEC: u32 = 1_000_000_000;
const UNIX_EPOCH_YEAR: i32 = 1970;

/// Recommended [`TaiTime`] alias for the general case, using an epoch set at
/// 1970-01-01 00:00:00 TAI.
///
/// The epoch of this timestamp coincides with the PTP epoch as defined by the
/// IEEE 1588-2008 standard, and with the
/// [`TAI64`](https://cr.yp.to/libtai/tai64.html) epoch. It is, however,
/// distinct from the Unix epoch, which is set at 1970-01-01 00:00:00 UTC.
///
/// When no specific epoch is required, this timestamp should be considered the
/// most sensible default as it makes it possible to easily convert TAI
/// timestamps to Unix timestamps by simple subtraction of the TAI - UTC leap
/// seconds.
///
/// # Examples
///
/// ```
/// use tai_time::MonotonicTime;
///
/// // Set the timestamp one nanosecond after the 1970 TAI epoch.
/// let mut timestamp = MonotonicTime::new(0, 1);
///
/// assert_eq!(timestamp, "1970-01-01 00:00:00.000000001".parse().unwrap());
/// ```
pub type MonotonicTime = TaiTime<0>;

/// A [`TaiTime`] alias using the Global Positioning System (GPS) epoch.
///
/// This timestamp is relative to 1980-01-06 00:00:00 UTC (1980-01-06 00:00:19
/// TAI).
///
/// # Examples
///
/// ```
/// use tai_time::GpsTime;
///
/// // Set the timestamp one nanosecond after the GPS epoch.
/// let mut timestamp = GpsTime::new(0, 1);
///
/// assert_eq!(timestamp, "1980-01-06 00:00:19.000000001".parse().unwrap());
/// ```
pub type GpsTime = TaiTime<315_964_819>;

/// A [`TaiTime`] alias using the Galileo System Time (GST) epoch.
///
/// This timestamp is relative to 1999-08-21 23:59:47 UTC (1999-08-22 00:00:19
/// TAI).
///
/// # Examples
///
/// ```
/// use tai_time::GstTime;
///
/// // Set the timestamp one nanosecond after the GST epoch.
/// let mut timestamp = GstTime::new(0, 1);
///
/// assert_eq!(timestamp, "1999-08-22 00:00:19.000000001".parse().unwrap());
/// ```
pub type GstTime = TaiTime<935_280_019>;

/// A [`TaiTime`] alias using the BeiDou Time (BDT) epoch.
///
/// This timestamp is relative to 2006-01-01 00:00:00 UTC (2006-01-01 00:00:33
/// TAI).
///
/// # Examples
///
/// ```
/// use tai_time::BdtTime;
///
/// // Set the timestamp one nanosecond after the BDT epoch.
/// let mut timestamp = BdtTime::new(0, 1);
///
/// assert_eq!(timestamp, "2006-01-01 00:00:33.000000001".parse().unwrap());
/// ```
pub type BdtTime = TaiTime<1_136_073_633>;

/// A [`TaiTime`] alias using an epoch set at 1958-01-01 00:00:00 TAI.
///
/// Timestamps with this epoch are in common use in TAI-based clocks. While most
/// literature sources consider that this epoch corresponds to 1958-01-01
/// 00:00:00 UTC without any leap seconds, UTC was not formally defined at that
/// date and there is no unanimous consensus on this point. Notably, the
/// `chrono::tai_clock` introduced in C++20 considers that this epoch
/// corresponds to 1957-12-31 23:59:50 UTC.
///
/// # Examples
///
/// ```
/// use tai_time::Tai1958Time;
///
/// // Set the timestamp one nanosecond after the 1958 TAI epoch.
/// let mut timestamp = Tai1958Time::new(0, 1);
///
/// assert_eq!(timestamp, "1958-01-01 00:00:00.000000001".parse().unwrap());
/// ```
pub type Tai1958Time = TaiTime<-378_691_200>;

/// A [`TaiTime`] alias using an epoch set at 1972-01-01 00:00:00 TAI.
///
/// Timestamps with this epoch are in common use in TAI-based clocks. The epoch
/// is exactly 10s in the past of 1972-01-01 00:00:00 UTC.
///
/// # Examples
///
/// ```
/// use tai_time::Tai1972Time;
///
/// // Set the timestamp one nanosecond after the 1972 TAI epoch.
/// let mut timestamp = Tai1972Time::new(0, 1);
///
/// assert_eq!(timestamp, "1972-01-01 00:00:00.000000001".parse().unwrap());
/// ```
pub type Tai1972Time = TaiTime<63_072_000>;

/// Nanosecond-precision monotonic clock timestamp parametrized by the epoch.
///
/// A timestamp specifies a [TAI] point in time. It is represented as a 64-bit
/// signed number of seconds and a positive number of nanoseconds counted with
/// reference to the epoch specified by the generic parameter.
///
/// The `EPOCH_REF` generic parameter defines the epoch via its signed distance
/// in seconds from 1970-01-01 00:00:00 TAI.
///
/// [TAI]: https://en.wikipedia.org/wiki/International_Atomic_Time
///
/// # Examples
///
/// ```
/// use std::time::Duration;
/// use tai_time::TaiTime;
///
/// // A timestamp type with an epoch at 1970:01:01 00:02:03 TAI.
/// type MyCustomTime = TaiTime<123>;
///
/// // A timestamp set to 2009-02-13 23:33:33.333333333 TAI.
/// let mut timestamp = MyCustomTime::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, MyCustomTime::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TaiTime<const EPOCH_REF: i64> {
    /// The number of whole seconds in the future (if positive) or in the past
    /// (if negative) of 1970-01-01 00:00:00 TAI.
    ///
    /// Note that the automatic derivation of `PartialOrd` relies on
    /// lexicographical comparison so the `secs` field must appear before
    /// `nanos` in declaration order to be given higher priority.
    secs: i64,
    /// The sub-second number of nanoseconds in the future of the point in time
    /// defined by `secs`.
    nanos: u32,
}

impl<const EPOCH_REF: i64> TaiTime<EPOCH_REF> {
    /// The reference epoch, which by definition is always a null timestamp.
    pub const EPOCH: Self = Self { secs: 0, nanos: 0 };

    /// The minimum possible `TaiTime` timestamp.
    pub const MIN: Self = Self {
        secs: i64::MIN,
        nanos: 0,
    };

    /// The maximum possible `TaiTime` timestamp.
    pub const MAX: Self = Self {
        secs: i64::MAX,
        nanos: NANOS_PER_SEC - 1,
    };

    /// Creates a timestamp from its parts.
    ///
    /// The number of seconds is relative to the epoch. The number of
    /// nanoseconds is always positive and always points towards the future.
    ///
    /// # Panics
    ///
    /// This constructor will panic if the number of nanoseconds is greater than
    /// or equal to 1 second.
    ///
    /// # Example
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// // A timestamp set to 2009-02-13 23:31:30.987654321 TAI.
    /// let timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
    ///
    /// // A timestamp set 0.5s in the past of the epoch.
    /// let timestamp = MonotonicTime::new(-1, 500_000_000);
    /// assert_eq!(timestamp, MonotonicTime::EPOCH - Duration::from_millis(500));
    /// ```
    pub const fn new(secs: i64, subsec_nanos: u32) -> Self {
        assert!(
            subsec_nanos < NANOS_PER_SEC,
            "invalid number of nanoseconds"
        );

        Self {
            secs,
            nanos: subsec_nanos,
        }
    }

    /// Creates a timestamp from a date-time representation.
    ///
    /// The first argument is the proleptic Gregorian year. It follows the ISO
    /// 8601 interpretation of year 0 as year 1 BC. Up to 6-digit years are
    /// supported, both positive and negative.
    ///
    /// Other arguments follow the usual calendar convention, with month and day
    /// numerals starting at 1.
    ///
    /// Note that the proleptic Gregorian calendar extrapolates dates before
    /// 1582 using the conventional leap year rules, and considers year 0 as a
    /// leap year. Proleptic Gregorian dates may therefore differ from those of
    /// the Julian calendar.
    ///
    /// Returns an error if any of the arguments is invalid, or if the calculated
    /// timestamp is outside the representable range.
    ///
    /// # Example
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// // A timestamp set to 2009-02-13 23:31:30.987654321 TAI.
    /// let timestamp = MonotonicTime::from_date_time(2009, 2, 13, 23, 31, 30, 987_654_321);
    /// assert_eq!(timestamp, Ok(MonotonicTime::new(1_234_567_890, 987_654_321)));
    /// ```
    pub const fn from_date_time(
        year: i32,
        month: u8,
        day: u8,
        hour: u8,
        min: u8,
        sec: u8,
        nano: u32,
    ) -> Result<Self, DateTimeError> {
        if month < 1 || month > 12 {
            return Err(DateTimeError::InvalidMonth(month));
        }
        if day < 1 || day > days_in_month(year, month) {
            return Err(DateTimeError::InvalidDayOfMonth(day));
        }
        if hour > 23 {
            return Err(DateTimeError::InvalidHour(hour));
        }
        if min > 59 {
            return Err(DateTimeError::InvalidMinute(min));
        }
        if sec > 59 {
            return Err(DateTimeError::InvalidSecond(sec));
        }
        if nano > NANOS_PER_SEC {
            return Err(DateTimeError::InvalidNanosecond(nano));
        }

        let days = days_from_year_0(year) - days_from_year_0(UNIX_EPOCH_YEAR)
            + day_of_year(year, month, day) as i64;

        // Note that the following cannot overflow since `days` cannot be
        // greater than approx. ±365.25*2^31.
        let secs = days * 86400 + hour as i64 * 3600 + min as i64 * 60 + sec as i64;

        if let Some(secs) = secs.checked_sub(EPOCH_REF) {
            Ok(Self { secs, nanos: nano })
        } else {
            Err(DateTimeError::OutOfRange)
        }
    }

    /// Creates a timestamp from the system clock.
    ///
    /// This is a shorthand for `from_system_time(&SystemTime::now(),
    /// leap_secs)`.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// Beware that the behavior of the system clock near a leap second
    /// shouldn't be relied upon, where *near* might actually stand for the
    /// whole 24h period preceding a leap second due to the possible use of the
    /// so-called *leap second smearing* strategy.
    ///
    /// Returns an error if the timestamp is outside the representable range,
    /// which in practice is only possible when `EPOCH_REF` is very far from 0
    /// (this will therefore never fail for `MonotonicTime`, and should not fail
    /// with the other provided `TaiTime` aliases unless the system clock is
    /// wrongly set).
    ///
    /// See also: [`from_system_time`](Self::from_system_time).
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Compute the current timestamp assuming that the current difference
    /// // between TAI and UTC time is 37s.
    /// let timestamp = MonotonicTime::now(37).unwrap();
    /// ```
    #[cfg(feature = "std")]
    pub fn now(leap_secs: i64) -> Result<Self, OutOfRangeError> {
        Self::from_system_time(&std::time::SystemTime::now(), leap_secs)
    }

    /// Creates a timestamp from the system TAI clock.
    ///
    /// This is currently only supported on Linux.
    ///
    /// Note that there are several caveats when using the Linux TAI clock. In
    /// particular:
    ///
    /// 1) on many default-configured Linux systems, the offset between TAI and
    ///    UTC is arbitrarily set to 0 at boot time, meaning that the normal UTC
    ///    system clock and the TAI system clocks will return the same value for
    ///    as long as no new leap second is introduced,
    /// 2) some systems are configured to perform *leap second smearing* by
    ///    altering the rate of the system clock over a 24h period so as to
    ///    avoid the leap second discontinuity; unfortunately, this entirely
    ///    defeats the purpose of the TAI clock by effectively synchronizing the
    ///    TAI clock with the (leap-smeared) UTC system clock.
    ///
    /// The first issue can be easily remedied, however, by installing `chrony`
    /// and, if necessary, making sure the `leapsectz` parameter in
    /// `chrony.conf` is set to `right/UTC`. Alternatively, one can specify the
    /// `leapfile` path in `ntp.conf` or set the TAI offset directly with a call
    /// to `adjtimex`/`ntp_adjtime`.
    ///
    /// Returns an error if the timestamp is outside the representable range,
    /// which in practice is only possible if `EPOCH_REF` is very far from 0
    /// _and_ the system clock is wrongly set. This will never fail for
    /// `MonotonicTime`.
    #[cfg(all(feature = "tai_clock", target_os = "linux"))]
    pub fn now_from_tai_clock() -> Result<Self, OutOfRangeError> {
        use core::mem::MaybeUninit;

        let mut c_time: MaybeUninit<libc::timespec> = MaybeUninit::uninit();
        let ret = unsafe { libc::clock_gettime(libc::CLOCK_TAI, c_time.as_mut_ptr()) };

        assert_eq!(ret, 0);

        let res = unsafe { c_time.assume_init() };

        #[allow(clippy::useless_conversion)]
        let secs: i64 = res.tv_sec.try_into().unwrap();
        #[allow(clippy::useless_conversion)]
        let subsec_nanos: u32 = res.tv_nsec.try_into().unwrap();

        // The timestamp _should_ have the same epoch as `MonotonicTime`, i.e.
        // 1970-01-01 00:00:00 TAI.
        let t = MonotonicTime::new(secs, subsec_nanos);

        t.to_tai_time()
    }

    /// Creates a TAI timestamp from a Unix timestamp.
    ///
    /// The last argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// Note that there is no unanimous consensus regarding the conversion
    /// between TAI and Unix timestamps prior to 1972.
    ///
    /// Returns an error if the timestamp is outside the representable range or
    /// if the number of nanoseconds is greater than or equal to 1 second.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Creates a timestamp corresponding to 2001-09-15 05:05:00.005 UTC,
    /// // accounting for the +32s difference between UAI and UTC on 2001-09-15.
    /// assert_eq!(
    ///     MonotonicTime::from_unix_timestamp(1_000_530_300, 5_000_000, 32),
    ///     Ok(MonotonicTime::new(1_000_530_332, 5_000_000))
    /// );
    /// ```
    pub const fn from_unix_timestamp(
        secs: i64,
        subsec_nanos: u32,
        leap_secs: i64,
    ) -> Result<Self, OutOfRangeError> {
        if let Some(secs) = secs.checked_add(leap_secs) {
            if let Some(secs) = secs.checked_sub(EPOCH_REF) {
                if subsec_nanos < NANOS_PER_SEC {
                    return Ok(Self {
                        secs,
                        nanos: subsec_nanos,
                    });
                }
            }
        }

        Err(OutOfRangeError(()))
    }

    /// Creates a TAI timestamp from a `SystemTime` timestamp.
    ///
    /// The last argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// Returns an error if the timestamp is outside the representable range.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::{Duration, SystemTime};
    /// use tai_time::MonotonicTime;
    ///
    /// // Creates a timestamp corresponding to 2001-09-15 05:05:00.005 UTC,
    /// // accounting for the +32s difference between UAI and UTC on 2001-09-15.
    /// let system_time = SystemTime::UNIX_EPOCH + Duration::new(1_000_530_300, 5_000_000);
    /// assert_eq!(
    ///     MonotonicTime::from_system_time(&system_time, 32),
    ///     Ok(MonotonicTime::new(1_000_530_332, 5_000_000))
    /// );
    /// ```
    #[cfg(feature = "std")]
    pub fn from_system_time(
        system_time: &std::time::SystemTime,
        leap_secs: i64,
    ) -> Result<Self, OutOfRangeError> {
        let unix_time = system_time
            .duration_since(std::time::SystemTime::UNIX_EPOCH)
            .map_err(|_| OutOfRangeError(()))?;

        // Account for the offset between PTP and Unix time as well as for the
        // offset between the PTP epoch and the actual epoch of this `TaiTime`.
        leap_secs
            .checked_sub(EPOCH_REF)
            .map(|delta| Self::new(delta, 0))
            .and_then(|timestamp| timestamp.checked_add(unix_time))
            .ok_or(OutOfRangeError(()))
    }

    /// Creates a timestamp from a `chrono::DateTime`.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// While no error will be reported, this method should not be considered
    /// appropriate for timestamps in the past of 1972.
    ///
    /// Returns an error if the timestamp is outside the representable range.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    /// use chrono::DateTime;
    ///
    /// let date_time = DateTime::parse_from_rfc3339("2001-09-15T05:05:00.005Z").unwrap();
    /// assert_eq!(
    ///     MonotonicTime::from_chrono_date_time(&date_time, 32),
    ///     Ok(MonotonicTime::new(1_000_530_332, 5_000_000))
    /// );
    /// ```
    #[cfg(feature = "chrono")]
    pub const fn from_chrono_date_time<Tz: chrono::TimeZone>(
        date_time: &chrono::DateTime<Tz>,
        leap_secs: i64,
    ) -> Result<Self, OutOfRangeError> {
        let secs = date_time.timestamp();
        let subsec_nanos = date_time.timestamp_subsec_nanos();

        // The `chrono` crate adds leap seconds to the nanoseconds part, so move
        // any potential leap seconds to the `secs` if necessary.
        let (secs_carry, subsec_nanos) = if subsec_nanos < NANOS_PER_SEC {
            (0, subsec_nanos)
        } else {
            (1, subsec_nanos - NANOS_PER_SEC)
        };

        if let Some(secs) = secs.checked_add(secs_carry) {
            return Self::from_unix_timestamp(secs, subsec_nanos, leap_secs);
        }

        Err(OutOfRangeError(()))
    }

    /// Returns the signed value of the second that is equal or lower than the
    /// timestamp, relative to the [`EPOCH`](TaiTime::EPOCH).
    ///
    /// This value is the same as the one that would be provided when
    /// constructing the timestamp with [`new()`](TaiTime::new).
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// let timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
    /// assert_eq!(timestamp.as_secs(), 1_234_567_890);
    ///
    /// let timestamp = MonotonicTime::EPOCH - Duration::new(3, 500_000_000);
    /// assert_eq!(timestamp.as_secs(), -4);
    /// ```
    pub const fn as_secs(&self) -> i64 {
        self.secs
    }

    /// Returns the sub-second fractional part in nanoseconds.
    ///
    /// Note that nanoseconds always point towards the future even if the date
    /// is in the past of the [`EPOCH`](TaiTime::EPOCH).
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// let timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
    /// assert_eq!(timestamp.subsec_nanos(), 987_654_321);
    /// ```
    pub const fn subsec_nanos(&self) -> u32 {
        self.nanos
    }

    /// Returns the number of seconds of the corresponding Unix timestamp.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// This method merely subtracts the offset from the value returned by
    /// [`as_secs()`](Self::as_secs) and checks for potential overflow; its main
    /// purpose is to prevent mistakes regarding the direction in which the
    /// offset should be applied.
    ///
    /// The nanosecond part of a Unix timestamp can be simply retrieved with
    /// [`subsec_nanos()`](Self::subsec_nanos) since UTC and TAI differ by a
    /// whole number of seconds since 1972.
    ///
    /// Note that there is no unanimous consensus regarding the conversion
    /// between TAI and Unix timestamps prior to 1972.
    ///
    /// Returns an error if the offset-adjusted timestamp is outside the
    /// representable range.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Set the date to 2000-01-01 00:00:00 TAI.
    /// let timestamp = MonotonicTime::new(946_684_800, 0);
    ///
    /// // Convert to a Unix timestamp, accounting for the +32s difference between
    /// // TAI and UTC on 2000-01-01.
    /// assert_eq!(
    ///     timestamp.to_unix_secs(32),
    ///     Ok(946_684_768)
    /// );
    /// ```
    pub const fn to_unix_secs(&self, leap_secs: i64) -> Result<i64, OutOfRangeError> {
        if let Some(secs) = self.secs.checked_sub(leap_secs) {
            if let Some(secs) = secs.checked_add(EPOCH_REF) {
                return Ok(secs);
            }
        }

        Err(OutOfRangeError(()))
    }

    /// Returns a timestamp with a different reference epoch.
    ///
    /// Returns an error if the new timestamp is outside the representable
    /// range.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use tai_time::{GpsTime, MonotonicTime};
    ///
    /// // Set the date to 2000-01-01 00:00:00 TAI.
    /// let timestamp = MonotonicTime::new(946_684_800, 0);
    ///
    /// // Convert to a GPS timestamp.
    /// let gps_timestamp: GpsTime = timestamp.to_tai_time().unwrap();
    /// assert_eq!(
    ///     gps_timestamp,
    ///     GpsTime::new(630_719_981, 0)
    /// );
    /// ```
    pub const fn to_tai_time<const OTHER_EPOCH_REF: i64>(
        &self,
    ) -> Result<TaiTime<OTHER_EPOCH_REF>, OutOfRangeError> {
        if let Some(epoch_diff) = EPOCH_REF.checked_sub(OTHER_EPOCH_REF) {
            if let Some(secs) = self.secs.checked_add(epoch_diff) {
                return Ok(TaiTime {
                    secs,
                    nanos: self.nanos,
                });
            }
        }

        Err(OutOfRangeError(()))
    }

    /// Returns a `SystemTime` based on the timestamp.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// While no error will be reported, this method should not be considered
    /// appropriate for timestamps in the past of 1972.
    ///
    /// Returns an error if the offset-adjusted timestamp is outside the
    /// representable range, and in particular if the timestamp predates the
    /// Unix epoch (1970-01-01 00:00:00 UTC).
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::{Duration, SystemTime};
    /// use tai_time::MonotonicTime;
    ///
    /// // Set the date to 2000-01-01 00:00:00.123 TAI.
    /// let timestamp = MonotonicTime::new(946_684_800, 123_000_000);
    ///
    /// // Obtain a `chrono::DateTime`, accounting for the +32s difference between
    /// // TAI and UTC on 2000-01-01.
    /// assert_eq!(
    ///     timestamp.to_system_time(32),
    ///     Ok(SystemTime::UNIX_EPOCH + Duration::new(946_684_768, 123_000_000))
    /// );
    /// ```
    #[cfg(feature = "std")]
    pub fn to_system_time(&self, leap_secs: i64) -> Result<std::time::SystemTime, OutOfRangeError> {
        let secs: u64 = self
            .to_unix_secs(leap_secs)
            .and_then(|secs| secs.try_into().map_err(|_| OutOfRangeError(())))?;

        std::time::SystemTime::UNIX_EPOCH
            .checked_add(Duration::new(secs, self.subsec_nanos()))
            .ok_or(OutOfRangeError(()))
    }

    /// Returns a `chrono::DateTime` based on the timestamp.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-28. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// While no error will be reported, this method should not be considered
    /// appropriate for timestamps in the past of 1972.
    ///
    /// Returns an error if the offset-adjusted timestamp is outside the
    /// representable range.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Set the date to 2000-01-01 00:00:00.123 TAI (1999-12-31 23:59:28.123 UTC).
    /// let timestamp = MonotonicTime::new(946_684_800, 123_000_000);
    ///
    /// // Obtain a `chrono::DateTime`, accounting for the +32s difference between
    /// // TAI and UTC on 2000-01-01.
    /// let date_time = timestamp.to_chrono_date_time(32).unwrap();
    /// assert_eq!(
    ///     date_time.to_string(),
    ///     "1999-12-31 23:59:28.123 UTC"
    /// );
    /// ```
    #[cfg(feature = "chrono")]
    pub fn to_chrono_date_time(
        &self,
        leap_secs: i64,
    ) -> Result<chrono::DateTime<chrono::Utc>, OutOfRangeError> {
        self.to_unix_secs(leap_secs).and_then(|secs| {
            chrono::DateTime::from_timestamp(secs, self.nanos).ok_or(OutOfRangeError(()))
        })
    }

    /// Adds a duration to a timestamp, checking for overflow.
    ///
    /// Returns `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// let timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
    /// assert!(timestamp.checked_add(Duration::new(10, 123_456_789)).is_some());
    /// assert!(timestamp.checked_add(Duration::MAX).is_none());
    /// ```
    pub const fn checked_add(self, rhs: Duration) -> Option<Self> {
        // A durations in seconds greater than `i64::MAX` is actually fine as
        // long as the number of seconds does not effectively overflow which is
        // why the below does not use `checked_add`. So technically the below
        // addition may wrap around on the negative side due to the
        // unsigned-to-signed cast of the duration, but this does not
        // necessarily indicate an actual overflow. Actual overflow can be ruled
        // out by verifying that the new timestamp is in the future of the old
        // timestamp.
        let mut secs = self.secs.wrapping_add(rhs.as_secs() as i64);

        // Check for overflow.
        if secs < self.secs {
            return None;
        }

        let mut nanos = self.nanos + rhs.subsec_nanos();
        if nanos >= NANOS_PER_SEC {
            secs = if let Some(s) = secs.checked_add(1) {
                s
            } else {
                return None;
            };
            nanos -= NANOS_PER_SEC;
        }

        Some(Self { secs, nanos })
    }

    /// Subtracts a duration from a timestamp, checking for overflow.
    ///
    /// Returns `None` if overflow occurred.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// let timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
    /// assert!(timestamp.checked_sub(Duration::new(10, 123_456_789)).is_some());
    /// assert!(timestamp.checked_sub(Duration::MAX).is_none());
    /// ```
    pub const fn checked_sub(self, rhs: Duration) -> Option<Self> {
        // A durations in seconds greater than `i64::MAX` is actually fine as
        // long as the number of seconds does not effectively overflow, which is
        // why the below does not use `checked_sub`. So technically the below
        // subtraction may wrap around on the positive side due to the
        // unsigned-to-signed cast of the duration, but this does not
        // necessarily indicate an actual overflow. Actual overflow can be ruled
        // out by verifying that the new timestamp is in the past of the old
        // timestamp.
        let mut secs = self.secs.wrapping_sub(rhs.as_secs() as i64);

        // Check for overflow.
        if secs > self.secs {
            return None;
        }

        let nanos = if self.nanos < rhs.subsec_nanos() {
            secs = if let Some(s) = secs.checked_sub(1) {
                s
            } else {
                return None;
            };

            (self.nanos + NANOS_PER_SEC) - rhs.subsec_nanos()
        } else {
            self.nanos - rhs.subsec_nanos()
        };

        Some(Self { secs, nanos })
    }

    /// Subtracts a timestamp from another timestamp.
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// # Panics
    ///
    /// Panics if the argument lies in the future of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// let timestamp_earlier = MonotonicTime::new(1_234_567_879, 987_654_321);
    /// let timestamp_later = MonotonicTime::new(1_234_567_900, 123_456_789);
    /// assert_eq!(
    ///     timestamp_later.duration_since(timestamp_earlier),
    ///     Duration::new(20, 135_802_468)
    /// );
    /// ```
    pub const fn duration_since(self, earlier: Self) -> Duration {
        if let Some(duration) = self.checked_duration_since(earlier) {
            return duration;
        }

        panic!("attempt to substract a timestamp from an earlier timestamp");
    }

    /// Computes the duration elapsed between a timestamp and an earlier
    /// timestamp, checking that the timestamps are appropriately ordered.
    ///
    /// Returns `None` if the argument lies in the future of `self`.
    ///
    /// # Examples
    ///
    /// (Shown here for `MonotonicTime`, an alias for `TaiTime<0>`)
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::MonotonicTime;
    ///
    /// let timestamp_earlier = MonotonicTime::new(1_234_567_879, 987_654_321);
    /// let timestamp_later = MonotonicTime::new(1_234_567_900, 123_456_789);
    /// assert!(timestamp_later.checked_duration_since(timestamp_earlier).is_some());
    /// assert!(timestamp_earlier.checked_duration_since(timestamp_later).is_none());
    /// ```
    pub const fn checked_duration_since(self, earlier: Self) -> Option<Duration> {
        // If the subtraction of the nanosecond fractions would overflow, carry
        // over one second to the nanoseconds.
        let (secs, nanos) = if earlier.nanos > self.nanos {
            if let Some(s) = self.secs.checked_sub(1) {
                (s, self.nanos + NANOS_PER_SEC)
            } else {
                return None;
            }
        } else {
            (self.secs, self.nanos)
        };

        // Make sure the computation of the duration will not overflow the
        // seconds.
        if secs < earlier.secs {
            return None;
        }

        // This subtraction may wrap around if the difference between the two
        // timestamps is more than `i64::MAX`, but even if it does the result
        // will be correct once cast to an unsigned integer.
        let delta_secs = secs.wrapping_sub(earlier.secs) as u64;

        // The below subtraction is guaranteed to never overflow.
        let delta_nanos = nanos - earlier.nanos;

        Some(Duration::new(delta_secs, delta_nanos))
    }
}

impl<const EPOCH_REF: i64> Add<Duration> for TaiTime<EPOCH_REF> {
    type Output = Self;

    /// Adds a duration to a timestamp.
    ///
    /// # Panics
    ///
    /// This function panics if the resulting timestamp cannot be
    /// represented. See [`TaiTime::checked_add`] for a panic-free
    /// version.
    fn add(self, other: Duration) -> Self {
        self.checked_add(other)
            .expect("overflow when adding duration to timestamp")
    }
}

impl<const EPOCH_REF: i64> Sub<Duration> for TaiTime<EPOCH_REF> {
    type Output = Self;

    /// Subtracts a duration from a timestamp.
    ///
    /// # Panics
    ///
    /// This function panics if the resulting timestamp cannot be
    /// represented. See [`TaiTime::checked_sub`] for a panic-free
    /// version.
    fn sub(self, other: Duration) -> Self {
        self.checked_sub(other)
            .expect("overflow when subtracting duration from timestamp")
    }
}

impl<const EPOCH_REF: i64> AddAssign<Duration> for TaiTime<EPOCH_REF> {
    /// Increments the timestamp by a duration.
    ///
    /// # Panics
    ///
    /// This function panics if the resulting timestamp cannot be represented.
    fn add_assign(&mut self, other: Duration) {
        *self = *self + other;
    }
}

impl<const EPOCH_REF: i64> SubAssign<Duration> for TaiTime<EPOCH_REF> {
    /// Decrements the timestamp by a duration.
    ///
    /// # Panics
    ///
    /// This function panics if the resulting timestamp cannot be represented.
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl<const EPOCH_REF: i64> FromStr for TaiTime<EPOCH_REF> {
    type Err = ParseDateTimeError;

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
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (year, month, day, hour, min, sec, nano) = parse_date_time(s)?;

        Self::from_date_time(year, month, day, hour, min, sec, nano)
            .map_err(ParseDateTimeError::RangeError)
    }
}

impl<const EPOCH_REF: i64> fmt::Display for TaiTime<EPOCH_REF> {
    /// Displays the TAI timestamp as an RFC3339-like date-time.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We need to use an i128 timestamp as it may otherwise overflow when
        // translated to year 0.
        let secs_from_year_0: i128 =
            self.secs as i128 + EPOCH_REF as i128 + days_from_year_0(1970) as i128 * 86400;
        let (year, doy, mut sec) = secs_to_date_time(secs_from_year_0);
        let (month, day) = month_and_day_of_month(year, doy);
        let hour = sec / 3600;
        sec -= hour * 3600;
        let min = sec / 60;
        sec -= min * 60;

        write!(
            f,
            "{}{:04}-{:02}-{:02} {:02}:{:02}:{:02}",
            if year < 0 { "-" } else { "" },
            year.abs(),
            month,
            day,
            hour,
            min,
            sec
        )?;

        if self.nanos != 0 {
            write!(f, ".{:09}", self.nanos)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equality() {
        let t0 = Tai1972Time::new(123, 123_456_789);
        let t1 = Tai1972Time::new(123, 123_456_789);
        let t2 = Tai1972Time::new(123, 123_456_790);
        let t3 = Tai1972Time::new(124, 123_456_789);

        assert_eq!(t0, t1);
        assert_ne!(t0, t2);
        assert_ne!(t0, t3);
    }

    #[test]
    fn ordering() {
        let t0 = Tai1972Time::new(0, 1);
        let t1 = Tai1972Time::new(1, 0);

        assert!(t1 > t0);
    }

    #[test]
    fn epoch_smoke() {
        // Set all timestamps to 2009-02-13 23:31:30.123456789 UTC.
        const T_UNIX_SECS: i64 = 1_234_567_890;
        const T_TAI_1970: MonotonicTime = MonotonicTime::new(1_234_567_924, 123_456_789);
        const T_TAI_1958: Tai1958Time = Tai1958Time::new(1_613_259_124, 123_456_789);
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(1_171_495_924, 123_456_789);
        const T_GPS: GpsTime = GpsTime::new(918_603_105, 123_456_789);
        const T_GST: GstTime = GstTime::new(299_287_905, 123_456_789);
        const T_BDT: BdtTime = BdtTime::new(98_494_291, 123_456_789);

        // Leap seconds can be neglected for this test.
        assert_eq!(T_TAI_1970.to_unix_secs(34).unwrap(), T_UNIX_SECS);
        assert_eq!(T_TAI_1958.to_unix_secs(34).unwrap(), T_UNIX_SECS);
        assert_eq!(T_TAI_1972.to_unix_secs(34).unwrap(), T_UNIX_SECS);
        assert_eq!(T_GPS.to_unix_secs(34).unwrap(), T_UNIX_SECS);
        assert_eq!(T_GST.to_unix_secs(34).unwrap(), T_UNIX_SECS);
        assert_eq!(T_BDT.to_unix_secs(34).unwrap(), T_UNIX_SECS);

        assert_eq!(T_TAI_1970.to_tai_time().unwrap(), T_TAI_1958);
        assert_eq!(T_TAI_1970.to_tai_time().unwrap(), T_TAI_1970);
        assert_eq!(T_TAI_1970.to_tai_time().unwrap(), T_TAI_1972);
        assert_eq!(T_TAI_1970.to_tai_time().unwrap(), T_GPS);
        assert_eq!(T_TAI_1970.to_tai_time().unwrap(), T_GST);
        assert_eq!(T_TAI_1970.to_tai_time().unwrap(), T_BDT);
    }

    #[cfg(feature = "std")]
    #[test]
    fn now_smoke() {
        const TAI_1972_START_OF_2022: i64 = 1_577_923_200;
        const TAI_1972_START_OF_2050: i64 = 2_461_536_000;

        // Leap seconds can be neglected for this test.
        let now_secs = Tai1972Time::now(0).unwrap().as_secs();

        assert!(now_secs > TAI_1972_START_OF_2022);
        assert!(now_secs < TAI_1972_START_OF_2050);
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_system_time() {
        // Unix and TAI 1972 time stamps for 2001:01:01 12:34:56.789 UTC.
        const T_UNIX: Duration = Duration::new(978_352_496, 789_000_000);
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(915_280_528, 789_000_000);

        let system_time = std::time::SystemTime::UNIX_EPOCH + T_UNIX;
        // Account for the +32 leap seconds on that date.
        let tai1792_time = Tai1972Time::from_system_time(&system_time, 32).unwrap();

        assert_eq!(tai1792_time, T_TAI_1972);
    }

    #[test]
    fn from_unix_timestamp() {
        // Unix and TAI 1972 time stamps for 2001:01:01 12:34:56.789 UTC.
        const T_UNIX_SECS: i64 = 978_352_496;
        const T_UNIX_NANOS: u32 = 789_000_000;
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(915_280_528, 789_000_000);

        // Account for the +32 leap seconds on that date.
        let tai1792_time = Tai1972Time::from_unix_timestamp(T_UNIX_SECS, T_UNIX_NANOS, 32).unwrap();

        assert_eq!(tai1792_time, T_TAI_1972);
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn from_chrono_date_time() {
        // TAI 1972 time stamp for 2001:01:01 12:34:56.789 UTC.
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(915_280_528, 789_000_000);

        let chrono_date_time =
            chrono::DateTime::parse_from_rfc3339("2001-01-01T12:34:56.789Z").unwrap();
        // Account for the +32 leap seconds on that date.
        let tai1792_time = Tai1972Time::from_chrono_date_time(&chrono_date_time, 32).unwrap();

        assert_eq!(tai1792_time, T_TAI_1972);
    }

    #[test]
    fn as_secs_and_nanos() {
        // TAI 1972 time stamp for 1999:01:01 01:23:45.678 UTC.
        const T_TAI_1972_SECS: i64 = 852_081_857;
        const T_TAI_1972_NANOS: u32 = 678_000_000;
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(T_TAI_1972_SECS, T_TAI_1972_NANOS);

        assert_eq!(T_TAI_1972.as_secs(), T_TAI_1972_SECS);
        assert_eq!(T_TAI_1972.subsec_nanos(), T_TAI_1972_NANOS);
    }

    #[test]
    fn to_unix_secs() {
        // Unix and TAI 1972 time stamp for 1999:01:01 01:23:45.678 UTC.
        const T_UNIX_SECS: i64 = 915_153_825;
        const T_TAI_1972_SECS: i64 = 852_081_857;
        const T_TAI_1972_NANOS: u32 = 678_000_000;
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(T_TAI_1972_SECS, T_TAI_1972_NANOS);

        assert_eq!(T_TAI_1972.to_unix_secs(32).unwrap(), T_UNIX_SECS);
    }

    #[test]
    fn to_tai_time() {
        // GPS and TAI 1972 time stamps for 1999:01:01 01:23:45.678 UTC.
        const T_GPS: GpsTime = GpsTime::new(599_189_038, 678_000_000);
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(852_081_857, 678_000_000);

        let tai1792_time: Tai1972Time = T_GPS.to_tai_time().unwrap();

        assert_eq!(tai1792_time, T_TAI_1972);
    }

    #[cfg(feature = "std")]
    #[test]
    fn to_system_time() {
        // Unix and TAI 1972 time stamp for 1999:01:01 01:23:45.678 UTC.
        const T_UNIX: Duration = Duration::new(915_153_825, 678_000_000);
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(852_081_857, 678_000_000);

        assert_eq!(
            T_TAI_1972.to_system_time(32).unwrap(),
            std::time::SystemTime::UNIX_EPOCH + T_UNIX
        );
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn to_chrono_date_time() {
        // TAI 1972 time stamp for 1999:01:01 01:23:45.678 UTC.
        const T_TAI_1972: Tai1972Time = Tai1972Time::new(852_081_857, 678_000_000);

        assert_eq!(
            T_TAI_1972.to_chrono_date_time(32).unwrap(),
            chrono::DateTime::parse_from_rfc3339("1999-01-01T01:23:45.678Z").unwrap()
        );
    }

    #[test]
    #[should_panic]
    fn invalid_nanoseconds() {
        Tai1958Time::new(123, 1_000_000_000);
    }

    #[test]
    fn duration_since_smoke() {
        let t0 = Tai1972Time::new(100, 100_000_000);
        let t1 = Tai1972Time::new(123, 223_456_789);

        assert_eq!(
            t1.checked_duration_since(t0),
            Some(Duration::new(23, 123_456_789))
        );
    }

    #[test]
    fn duration_with_carry() {
        let t0 = Tai1972Time::new(100, 200_000_000);
        let t1 = Tai1972Time::new(101, 100_000_000);

        assert_eq!(
            t1.checked_duration_since(t0),
            Some(Duration::new(0, 900_000_000))
        );
    }

    #[test]
    fn duration_since_extreme() {
        const MIN_TIME: Tai1972Time = TaiTime::MIN;
        const MAX_TIME: Tai1972Time = TaiTime::MAX;

        assert_eq!(
            MAX_TIME.checked_duration_since(MIN_TIME),
            Some(Duration::new(u64::MAX, NANOS_PER_SEC - 1))
        );
    }

    #[test]
    fn duration_since_invalid() {
        let t0 = Tai1972Time::new(100, 0);
        let t1 = Tai1972Time::new(99, 0);

        assert_eq!(t1.checked_duration_since(t0), None);
    }

    #[test]
    fn add_duration_smoke() {
        let t = Tai1972Time::new(-100, 100_000_000);
        let dt = Duration::new(400, 300_000_000);

        assert_eq!(t + dt, Tai1972Time::new(300, 400_000_000));
    }

    #[test]
    fn add_duration_with_carry() {
        let t = Tai1972Time::new(-100, 900_000_000);
        let dt1 = Duration::new(400, 100_000_000);
        let dt2 = Duration::new(400, 300_000_000);

        assert_eq!(t + dt1, Tai1972Time::new(301, 0));
        assert_eq!(t + dt2, Tai1972Time::new(301, 200_000_000));
    }

    #[test]
    fn add_duration_extreme() {
        let t = Tai1972Time::new(i64::MIN, 0);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        assert_eq!(t + dt, Tai1972Time::new(i64::MAX, NANOS_PER_SEC - 1));
    }

    #[test]
    #[should_panic]
    fn add_duration_overflow() {
        let t = Tai1972Time::new(i64::MIN, 1);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        let _ = t + dt;
    }

    #[test]
    fn sub_duration_smoke() {
        let t = Tai1972Time::new(100, 500_000_000);
        let dt = Duration::new(400, 300_000_000);

        assert_eq!(t - dt, Tai1972Time::new(-300, 200_000_000));
    }

    #[test]
    fn sub_duration_with_carry() {
        let t = Tai1972Time::new(100, 100_000_000);
        let dt1 = Duration::new(400, 100_000_000);
        let dt2 = Duration::new(400, 300_000_000);

        assert_eq!(t - dt1, Tai1972Time::new(-300, 0));
        assert_eq!(t - dt2, Tai1972Time::new(-301, 800_000_000));
    }

    #[test]
    fn sub_duration_extreme() {
        let t = Tai1972Time::new(i64::MAX, NANOS_PER_SEC - 1);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        assert_eq!(t - dt, Tai1972Time::new(i64::MIN, 0));
    }

    #[test]
    #[should_panic]
    fn sub_duration_overflow() {
        let t = Tai1972Time::new(i64::MAX, NANOS_PER_SEC - 2);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        let _ = t - dt;
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn date_time_year_count() {
        // This test relies on `chrono` as the source of truth.
        use chrono::NaiveDate;

        // Check enough years to cover several 400-year, 100-year, 4-year and
        // 1-year boundaries, with both negative and positive dates. Check as
        // well the most extreme dates supported by `chrono`.
        const TEST_MIN_YEAR: i32 = -801;
        const TEST_MAX_YEAR: i32 = 801;
        const CHRONO_MIN_YEAR: i32 = -0x3ffff;
        const CHRONO_MAX_YEAR: i32 = 0x3fffe;

        // The test abuses `chrono` by using TAI date-time stamps, pretending
        // they are UTC. This works because `chrono` ignores leap seconds in
        // arithmetic operations.
        let gps_chrono_epoch = NaiveDate::from_ymd_opt(1980, 1, 6)
            .unwrap()
            .and_hms_opt(0, 0, 19)
            .unwrap();

        for year in (-TEST_MIN_YEAR..=TEST_MAX_YEAR).chain([CHRONO_MIN_YEAR, CHRONO_MAX_YEAR]) {
            // Test the beginning of the year.
            let chrono_date_time = NaiveDate::from_ymd_opt(year, 1, 1)
                .unwrap()
                .and_hms_opt(0, 0, 0)
                .unwrap();
            let chrono_gps_timestamp = (chrono_date_time - gps_chrono_epoch).num_seconds();
            let tai_gps_timestamp = GpsTime::from_date_time(year, 1, 1, 0, 0, 0, 0)
                .unwrap()
                .as_secs();
            assert_eq!(tai_gps_timestamp, chrono_gps_timestamp);

            // Test the last second of the year.
            let chrono_date_time = NaiveDate::from_ymd_opt(year, 12, 31)
                .unwrap()
                .and_hms_opt(23, 59, 59)
                .unwrap();
            let chrono_gps_timestamp = (chrono_date_time - gps_chrono_epoch).num_seconds();
            let tai_gps_timestamp = GpsTime::from_date_time(year, 12, 31, 23, 59, 59, 0)
                .unwrap()
                .as_secs();
            assert_eq!(tai_gps_timestamp, chrono_gps_timestamp);
        }
    }

    #[cfg(feature = "chrono")]
    #[test]
    fn date_time_day_count() {
        // This test relies on `chrono` as the source of truth.
        use chrono::{Datelike, NaiveDate};

        // Test arbitrary leap and non-leap years, negative and positive.
        const TEST_YEARS: [i32; 6] = [-3000, -500, -1, 600, 723, 2400];

        // The test abuses `chrono` by using TAI date-time stamps, pretending
        // they are UTC. This works because `chrono` ignores leap seconds in
        // arithmetic operations.
        let bdt_chrono_epoch = NaiveDate::from_ymd_opt(2006, 1, 1)
            .unwrap()
            .and_hms_opt(0, 0, 33)
            .unwrap();

        for year in TEST_YEARS {
            let mut chrono_date_time = NaiveDate::from_ymd_opt(year, 1, 1)
                .unwrap()
                .and_hms_opt(0, 0, 0)
                .unwrap();

            while chrono_date_time.year() == year {
                // Test the beginning of the day.
                let chrono_bdt_timestamp = (chrono_date_time - bdt_chrono_epoch).num_seconds();
                let tai_bdt_timestamp = BdtTime::from_date_time(
                    year,
                    chrono_date_time.month() as u8,
                    chrono_date_time.day() as u8,
                    0,
                    0,
                    0,
                    0,
                )
                .unwrap()
                .as_secs();
                assert_eq!(tai_bdt_timestamp, chrono_bdt_timestamp);

                // Test the last second of the day.
                chrono_date_time += Duration::from_secs(86399);
                let chrono_bdt_timestamp = (chrono_date_time - bdt_chrono_epoch).num_seconds();
                let tai_bdt_timestamp = BdtTime::from_date_time(
                    year,
                    chrono_date_time.month() as u8,
                    chrono_date_time.day() as u8,
                    23,
                    59,
                    59,
                    0,
                )
                .unwrap()
                .as_secs();
                assert_eq!(tai_bdt_timestamp, chrono_bdt_timestamp);

                chrono_date_time += Duration::from_secs(1);
            }
        }
    }

    #[test]
    fn date_time_second_count() {
        // Pick an arbitrary day.
        const TEST_DAY: u8 = 12;
        const TEST_MONTH: u8 = 3;
        const TEST_YEAR: i32 = -4567;

        let mut timestamp =
            Tai1958Time::from_date_time(TEST_YEAR, TEST_MONTH, TEST_DAY, 0, 0, 0, 0)
                .unwrap()
                .as_secs();

        for hour in 0..=23 {
            for min in 0..=59 {
                for sec in 0..=59 {
                    let t = Tai1958Time::from_date_time(
                        TEST_YEAR, TEST_MONTH, TEST_DAY, hour, min, sec, 0,
                    )
                    .unwrap();
                    assert_eq!(t.as_secs(), timestamp);
                    timestamp += 1;
                }
            }
        }
    }

    #[test]
    fn date_time_string_roundtrip() {
        const TEST_DATES: &[(&str, (i32, u8, u8, u8, u8, u8, u32))] = &[
            (
                "-2147483647-01-01 00:00:00",
                (-2147483647, 1, 1, 0, 0, 0, 0),
            ),
            ("-0000-01-01T00:00:00", (0, 1, 1, 0, 0, 0, 0)),
            (
                "2000-02-29T12:23:45.000000001",
                (2000, 2, 29, 12, 23, 45, 1),
            ),
            (
                "+2345-10-11 12:13:14.123",
                (2345, 10, 11, 12, 13, 14, 123_000_000),
            ),
            (
                "2147483647-12-31 23:59:59.999999999",
                (2147483647, 12, 31, 23, 59, 59, 999_999_999),
            ),
        ];

        for (date_time_str, date_time) in TEST_DATES {
            let (year, month, day, hour, min, sec, nano) = *date_time;

            let t0: GstTime = date_time_str.parse().unwrap();
            let t1: GpsTime = t0.to_string().parse().unwrap();
            assert_eq!(
                t1,
                GpsTime::from_date_time(year, month, day, hour, min, sec, nano).unwrap()
            );
        }
    }

    #[test]
    fn date_time_invalid() {
        const TEST_DATES: &[&str] = &[
            "123-01-01 00:00:00",
            "-1500-02-29 00:00:00",
            "2001-06-31 00:00:00",
            "1234-01-00 00:00:00",
            "1234-00-01 00:00:00",
            "1234-13-01 00:00:00",
            "5678-09-10 24:00:00",
            "5678-09-10 00:60:00",
            "5678-09-10 00:00:60",
        ];

        for date_time_str in TEST_DATES {
            assert!(date_time_str.parse::<MonotonicTime>().is_err());
        }
    }
}
