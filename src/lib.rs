//! A nanosecond-precision monotonic clock timestamp based on the TAI time
//! standard.
//!
//! # Overview
//!
//! While Rust's standard library already provides the
//! [`Instant`](std::time::Instant) monotonic timestamp, its absolute value is
//! opaque. In many scientific and engineering applications such as simulations
//! and synchronized systems, monotonic timestamps based on absolute time
//! references are required.
//!
//! This crate provides a fairly unopinionated timestamp for such applications
//! with a focus on simplicity, adherence to Rust's `std::time` idioms and
//! interoperability with the [`Duration`] type.
//!
//! A [TaiTime] timestamp specifies a [TAI] point in time. It is represented as
//! a 64-bit signed number of seconds and a positive number of nanoseconds,
//! relative to 1970-01-01 00:00:00 TAI or to any arbitrary epoch. This
//! timestamp format has a number of desirable properties:
//!
//! - it is computationally efficient for arithmetic operations involving the
//!   standard [`Duration`] type, which uses a very similar internal
//!   representation,
//! - with a 1970 epoch (see [`MonotonicTime`]), exact conversion to a Unix
//!   timestamp is trivial and only requires subtracting from this timestamp the
//!   number of leap seconds between TAI and UTC time,
//! - with a 1970 epoch, it constitutes a strict 96-bit superset of 80-bit PTP
//!   IEEE-1588 timestamps, a widely used standard for high-precision time
//!   distribution,
//! - with a 1970 epoch, it is substantially similar (though not strictly
//!   identical) to the [TAI64N] time format,
//! - with a custom epoch, it can represent other monotonic clocks such as the
//!   Global Position System and the Galileo System Time clocks (see e.g.
//!   [`GpsTime`], [`GstTime`], [`Tai1958Time`] and [`Tai1972Time`]).
//!
//! [`MonotonicTime`], an alias for [`TaiTime`] with an epoch set at 1970-01-01
//! 00:00:00 TAI, is the recommended timestamp choice when no specific epoch is
//! mandated.
//!
//! [TAI]: https://en.wikipedia.org/wiki/International_Atomic_Time
//! [TAI64N]: https://cr.yp.to/libtai/tai64.html
//!
//!
//! # (Intentional) limitations
//!
//! No date-time parsing and formatting facilities are provided, but these can
//! be performed using other crates such as [chrono] (see [features
//! flags](#other-time-related-crates)).
//!
//! Leap seconds are never automatically computed during conversion to/from
//! UTC-based timestamps as this may provide a false sense of security and break
//! application code using a version of this library anterior to the
//! introduction of new leap seconds.
//!
//! [chrono]: https://crates.io/crates/chrono
//!
//!
//! # Features flags
//!
//! ### Support for `no-std`
//!
//! By default, this crate enables the `std` feature to access the operating
//! system clock, but specifying `default-features = false` makes it
//! `no-std`-compatible.
//!
//! ### Support for time-related crates
//!
//! Conversion methods to and from UTC date-time stamps from the [chrono] crate
//! are available with the `chrono` feature. This may also be used to parse and
//! format dates.
//!
//! ### Serialization
//!
//! `TaiTime` and related error types can be (de)serialized with `serde` by
//! activating the `serde` feature.
//!
//!
//! # Examples
//!
//! ```
//! use std::time::Duration;
//! use tai_time::MonotonicTime;
//!
//! // Set the timestamp to 2009-02-13 23:31:30.987654321 TAI.
//! let mut timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
//!
//! // Increment the timestamp by 123.456s.
//! timestamp += Duration::new(123, 456_000_000);
//!
//! assert_eq!(timestamp, MonotonicTime::new(1_234_568_014, 443_654_321));
//! assert_eq!(timestamp.as_secs(), 1_234_568_014);
//! assert_eq!(timestamp.subsec_nanos(), 443_654_321);
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::time::Duration;
#[cfg(feature = "std")]
use std::error::Error;
#[cfg(feature = "std")]
use std::time::SystemTime;

const NANOS_PER_SEC: u32 = 1_000_000_000;

/// Recommended [`TaiTime`] alias for the general case, with an epoch set at
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
/// use std::time::Duration;
/// use tai_time::MonotonicTime;
///
/// // Set the timestamp to 2009-02-13 23:31:30.987654321 TAI.
/// let mut timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, MonotonicTime::new(1_234_568_014, 443_654_321));
/// assert_eq!(timestamp.as_secs(), 1_234_568_014);
/// assert_eq!(timestamp.subsec_nanos(), 443_654_321);
/// ```
pub type MonotonicTime = TaiTime<0>;

/// A [`TaiTime`] alias with the Global Positioning System epoch.
///
/// This timestamp is relative to 1980-01-06 00:00:19 TAI or, equivalently, to
/// 1980-01-06 00:00:00 UTC.
///
/// # Examples
///
/// ```
/// use std::time::Duration;
/// use tai_time::GpsTime;
///
/// // Set the timestamp to 2019-02-18 23:31:49.987654321 TAI.
/// let mut timestamp = GpsTime::new(1_234_567_890, 987_654_321);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, GpsTime::new(1_234_568_014, 443_654_321));
/// assert_eq!(timestamp.as_secs(), 1_234_568_014);
/// assert_eq!(timestamp.subsec_nanos(), 443_654_321);
/// ```
pub type GpsTime = TaiTime<315_964_819>;

/// A [`TaiTime`] alias with the Galileo System Time epoch.
///
/// This timestamp is relative to 1999-08-21 23:59:47 UTC, or equivalently, to
/// 1999-08-22 00:00:19 TAI.
///
/// # Examples
///
/// ```
/// use std::time::Duration;
/// use tai_time::GstTime;
///
/// // Set the timestamp to 2038-10-04 23:31:49.987654321 TAI.
/// let mut timestamp = GstTime::new(1_234_567_890, 987_654_321);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, GstTime::new(1_234_568_014, 443_654_321));
/// assert_eq!(timestamp.as_secs(), 1_234_568_014);
/// assert_eq!(timestamp.subsec_nanos(), 443_654_321);
/// ```
pub type GstTime = TaiTime<935_280_019>;

/// A [`TaiTime`] alias with an epoch set at 1958-01-01 00:00:00 TAI.
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
/// use std::time::Duration;
/// use tai_time::Tai1958Time;
///
/// // Set the timestamp to 1997-02-13 23:31:30.987654321 TAI.
/// let mut timestamp = Tai1958Time::new(1_234_567_890, 987_654_321);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, Tai1958Time::new(1_234_568_014, 443_654_321));
/// assert_eq!(timestamp.as_secs(), 1_234_568_014);
/// assert_eq!(timestamp.subsec_nanos(), 443_654_321);
/// ```
pub type Tai1958Time = TaiTime<-378_691_200>;

/// A [`TaiTime`] alias with an epoch set at 1972-01-01 00:00:00 TAI.
///
/// Timestamps with this epoch are in common use in TAI-based clocks. The epoch
/// is exactly 10s in the past of 1972-01-01 00:00:00 UTC.
///
/// # Examples
///
/// ```
/// use std::time::Duration;
/// use tai_time::Tai1972Time;
///
/// // Set the timestamp to 2011-02-13 23:31:30.987654321 TAI.
/// let mut timestamp = Tai1972Time::new(1_234_567_890, 987_654_321);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, Tai1972Time::new(1_234_568_014, 443_654_321));
/// assert_eq!(timestamp.as_secs(), 1_234_568_014);
/// assert_eq!(timestamp.subsec_nanos(), 443_654_321);
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
/// use tai_time::MonotonicTime;
///
/// // Set the timestamp to 2009-02-13 23:31:30.987654321 TAI.
/// let mut timestamp = MonotonicTime::new(1_234_567_890, 987_654_321);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, MonotonicTime::new(1_234_568_014, 443_654_321));
/// assert_eq!(timestamp.as_secs(), 1_234_568_014);
/// assert_eq!(timestamp.subsec_nanos(), 443_654_321);
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

    /// Creates a timestamp relative to the epoch specified by `EPOCH_REF`.
    ///
    /// The number of seconds is for dates in the past of the epoch. The number
    /// of nanoseconds is always positive and always points towards the future.
    ///
    /// Note that `TaiTime<EPOCH_REF>::EPOCH` is by definition always the null
    /// timestamp, no matter the value of `EPOCH_REF`.
    ///
    /// # Panics
    ///
    /// This constructor will panic if the number of nanoseconds is greater than
    /// or equal to 1 second.
    ///
    /// # Example
    ///
    /// ```
    /// use std::time::Duration;
    /// use tai_time::{GpsTime, GstTime};
    ///
    /// // A GPS timestamp set to 2009-02-13 23:31:30.987654321 TAI.
    /// let timestamp = GpsTime::new(1_234_567_890, 987_654_321);
    ///
    /// // A timestamp set 3.5s before the GST epoch.
    /// let timestamp = GstTime::new(-4, 500_000_000);
    /// assert_eq!(
    ///     timestamp,
    ///     GstTime::EPOCH - Duration::new(3, 500_000_000)
    /// );
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

    /// Creates a timestamp from the current system time.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) at the current date. For reference, this offset
    /// has been +37s since 2017-01-01, a value which is to remain valid until
    /// at least 2024-12-31. See the [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// # Errors
    ///
    /// Returns an error if the reported system time is in the past of the Unix
    /// epoch or if the offset-adjusted timestamp is outside the representable
    /// range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Compute the current timestamp assuming that the current difference
    /// // between TAI and UTC time is 37s.
    /// let timestamp = MonotonicTime::from_system(37).unwrap();
    /// ```
    #[cfg(feature = "std")]
    pub fn from_system(leap_secs: i64) -> Result<Self, SystemTimeError> {
        let unix_time = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|_| SystemTimeError::InvalidSystemTime)?;

        // A correction in seconds that accounts for the offset between PTP and
        // Unix time as well as the offset between the PTP epoch and the
        // actual epoch of this `TaiTime`.
        let correction = leap_secs
            .checked_sub(EPOCH_REF)
            .ok_or(SystemTimeError::OutOfRange)?;

        Self::new(correction, 0)
            .checked_add(unix_time)
            .ok_or(SystemTimeError::OutOfRange)
    }

    /// Creates a TAI timestamp from a Unix timestamp.
    ///
    /// The last argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-31. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// Note that there is no unanimous consensus regarding the conversion
    /// between TAI and Unix timestamps prior to 1972.
    ///
    /// Returns `None` if the timestamp is outside the representable range or if
    /// the number of nanoseconds is greater than or equal to 1 second.
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Creates a timestamp corresponding to 2001-09-15 05:05:00.005 UTC,
    /// // accounting for the +32s difference between UAI and UTC on 2001-09-15.
    /// let timestamp = MonotonicTime::from_unix_timestamp(1_000_530_300, 5_000_000, 32).unwrap();
    /// assert_eq!(timestamp, MonotonicTime::new(1_000_530_332, 5_000_000));
    /// ```
    pub const fn from_unix_timestamp(secs: i64, subsec_nanos: u32, leap_secs: i64) -> Option<Self> {
        if let Some(secs) = secs.checked_add(leap_secs) {
            if let Some(secs) = secs.checked_sub(EPOCH_REF) {
                if subsec_nanos < NANOS_PER_SEC {
                    return Some(Self {
                        secs,
                        nanos: subsec_nanos,
                    });
                }
            }
        }

        None
    }

    /// Creates a timestamp from a `chrono::DateTime`.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-31. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// While no error will be reported, this method should not be considered
    /// appropriate for timestamps in the past of 1972.
    ///
    /// Returns `None` if the timestamp is outside the representable range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    /// use chrono::DateTime;
    ///
    /// let date_time = DateTime::parse_from_rfc3339("2001-09-15T05:05:00.005Z").unwrap();
    ///
    /// let timestamp = MonotonicTime::from_chrono_date_time(&date_time, 32).unwrap();
    /// assert_eq!(timestamp, MonotonicTime::new(1_000_530_332, 5_000_000));
    /// ```
    #[cfg(feature = "chrono")]
    pub const fn from_chrono_date_time<Tz: chrono::TimeZone>(
        date_time: &chrono::DateTime<Tz>,
        leap_secs: i64,
    ) -> Option<Self> {
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

        None
    }

    /// Returns the number of whole seconds relative to the
    /// [`EPOCH`](TaiTime::EPOCH).
    ///
    /// Consistently with the interpretation of seconds and nanoseconds in the
    /// [`new()`](TaiTime::new) constructor, seconds are always rounded towards
    /// `-∞`.
    ///
    /// # Examples
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
    /// value which is to remain valid until at least 2024-12-31. See the
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
    /// Returns `None` if the offset-adjusted timestamp is outside the
    /// representable range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Set the date to 2000-01-01 00:00:00 TAI.
    /// let timestamp = MonotonicTime::new(946_684_800, 0);
    ///
    /// // Convert to a Unix timestamp, accounting for the +32s difference between
    /// // TAI and UTC on 2000-01-01.
    /// let unix_secs = timestamp.as_unix_secs(32).unwrap();
    /// assert_eq!(unix_secs, 946_684_768)
    /// ```
    pub const fn as_unix_secs(&self, leap_secs: i64) -> Option<i64> {
        if let Some(secs) = self.secs.checked_sub(leap_secs) {
            return secs.checked_add(EPOCH_REF);
        }

        None
    }

    /// Returns a timestamp with a different reference epoch.
    ///
    /// Returns `None` if the new timestamp is outside the representable range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::{GpsTime, MonotonicTime};
    ///
    /// // Set the date to 2000-01-01 00:00:00 TAI.
    /// let timestamp = MonotonicTime::new(946_684_800, 0);
    ///
    /// // Convert to a GPS timestamp.
    /// let gps_timestamp: GpsTime = timestamp.as_tai_time().unwrap();
    /// ```
    pub const fn as_tai_time<const OTHER_EPOCH_REF: i64>(
        &self,
    ) -> Option<TaiTime<OTHER_EPOCH_REF>> {
        if let Some(epoch_diff) = EPOCH_REF.checked_sub(OTHER_EPOCH_REF) {
            if let Some(secs) = self.secs.checked_add(epoch_diff) {
                return Some(TaiTime {
                    secs,
                    nanos: self.nanos,
                });
            }
        }

        None
    }

    /// Returns a `chrono::DateTime` based on the timestamp.
    ///
    /// The argument is the difference between TAI and UTC time in seconds
    /// (a.k.a. leap seconds) applicable at the date represented by the
    /// timestamp. For reference, this offset has been +37s since 2017-01-01, a
    /// value which is to remain valid until at least 2024-12-31. See the
    /// [official IERS bulletin
    /// C](http://hpiers.obspm.fr/iers/bul/bulc/bulletinc.dat) for leap second
    /// announcements or the [IERS
    /// table](https://hpiers.obspm.fr/iers/bul/bulc/Leap_Second.dat) for
    /// current and historical values.
    ///
    /// While no error will be reported, this method should not be considered
    /// appropriate for timestamps in the past of 1972.
    ///
    /// Returns `None` if the offset-adjusted timestamp is outside the
    /// representable range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tai_time::MonotonicTime;
    ///
    /// // Set the date to 2000-01-01 00:00:00 TAI.
    /// let timestamp = MonotonicTime::new(946_684_800, 0);
    ///
    /// // Obtain a `chrono::DateTime`, accounting for the +32s difference between
    /// // TAI and UTC on 2000-01-01.
    /// let date_time = timestamp.as_chrono_date_time(32).unwrap();
    /// assert_eq!(date_time.to_string(), "1999-12-31 23:59:28 UTC");
    /// ```
    #[cfg(feature = "chrono")]
    pub fn as_chrono_date_time(&self, leap_secs: i64) -> Option<chrono::DateTime<chrono::Utc>> {
        self.as_unix_secs(leap_secs)
            .and_then(|secs| chrono::DateTime::from_timestamp(secs, self.nanos))
    }

    /// Adds a duration to a timestamp, checking for overflow.
    ///
    /// Returns `None` if overflow occurred.
    ///
    /// # Examples
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

/// An error that may be returned when initializing a [`TaiTime`] from
/// system time.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SystemTimeError {
    /// The system time is in the past of the Unix epoch.
    InvalidSystemTime,
    /// The system time cannot be represented as a `TaiTime`.
    OutOfRange,
}

impl fmt::Display for SystemTimeError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSystemTime => "invalid system time".fmt(fmt),
            Self::OutOfRange => "timestamp out of range".fmt(fmt),
        }
    }
}

#[cfg(feature = "std")]
impl Error for SystemTimeError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn time_equality() {
        let t0 = MonotonicTime::new(123, 123_456_789);
        let t1 = MonotonicTime::new(123, 123_456_789);
        let t2 = MonotonicTime::new(123, 123_456_790);
        let t3 = MonotonicTime::new(124, 123_456_789);

        assert_eq!(t0, t1);
        assert_ne!(t0, t2);
        assert_ne!(t0, t3);
    }

    #[test]
    fn time_ordering() {
        let t0 = Tai1972Time::new(0, 1);
        let t1 = Tai1972Time::new(1, 0);

        assert!(t1 > t0);
    }

    #[cfg(feature = "std")]
    #[test]
    fn time_from_system_smoke() {
        const START_OF_2022: i64 = 1640995200;
        const START_OF_2050: i64 = 2524608000;

        let now_secs = MonotonicTime::from_system(0).unwrap().as_secs();

        assert!(now_secs > START_OF_2022);
        assert!(now_secs < START_OF_2050);
    }

    #[test]
    #[should_panic]
    fn time_invalid() {
        Tai1958Time::new(123, 1_000_000_000);
    }

    #[test]
    fn time_duration_since_smoke() {
        let t0 = MonotonicTime::new(100, 100_000_000);
        let t1 = MonotonicTime::new(123, 223_456_789);

        assert_eq!(
            t1.checked_duration_since(t0),
            Some(Duration::new(23, 123_456_789))
        );
    }

    #[test]
    fn time_duration_with_carry() {
        let t0 = MonotonicTime::new(100, 200_000_000);
        let t1 = MonotonicTime::new(101, 100_000_000);

        assert_eq!(
            t1.checked_duration_since(t0),
            Some(Duration::new(0, 900_000_000))
        );
    }

    #[test]
    fn time_duration_since_extreme() {
        const MIN_TIME: MonotonicTime = TaiTime::MIN;
        const MAX_TIME: MonotonicTime = TaiTime::MAX;

        assert_eq!(
            MAX_TIME.checked_duration_since(MIN_TIME),
            Some(Duration::new(u64::MAX, NANOS_PER_SEC - 1))
        );
    }

    #[test]
    fn time_duration_since_invalid() {
        let t0 = MonotonicTime::new(100, 0);
        let t1 = MonotonicTime::new(99, 0);

        assert_eq!(t1.checked_duration_since(t0), None);
    }

    #[test]
    fn time_add_duration_smoke() {
        let t = MonotonicTime::new(-100, 100_000_000);
        let dt = Duration::new(400, 300_000_000);

        assert_eq!(t + dt, MonotonicTime::new(300, 400_000_000));
    }

    #[test]
    fn time_add_duration_with_carry() {
        let t = MonotonicTime::new(-100, 900_000_000);
        let dt1 = Duration::new(400, 100_000_000);
        let dt2 = Duration::new(400, 300_000_000);

        assert_eq!(t + dt1, MonotonicTime::new(301, 0));
        assert_eq!(t + dt2, MonotonicTime::new(301, 200_000_000));
    }

    #[test]
    fn time_add_duration_extreme() {
        let t = MonotonicTime::new(i64::MIN, 0);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        assert_eq!(t + dt, MonotonicTime::new(i64::MAX, NANOS_PER_SEC - 1));
    }

    #[test]
    #[should_panic]
    fn time_add_duration_overflow() {
        let t = MonotonicTime::new(i64::MIN, 1);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        let _ = t + dt;
    }

    #[test]
    fn time_sub_duration_smoke() {
        let t = MonotonicTime::new(100, 500_000_000);
        let dt = Duration::new(400, 300_000_000);

        assert_eq!(t - dt, MonotonicTime::new(-300, 200_000_000));
    }

    #[test]
    fn time_sub_duration_with_carry() {
        let t = MonotonicTime::new(100, 100_000_000);
        let dt1 = Duration::new(400, 100_000_000);
        let dt2 = Duration::new(400, 300_000_000);

        assert_eq!(t - dt1, MonotonicTime::new(-300, 0));
        assert_eq!(t - dt2, MonotonicTime::new(-301, 800_000_000));
    }

    #[test]
    fn time_sub_duration_extreme() {
        let t = MonotonicTime::new(i64::MAX, NANOS_PER_SEC - 1);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        assert_eq!(t - dt, MonotonicTime::new(i64::MIN, 0));
    }

    #[test]
    #[should_panic]
    fn time_sub_duration_overflow() {
        let t = MonotonicTime::new(i64::MAX, NANOS_PER_SEC - 2);
        let dt = Duration::new(u64::MAX, NANOS_PER_SEC - 1);

        let _ = t - dt;
    }
}