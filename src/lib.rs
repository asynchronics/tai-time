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
//! UTC-based timestamps. This is intentional: doing so would give a false sense
//! of security and, since leap seconds cannot be predicted far in the future,
//! this could unexpectedly break user code using a version of this library
//! anterior to the introduction of new leap seconds.
//!
//! At the moment, no date-time parsing or formatting facilities are provided.
//! These can be performed using other crates such as [chrono] (see [features
//! flags](#support-for-time-related-crates)).
//!
//!
//! [chrono]: https://crates.io/crates/chrono
//!
//!
//! # Features flags
//!
//! ### Support for `no-std`
//!
//! By default, this crate enables the `std` feature to access the operating
//! system clock and allow conversion to/from `time::SystemTime`, but specifying
//! `default-features = false` makes it `no-std`-compatible.
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
#![cfg_attr(
    feature = "std",
    doc = r##"
```
use tai_time::{GpsTime, MonotonicTime};

// A timestamp dated 2009-02-13 23:31:30.987654321 TAI.
// (same value as Unix timestamp for 2009-02-13 23:31:30.987654321 UTC).
let t0 = MonotonicTime::new(1_234_567_890, 987_654_321);

// Current TAI time based on system clock, assuming 37 leap seconds.
let now = MonotonicTime::now(37).unwrap();

// Elapsed time since timestamp.
let dt = now.duration_since(t0);
println!("{}s, {}ns", dt.as_secs(), dt.subsec_nanos());

// Current GPS time.
let gps_t0: GpsTime = t0.to_tai_time().unwrap();
println!("{}s, {}ns", gps_t0.as_secs(), gps_t0.subsec_nanos());
```"##
)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

use core::fmt;
use core::ops::{Add, AddAssign, Sub, SubAssign};
use core::time::Duration;

const NANOS_PER_SEC: u32 = 1_000_000_000;

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
/// use std::time::Duration;
/// use tai_time::MonotonicTime;
///
/// // Set the timestamp to 2009-02-13 23:31:30.333333333 TAI.
/// let mut timestamp = MonotonicTime::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, MonotonicTime::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
/// ```
pub type MonotonicTime = TaiTime<0>;

/// A [`TaiTime`] alias using the Global Positioning System (GPS) epoch.
///
/// This timestamp is relative to 1980-01-06 00:00:19 TAI (1980-01-06 00:00:00
/// UTC).
///
/// # Examples
///
/// ```
/// use std::time::Duration;
/// use tai_time::GpsTime;
///
/// // Set the timestamp to 2019-02-18 23:31:49.333333333 TAI.
/// let mut timestamp = GpsTime::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, GpsTime::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
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
/// use std::time::Duration;
/// use tai_time::GstTime;
///
/// // Set the timestamp to 2038-10-04 23:31:49.333333333 TAI.
/// let mut timestamp = GstTime::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, GstTime::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
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
/// use std::time::Duration;
/// use tai_time::BdtTime;
///
/// // Set the timestamp to 2045-02-13 23:32:03.333333333 TAI.
/// let mut timestamp = BdtTime::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, BdtTime::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
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
/// use std::time::Duration;
/// use tai_time::Tai1958Time;
///
/// // Set the timestamp to 1997-02-13 23:31:30.333333333 TAI.
/// let mut timestamp = Tai1958Time::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, Tai1958Time::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
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
/// use std::time::Duration;
/// use tai_time::Tai1972Time;
///
/// // Set the timestamp to 2011-02-13 23:31:30.333333333 TAI.
/// let mut timestamp = Tai1972Time::new(1_234_567_890, 333_333_333);
///
/// // Increment the timestamp by 123.456s.
/// timestamp += Duration::new(123, 456_000_000);
///
/// assert_eq!(timestamp, Tai1972Time::new(1_234_568_013, 789_333_333));
/// assert_eq!(timestamp.as_secs(), 1_234_568_013);
/// assert_eq!(timestamp.subsec_nanos(), 789_333_333);
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

    /// Creates a timestamp relative to the epoch.
    ///
    /// The number of seconds is for dates in the past of the epoch. The number
    /// of nanoseconds is always positive and always points towards the future.
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

    /// Creates a timestamp from the system clock.
    ///
    /// This is a shorthand for `from_system_time(&SystemTime::now(),
    /// leap_secs)`.
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
    /// Beware that the behavior of the system clock near a leap second
    /// shouldn't be relied upon, where *near* might actually stand for the
    /// whole 24h period preceding a leap second due to the possible use of the
    /// so-called *leap second smearing* strategy.
    ///
    /// Returns an error if the timestamp is outside the representable range.
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
    /// value which is to remain valid until at least 2024-12-31. See the
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

    /// Returns the number of whole seconds relative to the
    /// [`EPOCH`](TaiTime::EPOCH).
    ///
    /// Consistently with the interpretation of seconds and nanoseconds in the
    /// [`new()`](TaiTime::new) constructor, seconds are always rounded towards
    /// `-∞`.
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

/// The error type returned when the result of a conversion to or from a
/// [`TaiTime`] is outside the representable range.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OutOfRangeError(());

impl fmt::Display for OutOfRangeError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        "timestamp out of representable range".fmt(fmt)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OutOfRangeError {}

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
    fn invalid() {
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
}
