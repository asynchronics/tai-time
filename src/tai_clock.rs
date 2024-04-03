use std::time::{Instant, SystemTime};

use crate::{BdtTime, GpsTime, GstTime, MonotonicTime, Tai1958Time, Tai1972Time, TaiTime};

/// A [`TaiClock`] alias generating [`MonotonicTime`] timestamps.
pub type MonotonicClock = TaiClock<{ MonotonicTime::EPOCH_REF }>;

/// A [`TaiClock`] alias generating [`GpsTime`] timestamps.
pub type GpsClock = TaiClock<{ GpsTime::EPOCH_REF }>;

/// A [`TaiClock`] alias generating [`GstTime`] timestamps.
pub type GstClock = TaiClock<{ GstTime::EPOCH_REF }>;

/// A [`TaiClock`] alias generating [`BdtTime`] timestamps.
pub type BdtClock = TaiClock<{ BdtTime::EPOCH_REF }>;

/// A [`TaiClock`] alias generating [`Tai1958Time`] timestamps.
pub type Tai1958Clock = TaiClock<{ Tai1958Time::EPOCH_REF }>;

/// A [`TaiClock`] alias generating [`Tai1972Time`] timestamps.
pub type Tai1972Clock = TaiClock<{ Tai1972Time::EPOCH_REF }>;

/// A monotonic clock that generates [`TaiTime`] timestamps.
///
/// This clock internally relies on [`Instant::now`] and can therefore be used
/// on systems that do not support [`TaiTime::now`], or when the clock does not
/// need to use the wall clock time as absolute reference.
///
/// A `TaiClock` instance can be simultaneously accessed from several threads.
///
/// See also: [`MonotonicClock`], [`GpsClock`], [`GstClock`], [`BdtClock`],
/// [`Tai1958Clock`] and [`Tai1972Clock`].
///
/// # Examples
///
/// ```
/// use std::thread;
/// use std::sync::Arc;
/// use tai_time::TaiClock;
///
/// type MyCustomClock = TaiClock<123>;
///
/// // Initialize the TAI clock assuming that the current difference
/// // between TAI and UTC time is 37s.
/// let clock = Arc::new(MyCustomClock::init_from_utc(37));
///
/// // Time the execution of 2 different threads.
/// let th1 = thread::spawn({
///     let clock = clock.clone();
///     move || clock.now()
/// });
/// let th2 = thread::spawn(
///     move || clock.now()
/// );
/// let t1 = th1.join().unwrap();
/// let t2 = th2.join().unwrap();
///
/// println!("thread 1 has completed at {} TAI", t1);
/// println!("thread 2 has completed at {} TAI", t2);
/// ```
pub struct TaiClock<const EPOCH_REF: i64> {
    timestamp_ref: TaiTime<EPOCH_REF>,
    instant_ref: Instant,
}

impl<const EPOCH_REF: i64> TaiClock<EPOCH_REF> {
    /// Initializes the clock by associating the current wall clock time to the
    /// provided timestamp.
    ///
    /// Future calls to [`now`](Self::now) will return timestamps that are
    /// relative to the provided timestamp, with a constant offset with respect
    /// to the wall clock time.
    pub fn init_at(now: TaiTime<EPOCH_REF>) -> Self {
        Self {
            timestamp_ref: now,
            instant_ref: Instant::now(),
        }
    }

    /// Initializes the clock from the UTC system clock.
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
    /// Since it is not possible to get both monotonic and UTC clock timestamps
    /// with a single system call, this constructor attempts to select the best
    /// correlated pair of monotonic and UTC system clock timestamps from
    /// several measurements. This is currently done by interleaving 3 calls to
    /// `SystemTime::now` and 4 calls to `Instant::now`.
    pub fn init_from_utc(leap_secs: i64) -> Self {
        const EXTRA_SAMPLES: usize = 2;

        let mut instant = Instant::now();
        let system_time = SystemTime::now();
        let mut instant_after = Instant::now();

        let delta = instant_after.saturating_duration_since(instant); // uncertainty on measurement.
        let mut measurement = (instant, delta, system_time);

        for _ in 0..EXTRA_SAMPLES {
            instant = instant_after;
            let system_time = SystemTime::now();
            instant_after = Instant::now();
            let delta = instant_after.saturating_duration_since(instant);

            // If the uncertainty on this measurement is lower then prefer this
            // measurement. Measurements with a null uncertainty are discarded
            // as they are most likely indicative of a platform bug.
            if measurement.1.is_zero() || (delta < measurement.1 && !delta.is_zero()) {
                measurement = (instant, delta, system_time);
            }
        }

        Self {
            timestamp_ref: TaiTime::from_system_time(&measurement.2, leap_secs),
            instant_ref: measurement.0 + measurement.1.mul_f32(0.5), // take the mid-point
        }
    }

    /// Returns a TAI timestamp corresponding to the current wall clock time.
    ///
    /// The returned timestamp will never be lower than a timestamp returned by
    /// a previous call to `now`.
    pub fn now(&self) -> TaiTime<EPOCH_REF> {
        let delta = Instant::now().saturating_duration_since(self.instant_ref);

        self.timestamp_ref + delta
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clock_init_at_smoke() {
        use std::time::Duration;

        const TIME_REF: MonotonicTime = MonotonicTime::new(-12345678, 987654321); // just an arbitrary value
        const TOLERANCE_MILLIS: Duration = Duration::from_millis(20);

        let clock = MonotonicClock::init_at(TIME_REF);

        assert!(clock.now().duration_since(TIME_REF) <= TOLERANCE_MILLIS);
    }

    #[test]
    fn clock_init_from_utc_smoke() {
        use std::time::Duration;

        const LEAP_SECS: i64 = 123; // just an arbitrary value
        const TOLERANCE_MILLIS: Duration = Duration::from_millis(20);

        let clock = MonotonicClock::init_from_utc(LEAP_SECS);

        let utc_now = SystemTime::UNIX_EPOCH.elapsed().unwrap();
        let tai_now_from_utc = MonotonicTime::new(LEAP_SECS, 0) + utc_now;
        let tai_now_from_clock = clock.now();

        if tai_now_from_clock >= tai_now_from_utc {
            assert!(tai_now_from_clock.duration_since(tai_now_from_utc) <= TOLERANCE_MILLIS);
        } else {
            assert!(tai_now_from_utc.duration_since(tai_now_from_clock) <= TOLERANCE_MILLIS);
        }
    }
}
