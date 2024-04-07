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
/// on systems that do not support [`TaiTime::now`], or when the time reference
/// needs to differ from the wall clock time (clock with offset).
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
#[derive(Copy, Clone, Debug, Hash)]
pub struct TaiClock<const EPOCH_REF: i64> {
    timestamp_ref: TaiTime<EPOCH_REF>,
    wall_clock_ref: Instant,
}

impl<const EPOCH_REF: i64> TaiClock<EPOCH_REF> {
    /// Initializes the clock by associating a TAI timestamp to the current wall
    /// clock time.
    ///
    /// Future calls to [`now`](Self::now) will return timestamps that are
    /// relative to the provided timestamp, with a constant offset with respect
    /// to the monotonic wall clock time.
    pub fn init_at(now: TaiTime<EPOCH_REF>) -> Self {
        Self::init_from_instant(now, Instant::now())
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
    /// Note that `TaiClock` is based on the monotonic system clock while UTC
    /// time can only be obtained from the non-monotonic system clock. This
    /// constructor attempts to find a well-correlated pair of monotonic and UTC
    /// system clock timestamps by collecting several candidate samples from
    /// interleaved calls to `SystemTime::now` and `Instant::now`.
    pub fn init_from_utc(leap_secs: i64) -> Self {
        let (system_time_ref, instant_ref) = get_correlated_time_refs();

        Self::init_from_instant(
            TaiTime::from_system_time(&system_time_ref, leap_secs),
            instant_ref,
        )
    }

    /// Initializes the clock by associating the provided TAI timestamp to the
    /// provided `Instant`.
    ///
    /// The `wall_clock_ref` argument may lie in the past or in the future of
    /// the current wall clock time.
    ///
    /// Future calls to [`now`](Self::now) will return timestamps with a
    /// constant offset with respect to the monotonic wall clock time. The
    /// offset is defined by the requirement that [`now`](Self::now) should
    /// return `timestamp_ref` when the wall clock time matches
    /// `wall_clock_ref`.
    pub fn init_from_instant(timestamp_ref: TaiTime<EPOCH_REF>, wall_clock_ref: Instant) -> Self {
        Self {
            timestamp_ref,
            wall_clock_ref,
        }
    }

    /// Initializes the clock by associating a TAI timestamp to a `SystemTime`.
    ///
    /// The `wall_clock_ref` argument may lie in the past or in the future of
    /// the current wall clock time.
    ///
    /// Future calls to [`now`](Self::now) will return timestamps with a
    /// constant offset with respect to the monotonic wall clock time. The
    /// offset is defined by the requirement that [`now`](Self::now) should
    /// return `timestamp_ref` when the wall clock time matches
    /// `wall_clock_ref`.
    ///
    /// Note that `TaiClock` is based on the monotonic system clock while UTC
    /// time can only be obtained from the non-monotonic system clock. This
    /// constructor attempts to find a well-correlated pair of monotonic and UTC
    /// system clock timestamps by collecting several candidate samples from
    /// interleaved calls to `SystemTime::now` and `Instant::now`.
    pub fn init_from_system_time(
        timestamp_ref: TaiTime<EPOCH_REF>,
        wall_clock_ref: SystemTime,
    ) -> Self {
        let (system_time_ref, instant_ref) = get_correlated_time_refs();

        let timestamp_ref = if wall_clock_ref > system_time_ref {
            timestamp_ref - wall_clock_ref.duration_since(system_time_ref).unwrap()
        } else {
            timestamp_ref + system_time_ref.duration_since(wall_clock_ref).unwrap()
        };

        Self::init_from_instant(timestamp_ref, instant_ref)
    }

    /// Returns a TAI timestamp corresponding to the current wall clock time.
    ///
    /// The returned timestamp will never be lower than a timestamp returned by
    /// a previous call to `now`.
    pub fn now(&self) -> TaiTime<EPOCH_REF> {
        let now = Instant::now();

        if now >= self.wall_clock_ref {
            self.timestamp_ref + now.duration_since(self.wall_clock_ref)
        } else {
            self.timestamp_ref - self.wall_clock_ref.duration_since(now)
        }
    }
}

/// Returns a pair of well-correlated `SystemTime` and `Instant`.
fn get_correlated_time_refs() -> (SystemTime, Instant) {
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

    // Take the best measurement and associate its `SystemTime` to the average
    // value of the `Instant`s measured just before and just after it.
    (measurement.2, measurement.0 + measurement.1.mul_f32(0.5))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clock_init_at_smoke() {
        use std::time::Duration;

        let time_ref: MonotonicTime = MonotonicTime::new(-12345678, 987654321).unwrap(); // just an arbitrary value
        const TOLERANCE: Duration = Duration::from_millis(20);

        let clock = MonotonicClock::init_at(time_ref);

        assert!(clock.now().duration_since(time_ref) <= TOLERANCE);
    }

    #[test]
    fn clock_init_from_utc_smoke() {
        use std::time::Duration;

        const LEAP_SECS: i64 = 123; // just an arbitrary value
        const TOLERANCE: Duration = Duration::from_millis(20);

        let clock = MonotonicClock::init_from_utc(LEAP_SECS);

        let utc_now = SystemTime::UNIX_EPOCH.elapsed().unwrap();
        let tai_now_from_utc = MonotonicTime::new(LEAP_SECS, 0).unwrap() + utc_now;
        let tai_now_from_clock = clock.now();

        if tai_now_from_clock >= tai_now_from_utc {
            assert!(tai_now_from_clock.duration_since(tai_now_from_utc) <= TOLERANCE);
        } else {
            assert!(tai_now_from_utc.duration_since(tai_now_from_clock) <= TOLERANCE);
        }
    }

    #[test]
    fn clock_init_from_past_instant_smoke() {
        use std::time::Duration;

        use crate::MonotonicTime;

        const OFFSET: Duration = Duration::from_secs(1000);
        const TOLERANCE: Duration = Duration::from_millis(20);

        let t0 = MonotonicTime::new(123, 456).unwrap();
        let clock = MonotonicClock::init_from_instant(t0, Instant::now() - OFFSET);

        let delta = clock.now().duration_since(t0 + OFFSET);
        assert!(delta <= TOLERANCE);
    }

    #[test]
    fn clock_init_from_future_instant_smoke() {
        use std::time::Duration;

        use crate::MonotonicTime;

        const OFFSET: Duration = Duration::from_secs(1000);
        const TOLERANCE: Duration = Duration::from_millis(20);

        let t0 = MonotonicTime::new(123, 456).unwrap();
        let clock = MonotonicClock::init_from_instant(t0, Instant::now() + OFFSET);

        let delta = clock.now().duration_since(t0 - OFFSET);
        assert!(delta <= TOLERANCE);
    }

    #[test]
    fn clock_init_from_past_system_time_smoke() {
        use std::time::Duration;

        use crate::MonotonicTime;

        const OFFSET: Duration = Duration::from_secs(1000);
        const TOLERANCE: Duration = Duration::from_millis(20);

        let t0 = MonotonicTime::new(123, 456).unwrap();
        let clock = MonotonicClock::init_from_system_time(t0, SystemTime::now() - OFFSET);

        let delta = clock.now().duration_since(t0 + OFFSET);
        assert!(delta <= TOLERANCE);
    }

    #[test]
    fn clock_init_from_future_system_time_smoke() {
        use std::time::Duration;

        use crate::MonotonicTime;

        const OFFSET: Duration = Duration::from_secs(1000);
        const TOLERANCE: Duration = Duration::from_millis(20);

        let t0 = MonotonicTime::new(123, 456).unwrap();
        let clock = MonotonicClock::init_from_system_time(t0, SystemTime::now() + OFFSET);

        let delta = clock.now().duration_since(t0 - OFFSET);
        assert!(delta <= TOLERANCE);
    }
}
