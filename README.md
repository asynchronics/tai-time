# tai-time

A nanosecond-precision monotonic clock timestamp based on the TAI time standard.

[![Cargo](https://img.shields.io/crates/v/tai-time.svg)](https://crates.io/crates/tai-time)
[![Documentation](https://docs.rs/tai-time/badge.svg)](https://docs.rs/tai-time)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](https://github.com/asynchronics/tai-time#license)


## Overview

While Rust's standard library already provides the `std::time::Instant`
monotonic timestamp, its absolute value is opaque. In many scientific and
engineering applications such as simulations, GNSS and synchronized systems,
monotonic timestamps based on absolute time references are required.

This crate provides a fairly unopinionated timestamp for such applications with
a focus on simplicity, adherence to Rust's `std::time` idioms and
interoperability with the `std::time::Duration` type.

A `TaiTime` timestamp specifies a [TAI] point in time. It is represented as a 64-bit
signed number of seconds and a positive number of nanoseconds, relative to
1970-01-01 00:00:00 TAI or to any arbitrary epoch. This timestamp format has a
number of desirable properties:

- it is computationally efficient for arithmetic operations involving the
  standard `Duration` type, which uses a very similar internal
  representation,
- when a 1970 epoch is chosen (see `MonotonicTime`):
  * exact conversion to a Unix timestamp is trivial and only requires
    subtracting from this timestamp the number of leap seconds between TAI
    and UTC time,
  * it constitutes a strict 96-bit superset of 80-bit PTP IEEE-1588
    timestamps, a widely used standard for high-precision time distribution,
  * it is substantially similar (though not strictly identical) to the
    [TAI64N] time format,
- with a custom epoch, other monotonic clocks such as the Global Position System
  clock, the Galileo System Time clock and the BeiDou Time clock can be
  represented (see `GpsTime`, `GstTime`, `BdtTime`, `Tai1958Time` and
  `Tai1972Time`).

`MonotonicTime`, an alias for `TaiTime` with an epoch set at 1970-01-01 00:00:00
TAI, is the recommended timestamp choice when no specific epoch is mandated.

On systems where `std` is present, `TaiClock` can generate TAI timestamps based
on the monotonic system clock. On platforms that support it (currently, only
Linux), the native TAI system clock time can be retrieved with `TaiTime::now`.

[TAI]: https://en.wikipedia.org/wiki/International_Atomic_Time
[TAI64N]: https://cr.yp.to/libtai/tai64.html


## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
tai-time = "0.3.1"
```


## Examples

Basic usage:

```rust
use tai_time::{GpsTime, MonotonicClock, MonotonicTime};

// A timestamp dated 2009-02-13 23:31:30.987654321 TAI.
// (same value as Unix timestamp for 2009-02-13 23:31:30.987654321 UTC).
let t0 = MonotonicTime::new(1_234_567_890, 987_654_321).unwrap();

// Current TAI time based on the system clock, assuming 37 leap seconds.
let clock = MonotonicClock::init_from_utc(37);
let t1 = clock.now();
println!("Current TAI time: {}", t1);

// Elapsed time between `t0` and `t1`.
let dt = t1.duration_since(t0);
println!("t1 -t0: {}s, {}ns", dt.as_secs(), dt.subsec_nanos());

// Elapsed time since `t1`.
let dt = clock.now().duration_since(t1);
println!("Elapsed: {}s, {}ns", dt.as_secs(), dt.subsec_nanos());

// Print out `t1` as a GPS timestamp.
let gps_t1: GpsTime = t1.to_tai_time().unwrap();
println!("GPS timestamp: {}s, {}ns", gps_t1.as_secs(), gps_t1.subsec_nanos());
```

Construction from date-time fields and date-time strings:

```rust
use tai_time::{MonotonicTime, Tai1958Time};
let t0 = MonotonicTime::try_from_date_time(2222, 11, 11, 12, 34, 56, 789000000).unwrap();
// The `FromStr` implementation accepts date-time stamps with the format:
// [±][Y]...[Y]YYYY-MM-DD hh:mm:ss[.d[d]...[d]]
// or:
// [±][Y]...[Y]YYYY-MM-DD'T'hh:mm:ss[.d[d]...[d]]
assert_eq!("2222-11-11 12:34:56.789".parse(), Ok(t0));
```

Formatted display as date-time:

```rust
use tai_time::MonotonicTime;
let t0 = MonotonicTime::try_from_date_time(1234, 12, 13, 14, 15, 16, 123456000).unwrap();
assert_eq!(
    format!("{}", t0),
    "1234-12-13 14:15:16.123456"
);
assert_eq!(
    format!("{:.0}", t0),
    "1234-12-13 14:15:16"
);
assert_eq!(
    format!("{:.3}", t0),
    "1234-12-13 14:15:16.123"
);
assert_eq!(
    format!("{:.9}", t0),
    "1234-12-13 14:15:16.123456000"
);
```

Reading TAI time directly from the system clock (Linux-only, requires
feature `tai_clock`):

```rust
use tai_time::MonotonicTime;

let now = MonotonicTime::now();

println!("Current TAI time: {}", now);
```


## Design choices and limitations

Leap seconds are never automatically computed during conversion to/from
UTC-based timestamps. This is intentional: since leap seconds cannot be
predicted far in the future, any attempt to "hide" their existence from user
code would lend a false sense of security and, down the line, would make it
more difficult to identify failures subsequent to the introduction of new
leap seconds.


## Features flags

### Support for `no-std`

By default, this crate enables the `std` feature to access the operating
system clock and allow conversion to/from `time::SystemTime`. It can be made
`no-std`-compatible by specifying `default-features = false`.

### Support for time-related crates

Conversion methods to and from UTC date-time stamps from the [chrono] crate
are available with the `chrono` feature.

[chrono]: https://crates.io/crates/chrono

### TAI system clock

On Linux only, it is possible to read TAI time from the system clock by
activating the `tai_clock` feature. Be sure to read about possible caveats
in `TaiTime::now`.

### Serialization

`TaiTime` and related error types can be (de)serialized with `serde` by
activating the `serde` feature.

### `defmt` support

Activating the `defmt` feature will derive the
[`defmt::Format`](https://defmt.ferrous-systems.com/format) trait on `TaiTime`
and related error types.

## License

This software is licensed under the [Apache License, Version
2.0](LICENSE-APACHE) or the [MIT license](LICENSE-MIT), at your option.


## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
