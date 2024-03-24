# tai-time

A nanosecond-precision monotonic clock timestamp based on the TAI time standard.

[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](https://github.com/asynchronics/diatomic-waker#license)


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

[TAI]: https://en.wikipedia.org/wiki/International_Atomic_Time
[TAI64N]: https://cr.yp.to/libtai/tai64.html


## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
tai-time = { git = "https://github.com/asynchronics/tai-time.git" }
```


## Example

```rust
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
let gps_t0: GpsTime = t0.as_tai_time().unwrap();
println!("{}s, {}ns", gps_t0.as_secs(), gps_t0.subsec_nanos());
```


## Design choices and limitations

Leap seconds are never automatically computed during conversion to/from
UTC-based timestamps. This is intentional: doing so would give a false sense of
security and, since leap seconds cannot be predicted far in the future, this
could unexpectedly break user code using a version of this library anterior to
the introduction of new leap seconds.

At the moment, no date-time parsing or formatting facilities are provided. These
can be performed using other crates such as [chrono] (see [features
flags](#support-for-time-related-crates)).

[chrono]: https://crates.io/crates/chrono


## Features flags

### Support for `no-std`

By default, this crate enables the `std` feature to access the operating system
clock and allow conversion to/from `time::SystemTime`, but specifying
`default-features = false` makes it `no-std`-compatible.

### Support for time-related crates

Conversion methods to and from UTC date-time stamps from the [chrono] crate
are available with the `chrono` feature. This may also be used to parse and
format dates.

### Serialization

`TaiTime` and related error types can be (de)serialized with
`serde` by activating the `serde` feature.

## License

This software is licensed under the [Apache License, Version
2.0](LICENSE-APACHE) or the [MIT license](LICENSE-MIT), at your option.


## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
