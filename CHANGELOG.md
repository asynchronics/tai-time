# [Unreleased]

* honor formatter precision specifier (`{:.N}`) for nanosecond display.


# 0.3.0 (2024-04-07)

* **:warning: Breaking API changes:** Make `new()` return an `Option` ([#16]).
* **:warning: Breaking API changes:** Implement some new `try_from_*` methods
  and rename some former `from_*` methods into `try_from_*` for consistency
  ([#17]).
* Use `Nix` crate instead of `libc` to remove `unsafe` in `now()` implementation
  ([#18]).

[#16]: https://github.com/asynchronics/tai-time/pull/16
[#17]: https://github.com/asynchronics/tai-time/pull/17
[#18]: https://github.com/asynchronics/tai-time/pull/18


# 0.2.2 (2024-04-03)

* Make it possible to initialize a `TaiClock` from an arbitrary `Instant` or an
  arbitrary `SystemTime` ([#12]).
* Derive more traits on `TaiTime` and `TaiClock`.

[#12]: https://github.com/asynchronics/tai-time/pull/12


# 0.2.1 (2024-04-03)

* Add `TaiClock`, a monotonic clock that can generate TAI timestamps on all
  systems where `std` is available ([#8]).

[#8]: https://github.com/asynchronics/tai-time/pull/8


# 0.2.0 (2024-04-03)

* Enable construction of timestamps from a date-time representation and
  implement the `FromStr` and `Display` traits to enable conversions to and from
  date-time strings ([#4]).
* **:warning: Breaking API changes:** Add support for the Linux system TAI clock ([#5]) and
  rename former `now` method to `now_from_utc`.
* **:warning: Breaking API changes:** Panic instead of returning errors on overflow ([#7]).

[#4]: https://github.com/asynchronics/tai-time/pull/4
[#5]: https://github.com/asynchronics/tai-time/pull/5
[#7]: https://github.com/asynchronics/tai-time/pull/7


# 0.1.0 (2024-03-26)

Initial release
