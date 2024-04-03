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
