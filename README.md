# schubfach

[![crate](https://img.shields.io/crates/v/schubfach.svg)](https://crates.io/crates/schubfach)
[![documentation](https://docs.rs/schubfach/badge.svg)](https://docs.rs/schubfach)
[![crate](https://img.shields.io/crates/l/schubfach.svg)](https://github.com/blueglyph/schubfach/blob/master/LICENSE-MIT)
<!-- [![build status](https://github.com/blueglyph/schubfach/actions/workflows/master.yml/badge.svg)](https://github.com/blueglyph/schubfach/actions) -->

<hr/>

# Schubfach algorithm

This is a Rust implementation of the Schufbach algorithm that converts IEEE-754 double-precision floating-point values to their string decimal representation.

It is performant and has a relatively small footprint. For performance comparisons, check the [Drachennest project](https://github.com/abolz/Drachennest) or the [Dragonbox project](https://github.com/jk-jeon/dragonbox).

## Status

**WARNING! This is very much work-in-progress.** 

The code is functional but must still be more thoroughly tested and optimized. The API is not considered as definitive yet, nor is the code architecture.

Current features:
- double-precision values (f64) are supported
- a simple function converts values to a simple string format, either fixed or scientific depending on the value
- a more complex function offers more choices, like 
  - fixed / scientific format selection
  - precision
  - correct rounding to even
  - interface through method or Display trait

Planned features:
- engineering format
- support for f32 values

## References

The algorithm is described by its author in the following article:

- Raffaello Giulietti, "[The Schubfach way to render doubles](https://drive.google.com/file/d/1luHhyQF9zKlM8yJ1nebU0OgVYhfC6CBN)", March 16, 2020,

The author made a Java implementation:

- https://github.com/c4f7fcce9cb06515/Schubfach

The Rust code is mainly a translation from Alexander Bolz's C++ implementation:

- https://github.com/abolz/Drachennest

  with the following licence:

      Copyright 2020 Alexander Bolz
  
      Distributed under the Boost Software License, Version 1.0.
       (See accompanying file LICENSE_1_0.txt or copy at 
        https://www.boost.org/LICENSE_1_0.txt)

# Compatibility

The `schubfach` crate is tested for rustc 1.68 and greater, on Windows 64-bit and Linux 64/32-bit platforms. There shouldn't be any problem with older versions.

<!--
# Releases

[RELEASES.md](RELEASES.md) keeps a log of all the releases.
-->

# License

Licensed under [MIT license](https://choosealicense.com/licenses/mit/).
