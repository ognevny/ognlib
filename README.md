<p align="center">
  <a title="GitHub Actions" href="https://github.com/ognevny/ognlib/actions"><img alt="workflow Status" src="https://img.shields.io/github/actions/workflow/status/ognevny/ognlib/ci.yml?branch=master&longCache=true&style=flat-square&label=build&logo=github"></a><!--
  -->
  <a title="Crate" href="https://crates.io/crates/ognlib"><img src="https://img.shields.io/crates/v/ognlib.svg?style=flat-square"></a><!--
  -->
  <a title="Docs" href="https://docs.rs/ognlib"><img src="https://img.shields.io/badge/docs.rs-ognlib-red?style=flat-square"></a><!--
  -->
  <a title="Open in vscode.dev" href="https://open.vscode.dev/ognevny/ognlib"><img src="https://img.shields.io/badge/Open%20in%20Visual%20Studio%20Code-blue?logo=visual-studio-code&logoColor=ffffff&style=flat-square"></a><!--
  -->
</p>

# ognlib

ognlib is created to practice Rust (for me), so you won't find any new code, that can be used for
your projects. It contains code for operations under number digits, some power algorithms, radix
numbers and some algorithms.

## Features

By default the feature `std` is enable. It's enabled for `rayon` crate, which doesn't provide
`no_std` feature. You can disable it with `default-features = false`. This makes some code a bit
slower and makes some sort algorithmes unavialable.

## Contributing

I'm open for your feedback! If you want to improve my code and explain everything that is new for
me, feel free to open PR in GitHub repo.

## Why was it created?

Currently I'm learning Rust and I want to have practice on something, so I created this lib based on
functions from
[`ognfunc.cpp`](https://github.com/ognevnydemon/my-code/blob/master/dad-is-great-in-C/ognfunc.cpp)
file I made for the another repo.
