# ognlib

[![CI Status](https://github.com/ognevnydemon/ognlib/workflows/CI/badge.svg?style=flat-square)](https://github.com/ognevnydemon/ognlib/actions)
[![Crate](https://img.shields.io/crates/v/ognlib.svg?style=flat-square)](https://crates.io/crates/ognlib)
[![API](https://docs.rs/ognlib/badge.svg?style=flag-square)](https://docs.rs/ognlib)
[![Open in Visual Studio Code](https://img.shields.io/badge/Open%20in%20Visual%20Studio%20Code-blue?logo=visual-studio-code&logoColor=ffffff&style=flat-square)](https://open.vscode.dev/ognevnydemon/ognlib)
[![License](https://img.shields.io/badge/License-Apache--2.0-blue.svg?style=flat-square)](https://github.com/ognevnydemon/ognlib/blob/master/LICENSE-APACHE)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg?style=flat-square)](https://github.com/ognevnydemon/ognlib/blob/master/LICENSE-MIT)

ognlib is created to practice Rust (for me), so you won't find any new code, that can be used for your projects. It contains code for operations under number digits, some power algorithms, radix numbers and some algorithms.
## How to build on Windows?
first: this crate DOES NOT compiles for `*-msvc` targets, so use cargo from MSYS2.
#### Installing MSYS2
to cleanly install MSYS2 follow these steps:
- install it from https://msys2.org/ and follow all steps provided
- install all needed dependencies with
```console
$ pacman -S mingw-w64-ucrt-x86_64-rust mingw-w64-ucrt-x86_64-autotools 
```
then you can use this crate for your projects.
IMPORTANT: compile-time may take up to 10 minutes (or even more!), so just be patient.
## Contributing
I'm open for your feedback! If you want to improve my code and explain everything that is new for me, feel free to open PR in GitHub repo.
## Why was it created?
Currently I'm learning Rust and I want to have practice on something, so I created this lib based on functions from [`ognfunc.cpp`](https://github.com/ognevnydemon/my-code/blob/master/dad-is-great-in-C/ognfunc.cpp) file I made for the another repo.
