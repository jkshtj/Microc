# What's in this repo?
Rust is an awesome programming language which has truly empowered me by making the "hard" things simple. Looking at some of the things that the Rust compiler does, such as, [non-lexical lifetimes](https://stackoverflow.com/questions/50251487/what-are-non-lexical-lifetimes), closure captures, preventing mutable aliasing etc. I was very fascinated by all the things that a compiler can do. So much so that I decided to write one myself in order to understand how compilers work end to end.

This repo contains my hands-on attempt to understand compilers. It contains the grammar and the compiler for a toy language called **Microc**. [Microc](https://github.com/jain98/Microc/blob/master/token_definitions.txt) is a super minimal, strongly typed language that supports 3 types - ints, floats & string literals, if/else conditional blocks, for loops, comments and user-defined functions.

My compiler currently compiles Microc to an educational/fictional target called [tiny](https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt). So far I have added support for everything other than function calls, which I will be doing very soon.


