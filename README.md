# CAS CS 400 Course Library

This repository has the standard library used for the course CAS CS
400 at Boston University.  It is a simplification of the agda standard
library.  In particular, its functions are not universe polymorphic
and there is no use of unicode.

## Set-Up Instructions

1. Clone this repository to some directory on your machine (referred
   to as `$HERE` below).
2. Add the line `$HERE/CS400-Lib/cs400-lib.agda-lib` to your
   `$HOME/.agda/libraries` file, creating it if it does not already
   exists.
3. Add the line `cs400-lib` to your `$HOME/.agda/defaults` file,
   creating it if it doesn't already exists.

When you work on a piece of Agda code, you should be able to include
the line `open import CS400-Lib` to introduce the functions used for
the course into your file.
