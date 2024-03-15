# CAS CS 400 Course Library

This repository contains the library used for the course CAS CS 400 at
Boston University.  It is a simplification of a very small fragment of
the agda standard library.  In particular, its functions are not
universe polymorphic and there is no use of unicode.

## Set-Up Instructions

1. Clone this repository to some directory (referred to as `$HERE`
   below).
2. Add the line `$HERE/CS400-Lib/cs400-lib.agda-lib` to your
   `$HOME/.agda/libraries` file, creating it if it does not already
   exist.
3. Add the line `cs400-lib` to your `$HOME/.agda/defaults` file,
   creating it if it doesn't already exist.

When you work on a piece of Agda code, you should be able to include
the line `open import CS400-Lib` to introduce the functions used for
the course into your file.

## Github Codespace

If you have trouble setting up this library, or just want to try it
out without setting it up, you can create a GitHub codespace at this
repo
[here](https://github.com/codespaces/new?hide_repo_select=true&ref=main&repo=755165974&skip_quickstart=true&machine=standardLinux32gb&devcontainer_path=.devcontainer%2Fdevcontainer.json&geo=UsEast).
Make sure you are using the `TTMR dev container` configuration (and
though not necessary, I recommend using the 4-core Machine type).

This will take a while to build, but once it's done, you'll be dropped
into a home directory, from which you can create agda files and use
`open import CS400-Lib` as above.

This should not be a long term solution, but if you finding yourself
using this codespace frequently, you should run

```
git -C /workspaces/CS400-Lib/ pull
```

any time you open the codespace to make sure you're working with the
most up-to-date version of the library.
