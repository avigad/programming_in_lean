
[![Build
Status](https://travis-ci.org/avigad/programming_in_lean.svg?branch=master)](https://travis-ci.org/avigad/programming_in_lean)

Programming in Lean
-------------------

Built using Sphinx and restructured text.

# How to build

The build requires python 3 (install `python3-venv` on ubuntu).

```
make install-deps
make html
make latexpdf
```

The call to `make install-deps` is only required the first time, and only if you want to use the bundled version of Sphinx and Pygments with improved syntax highlighting for Lean.

# How to test the Lean code snippets

```
make leantest
```

# How to deploy

```
./deploy.sh avigad programming_in_lean
```
