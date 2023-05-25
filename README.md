# Formalising solid abelian groups

The goal of this repository is to formalise the definition of solid abelian groups and theorems about them from Lectures V and VI in the lecture notes [Condensed.pdf](https://people.mpim-bonn.mpg.de/scholze/Condensed.pdf) by Peter Scholze.

It is forked from the Liquid Tensor Experiment (see https://github.com/leanprover-community/lean-liquid.git and more about it below), and builds on lots of the basic definitions and results about condensed sets and abelian groups formalised there.

## Getting and browsing the repository

* Install a Lean development environment following the
  [installation instructions](https://leanprover-community.github.io/get_started.html#regular-install).
* To download and open a copy of the repository
  by executing the following command in a terminal:
  ```
  leanproject get dagurtomas/lean-solid
  cd lean-solid
  ./scripts/fetch_olean_cache.sh
  code lean-solid
  ```
* Everything added by me for the project about solid abelian groups so far is contained in the directory src/solid/
