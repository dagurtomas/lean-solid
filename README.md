# Formalising discrete condensed sets

This repository is a snapshot of my formalisation of an equivalence of three different definitions of discrete condensed sets.

It is forked from the Liquid Tensor Experiment (LTE, see https://github.com/leanprover-community/lean-liquid.git), and builds on lots of the basic definitions and results about condensed sets formalised there.

The main results are in the file `src/discrete/discrete_comparison.lean` along with a description.

## Getting and browsing the repository

* Install a Lean development environment following the
  [installation instructions](https://leanprover-community.github.io/get_started.html#regular-install).
* To download and open a copy of the repository, execute the following command in a terminal:
  ```
  leanproject get dagurtomas/lean-solid
  cd lean-solid
  git checkout discrete
  ./scripts/get-cache.sh
  ./scripts/fetch_olean_cache.sh
  lean --make src/discrete/discrete_comparison.lean
  ```
  I'm not sure the scripts `get-cache` and `fetch_olean_cache` are actually doing anything, but they are supposed to get oleans for LTE. If they don't work, the last command will take a really long time, but it is necessary to build the file with the main results and all its dependencies. This should allow to browse the project in VS Code with good interactive speed.
* All code written by me is contained in the directory `src/discrete/`. Everything else is unchanged from LTE.
