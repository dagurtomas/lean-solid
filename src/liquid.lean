import Mbar.complex

/-!
# Liquid Tensor Experiment

This file is the entry point for this project.
The first goal of the Liquid Tensor Experiment
is to formalize a theorem by Clausen and Scholze stated below,
namely a mix of Theorem 9.4 and Theorem 9.5 of
[Analytic]: http://www.math.uni-bonn.de/people/scholze/Analytic.pdf

**How to browse this project? See `README.md` in the root of the repository.**

We will now state the main theorem.

First we need to fix a package of data corresponding to the Breen--Deligne resolution.
If you don't know the Breen--Deligne resolution, don't worry,
we'll explain more about how to find out more about it below.
Once we have fixed this data, we can state the theorem.
-/

open_locale nnreal -- enable the notation `ℝ≥0` for the nonnegative real numbers.

variables (BD : breen_deligne.package)
variables (c' : ℕ → ℝ≥0)  -- implicit constants, chosen once and for all
                          -- see the sentence after that statement of Thm 9.5

/-- A mix of Theorems 9.4 and 9.5 in [Analytic] -/
theorem first_target [BD.suitable c']
  (r r' : ℝ≥0) [fact (0 < r)] [fact (0 < r')] [fact (r < r')] [fact (r' ≤ 1)] :
  ∀ m : ℕ,
  ∃ (k K : ℝ≥0) [fact (1 ≤ k)],
  ∃ c₀ : ℝ≥0,
  ∀ (S : Type) [fintype S],
  ∀ (V : NormedGroup) [normed_with_aut r V],
    ​(Mbar_system V S r r' BD c').is_bdd_exact_for_bdd_degree_above_idx k K m c₀ :=
admit

/-!
## On the statement

Most of the theorem should be fairly readable.
We will now briefly explain some of the more peculiar syntax.

* `[BD.suitable c']` assumes that the nonnegative reals `c' i` satisfy some suitable conditions
  with respect to the package of Breen--Deligne data `BD`.
* `[fact (0 < r)]` records the "fact" `0 < r` as an assumption to whatever comes later.
* `(S : Type) [fintype S]` is Lean's way of saying "`S` is a finite set".
  See also the "Brief note on type theory" in `README.md`.
* `[normed_with_aut r V]` adds the assumption that `V` is endowed with an automorphism `T`
  that scales elements `v` of `V` by the positive scalar `r`: `∥T(v)∥ = r * ∥v∥`.
* `Mbar_system` is the system of complexes of normed abelian groups
  occuring in Theorems 9.4/9.5 of [Analytic].
* `is_bdd_exact_for_bdd_degree_above_idx` is the assertion that a system of complexes
  of normed abelian groups satisfies a suitable exactness criterion of being
  `≤ k`-exact in degrees `≤ m` for `c ≥ c₀` (where `c` is an index to the system of complexes).
* `sorry` tells Lean to accept this theorem without proof. We are working hard on removing it!
-/
