import data.polynomial.degree.lemmas
import algebra.module.ordered
import algebra.regular
--import ring_theory.noetherian
import toric_2021_02_19.span_as_sum
import linear_algebra.basic
import linear_algebra.finite_dimensional
import algebra.big_operators.basic
--import analysis.normed_space.inner_product

/-- In the intended application, these are the players:
* `R₀ = ℕ`;
* `R = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

-- the example is here since otherwise Lean complains that `section does not accept doc string`
example : true := trivial

open_locale big_operators classical

-- Here we make the general statements that require few assumptions on the various types.
section abstract

variables (R₀ R M : Type*)

namespace submodule


section comm_semiring

variables {R₀} {M}

variables [comm_semiring R₀] [add_comm_monoid M] [semimodule R₀ M]

/-- This definition does not assume that `R₀` injects into `R`.  If the map `R₀ → R` has a
non-trivial kernel, this might not be the definition you think. -/
def saturated (s : submodule R₀ M) : Prop :=
∀ (r : R₀) (hr : is_regular r) (m : M), r • m ∈ s → m ∈ s

/--  The saturation of a submodule `s ⊆ M` is the submodule obtained from `s` by adding all
elements of `M` that admit a multiple by a regular element of `R₀` lying in `s`. -/
def saturation (s : submodule R₀ M) : submodule R₀ M :=
{ carrier := { m : M | ∃ (r : R₀), is_regular r ∧ r • m ∈ s },
  zero_mem' := ⟨1, is_regular_one, by { rw smul_zero, exact s.zero_mem }⟩,
  add_mem' := begin
    rintros a b ⟨q, hqreg, hqa⟩ ⟨r, hrreg, hrb⟩,
    refine ⟨q * r, is_regular_mul_iff.mpr ⟨hqreg, hrreg⟩, _⟩,
    rw [smul_add],
    refine s.add_mem _ _,
    { rw [mul_comm, mul_smul],
      exact s.smul_mem _ hqa },
    { rw mul_smul,
      exact s.smul_mem _ hrb },
  end,
  smul_mem' := λ c m ⟨r, hrreg, hrm⟩,
    ⟨r, hrreg, by {rw smul_algebra_smul_comm, exact s.smul_mem _ hrm}⟩ }

/--  The saturation of `s` contains `s`. -/
lemma le_saturation (s : submodule R₀ M) : s ≤ saturation s :=
λ m hm, ⟨1, is_regular_one, by rwa one_smul⟩

/-- The set `S` is contained in the saturation of the submodule spanned by `S` itself. -/
lemma set_subset_saturation  {S : set M} :
  S ⊆ (submodule.saturation (submodule.span R₀ S)) :=
set.subset.trans (submodule.subset_span : S ⊆ submodule.span R₀ S)
  (submodule.le_saturation (submodule.span R₀ S))

/-
TODO: develop the API for the definitions
`is_cyclic`, `pointed`, `has_extremal_ray`, `extremal_rays`.
Prove(?) `sup_extremal_rays`, if it is true, even in the test case.
-/
/--  A cyclic submodule is a submodule generated by a single element. -/
def is_cyclic (s : submodule R₀ M) : Prop := ∃ m : M, (R₀ ∙ m) = s

variables (R₀ M)

/--  A semimodule is cyclic if its top submodule is generated by a single element. -/
def semimodule.is_cyclic : Prop := is_cyclic (⊤ : submodule R₀ M)

variables {R₀ M}

/--  The zero submodule is cyclic. -/
lemma is_cyclic_bot : is_cyclic (⊥ : submodule R₀ M) :=
⟨_, span_zero_singleton⟩

/--  An extremal ray of a submodule `s` is a cyclic submodule `r` with the property that if two
elements of `s` have sum contained in `r`, then the elements themselves are contained in `r`.
These are the "edges" of the cone. -/
structure has_extremal_ray (s r : submodule R₀ M) : Prop :=
(incl : r ≤ s)
(is_cyclic : r.is_cyclic)
(mem_of_sum_mem : ∀ {x y : M}, x ∈ s → y ∈ s → x + y ∈ r → (x ∈ r ∧ y ∈ r))

/--  The set of all extremal rays of a submodule.  Hopefully, these are a good replacement for
generators, in the case in which the cone is `pointed`. -/
def extremal_rays (s : submodule R₀ M) : set (submodule R₀ M) :=
{ r | s.has_extremal_ray r }

/-  The `is_scalar_tower R₀ R M` assumption is not needed to state `pointed`, but will likely play
a role in the proof of `sup_extremal_rays`. -/
variables [semiring R] [semimodule R M]

/--  A pointed submodule is a submodule `s` for which there exists a linear function `φ : M → R`,
such that the hyperplane `ker φ` intersects `s` in just the origin.
Alternatively, the submodule `s` contains no `R` linear subspace. -/
def pointed (s : submodule R₀ M) : Prop := ∃ φ : M →ₗ[R] R, ∀ x : M, x ∈ s → φ x = 0 → x = 0

/--  A pointed subset is a submodule `s` for which there exists a linear function `φ : M → R`,
such that the hyperplane `ker φ` intersects `s` in just the origin. -/
-- We may not need this definition.
def pointed_subset (s : set M) : Prop := ∃ φ : M →ₗ[R] R, ∀ x : M, x ∈ s → φ x = 0 → x = 0

variables [algebra R₀ R] [is_scalar_tower R₀ R M]

/--  A submodule of a pointed submodule is pointed. -/
lemma pointed_of_submodule {s t : submodule R₀ M} (st : s ≤ t) (pt : pointed R t) : pointed R s :=
begin
  cases pt with l hl,
  exact ⟨l, λ m ms m0, hl m (st ms) m0⟩,
end

/-- Any `R₀`-submodule of `R` is pointed, since the identity function is a "separating hyperplane".
This should not happen if the module is not cyclic for `R`. -/
lemma pointed_of_sub_R {s : submodule R₀ R} : pointed R s :=
⟨1, λ _ _ h, h⟩

/-- The zero submodule of any `R`-module `M` is pointed, since the zero function is a
"separating hyperplane". -/
lemma pointed_of_bot : pointed R (⊥ : submodule R₀ M) :=
⟨0, λ x xb h, xb⟩

lemma fd {ι : Type*} (v : ι → R) (ind : linear_independent R v) :
  pointed R (submodule.span R₀ (v '' set.univ)) :=
pointed_of_sub_R R

/--  Hopefully, this lemma will be easy to prove. -/
lemma sup_extremal_rays {s : submodule R₀ M} (sp : s.pointed R) :
  (⨆ r ∈ s.extremal_rays, r) = s :=
begin
  refine le_antisymm (bsupr_le $ λ i hi, hi.1) _,
  intros m ms t ht,
  rcases ht with ⟨y, rfl⟩,
  simp only [forall_apply_eq_imp_iff', supr_le_iff, set.mem_range, mem_coe, set.mem_Inter,
    set.mem_set_of_eq, exists_imp_distrib],
  intros a,
  rcases sp with ⟨el, lo⟩,
  sorry
end

end comm_semiring

section integral_domain

variables [integral_domain R₀] [add_comm_monoid M] [semimodule R₀ M]

/--  A sanity check that our definitions imply something not completely trivial
in an easy situation! -/
lemma sat {s t : submodule R₀ M}
  (s0 : s ≠ ⊥) (ss : s.saturated) (st : s ≤ t) (ct : is_cyclic t) :
  s = t :=
begin
  refine le_antisymm st _,
  rcases ct with ⟨t0, rfl⟩,
  refine (span_singleton_le_iff_mem t0 s).mpr _,
  rcases (submodule.ne_bot_iff _).mp s0 with ⟨m, hm, m0⟩,
  rcases (le_span_singleton_iff.mp st) _ hm with ⟨c, rfl⟩,
  refine ss _ (is_regular_of_ne_zero _) _ hm,
  exact λ h, m0 (by rw [h, zero_smul]),
end

end integral_domain

end submodule


section pairing

variables [comm_semiring R₀] [comm_semiring R] [algebra R₀ R]
  [add_comm_monoid M] [semimodule R₀ M] [semimodule R M] [is_scalar_tower R₀ R M]

variables (N P : Type*)
  [add_comm_monoid N] [semimodule R₀ N] [semimodule R N] [is_scalar_tower R₀ R N]
  [add_comm_monoid P] [semimodule R₀ P] [semimodule R P] [is_scalar_tower R₀ R P]
  (P₀ : submodule R₀ P)

/-- An R-pairing on the R-modules M, N, P is an R-linear map M -> Hom_R(N,P). -/
@[derive has_coe_to_fun] def pairing := M →ₗ[R] N →ₗ[R] P

namespace pairing

instance inhabited : inhabited (pairing R M N P) :=
⟨{to_fun := 0, map_add' := by simp, map_smul' := by simp }⟩

variables {R₀ R M N P}

/--  Given a pairing between the `R`-modules `M` and `N`, we obtain a pairing between `N` and `M`
by exchanging the factors. -/
def flip : pairing R M N P → pairing R N M P := linear_map.flip

variables (f : pairing R M N P)

/-- For a given pairing `<_, _> : M × N → P` and an element `m ∈ M`, `mul_left` is the linear map
`n ↦ <m, n>`.
-- Left multiplication may not be needed.
def mul_left (m : M) : N →ₗ[R] P :=
{ to_fun := λ n, f m n,
  map_add' := λ x y, by simp only [linear_map.add_apply, linear_map.map_add],
  map_smul' := λ x y, by simp only [linear_map.smul_apply, linear_map.map_smul] }

/-- For a given pairing `<_, _> : M × N → P` and an element `n ∈ N`, `mul_right` is the linear map
`m ↦ <m, n>`. -/
def mul_right (n : N) : M →ₗ[R] P :=
{ to_fun := λ m, f m n,
  map_add' := λ x y, by simp only [linear_map.add_apply, linear_map.map_add],
  map_smul' := λ x y, by simp only [linear_map.smul_apply, linear_map.map_smul] }
-/

example {n : N} : f.flip n = f.flip n := rfl

/--  A pairing `M × N → P` is `left_nondegenerate` if `0 ∈ N` is the only element of `N` pairing
to `0` with all elements of `M`. -/
def left_nondegenerate : Prop := ∀ n : N, (∀ m : M, f m n = 0) → n = 0

/--  A pairing `M × N → P` is `right_nondegenerate` if `0 ∈ M` is the only element of `M` pairing
to `0` with all elements of `N`. -/
def right_nondegenerate : Prop := ∀ m : M, (∀ n : N, f m n = 0) → m = 0

/--  A pairing `M × N → P` is `perfect` if it is left and right nondegenerate. -/
def perfect : Prop := left_nondegenerate f ∧ right_nondegenerate f

/--  For a subset `s ⊆ M`, the `dual_set s` is the submodule consisting of all elements of `N`
that have "positive pairing with all the elements of `s`.  "Positive" means that it lies in the
`R₀`-submodule `P₀` of `P`. -/
def dual_set (s : set M) : submodule R₀ N :=
{ carrier := { n : N | ∀ m ∈ s, f m n ∈ P₀ },
  zero_mem' := λ m hm, by simp only [linear_map.map_zero, P₀.zero_mem],
  add_mem' := λ n1 n2 hn1 hn2 m hm, begin
    rw linear_map.map_add,
    exact P₀.add_mem (hn1 m hm) (hn2 m hm),
  end,
  smul_mem' := λ r n h m hms, by simp [h m hms, P₀.smul_mem] }

lemma mem_dual_set (s : set M) (n : N) :
  n ∈ f.dual_set P₀ s ↔ ∀ m ∈ s, f m n ∈ P₀ := iff.rfl

section saturated

variables {P₀} (hP₀ : P₀.saturated)
include hP₀

lemma smul_regular_iff {r : R₀} (hr : is_regular r) (p : P) :
  r • p ∈ P₀ ↔ p ∈ P₀ :=
⟨hP₀ _ hr _, P₀.smul_mem _⟩

lemma dual_set_saturated (s : set M) (hP₀ : P₀.saturated) :
  (f.dual_set P₀ s).saturated :=
λ r hr n hn m hm, by simpa [smul_regular_iff hP₀ hr] using hn m hm

end saturated

-- this instance can be removed when #6331 is merged.
instance : is_scalar_tower R₀ R (N →ₗ[R] P) :=
{ smul_assoc := λ _ _ _, linear_map.ext $ by simp }

variable {P₀}

lemma dual_subset {s t : set M} (st : s ⊆ t) : f.dual_set P₀ t ≤ f.dual_set P₀ s :=
λ n hn m hm, hn m (st hm)

lemma mem_span_dual_set (s : set M) :
  f.dual_set P₀ (submodule.span R₀ s) = f.dual_set P₀ s :=
begin
  refine (dual_subset f submodule.subset_span).antisymm _,
  { refine λ n hn m hm, submodule.span_induction hm hn _ _ _,
    { simp only [linear_map.map_zero, submodule.zero_mem, linear_map.zero_apply] },
    { exact λ x y hx hy, by simp [P₀.add_mem hx hy] },
    { exact λ r m hm, by simp [P₀.smul_mem _ hm] } }
end

lemma subset_dual_dual {s : set M} : s ⊆ f.flip.dual_set P₀ (f.dual_set P₀ s) :=
λ m hm _ hm', hm' m hm

lemma subset_dual_set_of_subset_dual_set {S : set M} {T : set N}
  (ST : S ⊆ f.flip.dual_set P₀ T) :
  T ⊆ f.dual_set P₀ S :=
λ n hn m hm, ST hm _ hn

lemma le_dual_set_of_le_dual_set {S : submodule R₀ M} {T : submodule R₀ N}
  (ST : S ≤ f.flip.dual_set P₀ T) :
  T ≤ f.dual_set P₀ S :=
subset_dual_set_of_subset_dual_set _ ST

lemma dual_set_closure_eq {s : set M} :
  f.dual_set P₀ (submodule.span R₀ s) = f.dual_set P₀ s :=
begin
  refine (dual_subset _ submodule.subset_span).antisymm _,
  refine λ n hn m hm, submodule.span_induction hm hn _ _ _,
  { simp only [linear_map.map_zero, linear_map.zero_apply, P₀.zero_mem] },
  { exact λ x y hx hy, by simp only [linear_map.add_apply, linear_map.map_add, P₀.add_mem hx hy] },
  { exact λ r m hmn, by simp [P₀.smul_mem r hmn] },
end

lemma dual_eq_dual_saturation {S : set M} (hP₀ : P₀.saturated) :
  f.dual_set P₀ S = f.dual_set P₀ ((submodule.span R₀ S).saturation) :=
begin
  refine le_antisymm _ (dual_subset _ (submodule.set_subset_saturation)),
  rintro n hn m ⟨r, hr_reg, hrm⟩,
  refine (smul_regular_iff hP₀ hr_reg _).mp _,
  rw [← mem_span_dual_set, mem_dual_set] at hn,
  simpa using hn (r • m) hrm
end

/- flip the inequalities assuming saturatedness -/
lemma le_dual_set_of_le_dual_set_satu {S : submodule R₀ M} {T : submodule R₀ N}
  (ST : S ≤ f.flip.dual_set P₀ T) :
  T ≤ f.dual_set P₀ S :=
subset_dual_set_of_subset_dual_set _ ST

lemma subset_dual_set_iff {S : set M} {T : set N} :
  S ⊆ f.flip.dual_set P₀ T ↔ T ⊆ f.dual_set P₀ S :=
⟨subset_dual_set_of_subset_dual_set f, subset_dual_set_of_subset_dual_set f.flip⟩

lemma le_dual_set_iff {S : submodule R₀ M} {T : submodule R₀ N} :
  S ≤ f.flip.dual_set P₀ T ↔ T ≤ f.dual_set P₀ S :=
subset_dual_set_iff _

/- This lemma is a weakining of `dual_dual_of_saturated`.
It has the advantage that we can prove it in this level of generality!  ;) -/
lemma dual_dual_dual (S : set M) :
  f.dual_set P₀ (f.flip.dual_set P₀ (f.dual_set P₀ S)) = f.dual_set P₀ S :=
le_antisymm (λ m hm n hn, hm _ ((subset_dual_set_iff f).mpr set.subset.rfl hn))
  (λ m hm n hn, hn m hm)

variable (P₀)

/--  The rays of the dual of the set `s` are the duals of the subsets of `s` that happen to be
cyclic. -/
def dual_set_rays (s : set M) : set (submodule R₀ N) :=
{ r | r.is_cyclic ∧ ∃ s' ⊆ s, r = f.dual_set P₀ s' }

/-  We may need extra assumptions for this. -/
/--  The link between the rays of the dual and the extremal rays of the dual should be the
crucial finiteness step: if `s` is finite, there are only finitely many `dual_set_rays`, since
there are at most as many as there are subsets of `s`.  If the extremal rays generate
dual of `s`, then we are in a good position to prove Gordan's lemma! -/
lemma dual_set_rays_eq_extremal_rays (s : set M) :
  f.dual_set_rays P₀ s = (f.dual_set P₀ s).extremal_rays :=
sorry

lemma dual_set_pointed (s : set M) (hs : (submodule.span R₀ s).saturation) :
  (f.dual_set P₀ s).pointed R := sorry

--def dual_set_generators (s : set M) : set N := { n : N | }

--lemma dual_fg_of_finite {s : set M} (fs : s.finite) : (f.dual_set P₀ s).fg :=
--sorry

/-
/--  The behaviour of `dual_set` under smultiplication. -/
lemma dual_smul {s : set M} {r : R₀} {m : M} :
  f.dual_set P₀ (s.insert m) ≤ f.dual_set P₀ (s.insert (r • m)) :=
begin
  intros n hn m hm,
  rcases hm with rfl | hm,
  { rw [linear_map.map_smul_of_tower, linear_map.smul_apply],
    exact P₀.smul_mem r (hn m (s.mem_insert m)) },
  { exact hn _ (set.mem_insert_iff.mpr (or.inr hm)) }
end
-/

lemma dual_dual_of_saturated {S : submodule R₀ M} (Ss : S.saturated) :
  f.flip.dual_set P₀ (f.dual_set P₀ S) = S :=
begin
  refine le_antisymm _ (subset_dual_dual f),
  intros m hm,
--  rw mem_dual_set at hm,
  change ∀ (n : N), n ∈ (dual_set P₀ f ↑S) → f m n ∈ P₀ at hm,
  simp_rw mem_dual_set at hm,
  -- is this true? I (KMB) don't know and the guru (Damiano) has left!
  -- oh wait, no way is this true, we need some nondegeneracy condition
  -- on f, it's surely not true if f is just the zero map.
  -- I (DT) think that you are right, Kevin.  We may now start to make assumptions
  -- that are more specific to our situation.
  sorry,
end

/-
def to_linear_dual (f : pairing R M N R) : N →ₗ[R] (M →ₗ[R] R) :=
{ to_fun := λ n,
  { to_fun := λ m, f m n,
    map_add' := λ x y, by simp only [linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x y, by simp only [linear_map.smul_apply, linear_map.map_smul] },
  map_add' := λ x y, by simpa only [linear_map.map_add],
  map_smul' := λ r n, by simpa only [algebra.id.smul_eq_mul, linear_map.map_smul] }

lemma to_ld (f : pairing R M N R) (n : N) : to_linear_dual f n = mul_right f n := rfl

-- this lemma requires some extra hypotheses: at the very least, some finite-generation
-- condition: the "standard" scalar product on `ℝ ^ (⊕ ℕ)` has power-series as its dual
-- but is non-degenerate.
/-- A pairing `f` between two `R`-modules `M` and `N` with values in `R` is perfect if every
linear function `l : M →ₗ[R] R` is represented as -/
lemma left_nondegenerate_exists {f : pairing R M N R} (r : right_nondegenerate f) :
  ∀ l : M →ₗ[R] R, ∃ n : N, ∀ m : M, l m = f m n :=
begin
  intros l,
  sorry,
end
-/


end pairing

end pairing

end abstract

-- ending the section to clear out all the assumptions

section add_group

variables {R₀ R : Type*} [comm_ring R₀] [comm_ring R] [algebra R₀ R]
variables {M : Type*} [add_comm_group M] [module R₀ M] [module R M] [is_scalar_tower R₀ R M]
--variables {M N : Type*} [add_comm_monoid M] --[semimodule ℕ M] [semimodule ℤ M]
  --[algebra ℕ ℤ] [is_scalar_tower ℕ ℤ M]

--variables {P : Type*}
--  [add_comm_monoid N] --[semimodule ℕ N] [semimodule ℤ N] --[is_scalar_tower ℕ ℤ N]
--  [add_comm_monoid P] --[semimodule ℕ P] [semimodule ℤ P] --[is_scalar_tower ℕ ℤ P]
--  (P₀ : submodule ℕ P)


open pairing submodule

/-
lemma pointed_of_is_basis {ι : Type*} (v : ι → M) (bv : is_basis R v) :
  pointed R (submodule.span R₀ (set.range v)) :=
begin
  obtain ⟨l, hl⟩ : ∃ l : M →ₗ[R] R, ∀ i : ι, l (v i) = 1 :=
    ⟨bv.constr (λ _, 1), λ i, constr_basis bv⟩,
  refine Exists.intro
  { to_fun := ⇑l,
    map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
    map_smul' := λ m x, by
    { rw [algebra.id.smul_eq_mul, linear_map.map_smul],
      refine congr _ rfl,
      exact funext (λ y, by simp only [has_scalar.smul, gsmul_int_int]) } } _,
  rintros m hm (m0 : l m = 0),
  obtain ⟨c, csup, rfl⟩ := span_as_sum hm,
  simp_rw [linear_map.map_sum] at m0,--, linear_map.map_smul_of_tower] at m0,
  have : linear_map.compatible_smul M R R₀ R := sorry,
  conv_lhs at m0 {
    apply_congr, skip, rw @linear_map.map_smul_of_tower _ _ _ _ _ _ _ _ _ _ _ this l, skip },
  have : ∑ (i : M) in c.support, (c i • l i : R) = ∑ (i : M) in c.support, (c i : R),
  { refine finset.sum_congr rfl (λ x hx, _),
    rcases set.mem_range.mp (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup) with ⟨i, rfl⟩,
    simp [hl _, (•)], },
  rw this at m0,
  have : ∑ (i : M) in c.support, (0 : M) = 0,
  { rw finset.sum_eq_zero,
    simp only [eq_self_iff_true, forall_true_iff] },
  rw ← this,
  refine finset.sum_congr rfl (λ x hx, _),
  rw finset.sum_eq_zero_iff_of_nonneg at m0,
  { rw [int.coe_nat_eq_zero.mp (m0 x hx), zero_smul] },
  { exact λ x hx, int.coe_nat_nonneg _ }
end
-/

end add_group


/- In the intended application, these are the players:
* `R₀ = ℕ`;
* `R = ℤ`;
* `M`and `N` are free finitely generated `ℤ`-modules that are dual to each other;
* `P = ℤ` is the target of the natural pairing `M ⊗ N → ℤ`.
-/

section concrete

namespace pairing

open pairing submodule

variables {M : Type*} [add_comm_group M] --[semimodule ℕ M]
-- [semimodule ℤ M]
--variables {M N : Type*} [add_comm_monoid M] --[semimodule ℕ M] [semimodule ℤ M]
  --[algebra ℕ ℤ] [is_scalar_tower ℕ ℤ M]

--variables {P : Type*}
--  [add_comm_monoid N] --[semimodule ℕ N] [semimodule ℤ N] --[is_scalar_tower ℕ ℤ N]
--  [add_comm_monoid P] --[semimodule ℕ P] [semimodule ℤ P] --[is_scalar_tower ℕ ℤ P]
--  (P₀ : submodule ℕ P)



lemma pointed_of_is_basis_is_inj {ι : Type*} {N Z : Type*} [ordered_comm_ring Z]
  [comm_semiring N] [semimodule N M] [module Z M] [algebra N Z] [is_scalar_tower N Z M]
  (hNZ : is_inj_nonneg (algebra_map N Z)) (v : ι → M) (bv : is_basis Z v) :
  pointed Z (submodule.span N (set.range v)) :=
begin
  obtain ⟨l, hl⟩ : ∃ l : M →ₗ[Z] Z, ∀ i : ι, l (v i) = 1 :=
    ⟨bv.constr (λ _, 1), λ i, constr_basis bv⟩,
  refine Exists.intro
  { to_fun := ⇑l,
    map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
    map_smul' := λ m x, by
    { rw [algebra.id.smul_eq_mul, linear_map.map_smul],
      refine congr _ rfl,
      exact funext (λ (y : Z), by simp only [has_scalar.smul, gsmul_int_int]) } } _,
  rintros m hm (m0 : l m = 0),
  obtain ⟨c, csup, rfl⟩ := mem_span_set.mp hm,
  change l (∑ i in c.support, c i • i) = 0 at m0,
  simp_rw [linear_map.map_sum, linear_map.map_smul_of_tower] at m0,
  have : ∑ (i : M) in c.support, c i • l i = ∑ (i : M) in c.support, c i • (1 : Z),
  { refine finset.sum_congr rfl (λ x hx, _),
    rcases set.mem_range.mp (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup) with ⟨i, rfl⟩,
    simp [hl _, (•)], },
  rw this at m0,
  have : ∑ (i : M) in c.support, (0 : M) = 0,
  { rw finset.sum_eq_zero,
    simp only [eq_self_iff_true, forall_true_iff] },
  rw ← this,
  refine finset.sum_congr rfl (λ x hx, _),
  rw finset.sum_eq_zero_iff_of_nonneg at m0,
  { dsimp,
    convert zero_smul N _,
    obtain F := (m0 x hx),
    rw ← algebra.algebra_map_eq_smul_one at F,
    refine hNZ.1 _,
    rwa [ring_hom.map_zero] },
  { refine λ m hm, _,
    rw ← algebra.algebra_map_eq_smul_one,
    exact hNZ.2 (c m) }
end

lemma pointed_of_is_basis {ι : Type*} (v : ι → M) (bv : is_basis ℤ v) :
  pointed ℤ (submodule.span ℕ (set.range v)) :=
pointed_of_is_basis_is_inj (is_inj_nonneg.nat ℤ) v bv

--instance {R : Type*} [ordered_comm_ring R] : ordered_comm_semiring (pR R) := by apply_instance

lemma pointed_pR {R : Type*} [ordered_comm_ring R] [module R M] [semimodule (pR R) M]
  [is_scalar_tower (pR R) R M] {ι : Type*} (v : ι → M) (bv : is_basis R v) :
  pointed R (submodule.span (pR R) (set.range v)) :=
begin
  apply pointed_of_is_basis_is_inj _ v bv,
  apply_instance,
  rotate,
  { exact is_inj_nonneg.pR_ocr R },
  sorry,
/-
  convert _inst_5 using 5,

  congr,

  {
    fconstructor,
    --convert {smul_assoc := λ x y z, smul_assoc x y z},
    intros x y z,
    convert smul_assoc x y z,
    sorry,
    --convert _inst_5,
  },
-/
end



lemma speed_up_1 {M R : Type*} [add_comm_group M] [ordered_comm_ring R] [module R M]
  [semimodule ↥(pR R) M]
  (l : M →ₗ[R] R)
  (c : M →₀ ↥(pR R)) :
  l (c.sum (λ (mi : M) (r : ↥(pR R)), r • mi)) = l (∑ (i : M) in c.support, c i • i) := rfl

lemma speed_up_2 {M R : Type*} [add_comm_group M] [ordered_comm_ring R] [semimodule ↥(pR R) M]
  {x : M}
  {c : M →₀ ↥(pR R)}
  (hx : x ∈ c.support)
  (m0 : ∀ (x : M), x ∈ c.support → ((c x) : R) = 0) :
  (λ (mi : M) (r : (pR R)), r • mi) x (c x) = 0 :=
begin
  convert zero_smul (pR R) _,
  exact subtype.coe_injective (m0 x hx)
end

/--  Trying to prove this lemma above, using the new is_inj_nonneg
lemma pointed_pR {R : Type*} [ordered_comm_ring R] [module R M] [semimodule (pR R) M]
  [is_scalar_tower (pR R) R M] {ι : Type*} (v : ι → M) (bv : is_basis R v) :
  pointed R (submodule.span (pR R) (set.range v)) :=
begin
  obtain ⟨l, hl⟩ : ∃ l : M →ₗ[R] R, ∀ i : ι, l (v i) = 1 :=
    ⟨bv.constr (λ _, 1), λ i, constr_basis bv⟩,
  refine Exists.intro
  { to_fun := ⇑l,
    map_add' := by simp only [forall_const, eq_self_iff_true, linear_map.map_add],
    map_smul' := λ m x, by
    { rw [algebra.id.smul_eq_mul, linear_map.map_smul],
      refine congr _ rfl,
      exact funext (λ (y : R), by simp only [has_scalar.smul, gsmul_int_int]) } } _,
  rintros m hm (m0 : l m = 0),
  obtain ⟨c, csup, rfl⟩ := mem_span_set.mp hm,
  rw speed_up_1 at m0,
--  change l (∑ i in c.support, c i • i) = 0 at m0, --takes some time
  --simp_rw [linear_map.map_sum, linear_map.map_smul_of_tower] at m0,
  have : ∑ (i : M) in c.support, c i • l i = ∑ (i : M) in c.support, c i,
  { refine finset.sum_congr rfl (λ x hx, _),
    rcases set.mem_range.mp (set.mem_of_mem_of_subset (finset.mem_coe.mpr hx) csup) with ⟨i, rfl⟩,
    simp only [hl _, mul_one, algebra.id.smul_eq_mul],

    simp_rw ← algebra.algebra_map_eq_smul_one, },
  rw this at m0,
  have : ∑ (i : M) in c.support, (0 : M) = 0,
  { rw finset.sum_eq_zero,
    simp only [eq_self_iff_true, forall_true_iff] },
  rw ← this,
  refine finset.sum_congr rfl (λ x hx, speed_up_2 hx _),
  rwa finset.sum_eq_zero_iff_of_nonneg at m0,
  exact λ x hx, mem_pR_nonneg (c x)
end
 -/

lemma of_non_deg {ι : Type*} {f : pairing ℤ M M ℤ} {v : ι → M}
  (nd : perfect f) (sp : submodule.span ℤ (v '' set.univ)) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
--  tidy?,
  sorry
end

end pairing

end concrete
/- This might be junk
def standard_pairing_Z : pairing ℤ ℤ ℤ ℤ :=
{ to_fun := λ z,
  { to_fun := λ n, z * n,
    map_add' := mul_add z,
    map_smul' := λ m n, algebra.mul_smul_comm m z n },
  map_add' := λ x y, by simpa [add_mul],
  map_smul' := λ x y, by simpa only [algebra.smul_mul_assoc] }

lemma nond_Z : right_nondegenerate standard_pairing_Z :=
λ m hm, eq.trans (mul_one m).symm (hm 1)


def standard_pairing_Z_sq : pairing ℤ (ℤ × ℤ) (ℤ × ℤ) ℤ :=
{ to_fun := λ z,
  { to_fun := λ n, z.1 * n.1 + z.2 * n.2,
    map_add' := λ x y, by { rw [prod.snd_add, prod.fst_add], ring },
    map_smul' := λ x y,
      by simp only [smul_add, algebra.mul_smul_comm, prod.smul_snd, prod.smul_fst] },
  map_add' := λ x y, begin
    congr,
    ext,
    dsimp,
    rw [prod.snd_add, prod.fst_add, add_mul],
    ring,
  end,
  map_smul' := λ x y, begin
    congr,
    simp only [smul_add, prod.smul_snd, linear_map.coe_mk, prod.smul_fst, algebra.smul_mul_assoc],
  end }

lemma nond_Z_sq : right_nondegenerate standard_pairing_Z_sq :=
begin
  refine λ  m hm, prod.ext _ _,
  { obtain (F : m.fst * (1 : ℤ) + m.snd * (0 : ℤ) = 0) := hm (1, 0),
    simpa using F },
  { obtain (F : m.fst * (0 : ℤ) + m.snd * (1 : ℤ) = 0) := hm (0, 1),
    simpa using F }
end

lemma fd (v : fin 2 → ℤ × ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  refine ⟨_, _⟩,
  convert mul_right standard_pairing_Z_sq (v 0 + v 1),
--  convert @mul_right ℤ (ℤ × ℤ) _ _ _ (ℤ × ℤ) ℤ _ _ _ _ standard_pairing_Z_sq ((1, 1) : ℤ × ℤ),
  intros m hm m0,
  induction m with m1 m2,
  congr,

--  tidy?,

  refine (mul_right standard_pairing_Z_sq ((1, 1) : ℤ × ℤ) : ℤ × ℤ →ₗ[ℤ] ℤ),
--  refine ((λ m : ℤ × ℤ, standard_pairing_Z_sq m (1,1)) : ℤ × ℤ →ₗ[ℤ] ℤ),
  refine
  { to_fun := λ m, standard_pairing_Z_sq m (1,1),
    map_add' :=
      by simp only [forall_const, eq_self_iff_true, linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x m, begin
      rw [standard_pairing_Z_sq, algebra.id.smul_eq_mul, linear_map.map_smul, linear_map.coe_mk, linear_map.coe_mk],
      simp only [has_scalar.smul, gsmul_int_int, linear_map.coe_mk],
  end },
  simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { intros ᾰ, cases ᾰ }, work_on_goal 1 { intros x y, cases y, cases x, dsimp at * }, work_on_goal 2 { intros m x, cases x, dsimp at * } }, work_on_goal 3 { intros x ᾰ ᾰ_1, cases x, dsimp at *, simp at *, simp at *, fsplit, work_on_goal 0 { assumption } },
  { refl },
  { simp [(•)] },

  convert pointed_of_sub_R M,
end

#exit

lemma fd {ι : Type*} (s : finset ι) (v : ι → ℤ × ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  refine ⟨_, _⟩,
  convert mul_right standard_pairing_Z_sq (∑ a in s, v a),
--  convert @mul_right ℤ (ℤ × ℤ) _ _ _ (ℤ × ℤ) ℤ _ _ _ _ standard_pairing_Z_sq ((1, 1) : ℤ × ℤ),
  intros m hm m0,
  induction m with m1 m2,
  congr,

--  tidy?,

  refine (mul_right standard_pairing_Z_sq ((1, 1) : ℤ × ℤ) : ℤ × ℤ →ₗ[ℤ] ℤ),
--  refine ((λ m : ℤ × ℤ, standard_pairing_Z_sq m (1,1)) : ℤ × ℤ →ₗ[ℤ] ℤ),
  refine
  { to_fun := λ m, standard_pairing_Z_sq m (1,1),
    map_add' :=
      by simp only [forall_const, eq_self_iff_true, linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x m, begin
      rw [standard_pairing_Z_sq, algebra.id.smul_eq_mul, linear_map.map_smul, linear_map.coe_mk, linear_map.coe_mk],
      simp only [has_scalar.smul, gsmul_int_int, linear_map.coe_mk],
  end },
  simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { intros ᾰ, cases ᾰ }, work_on_goal 1 { intros x y, cases y, cases x, dsimp at * }, work_on_goal 2 { intros m x, cases x, dsimp at * } }, work_on_goal 3 { intros x ᾰ ᾰ_1, cases x, dsimp at *, simp at *, simp at *, fsplit, work_on_goal 0 { assumption } },
  { refl },
  { simp [(•)] },

  convert pointed_of_sub_R M,
end

lemma fd {ι : Type*} (v : ι → ℤ × ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  refine ⟨_, _⟩,
  convert mul_right standard_pairing_Z_sq (1, 1),
--  convert @mul_right ℤ (ℤ × ℤ) _ _ _ (ℤ × ℤ) ℤ _ _ _ _ standard_pairing_Z_sq ((1, 1) : ℤ × ℤ),
  intros m hm m0,

  refine (mul_right standard_pairing_Z_sq ((1, 1) : ℤ × ℤ) : ℤ × ℤ →ₗ[ℤ] ℤ),
--  refine ((λ m : ℤ × ℤ, standard_pairing_Z_sq m (1,1)) : ℤ × ℤ →ₗ[ℤ] ℤ),
  refine
  { to_fun := λ m, standard_pairing_Z_sq m (1,1),
    map_add' :=
      by simp only [forall_const, eq_self_iff_true, linear_map.add_apply, linear_map.map_add],
    map_smul' := λ x m, begin
      rw [standard_pairing_Z_sq, algebra.id.smul_eq_mul, linear_map.map_smul, linear_map.coe_mk, linear_map.coe_mk],
      simp only [has_scalar.smul, gsmul_int_int, linear_map.coe_mk],
  end },
  simp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { intros ᾰ, cases ᾰ }, work_on_goal 1 { intros x y, cases y, cases x, dsimp at * }, work_on_goal 2 { intros m x, cases x, dsimp at * } }, work_on_goal 3 { intros x ᾰ ᾰ_1, cases x, dsimp at *, simp at *, simp at *, fsplit, work_on_goal 0 { assumption } },
  { refl },
  { simp [(•)] },

  convert pointed_of_sub_R M,
end



lemma pointed_of_sub_Z {ι : Type*} (v : ι → ℤ) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
by convert pointed_of_sub_R ℤ

lemma fd {ι : Type*} (v : ι → M) (ind : linear_independent ℤ v) :
  pointed ℤ (submodule.span ℕ (v '' set.univ)) :=
begin
  tidy?,
  convert pointed_of_sub_R M,
end
-/
