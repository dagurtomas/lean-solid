-- import laurent_measures.functor
import analysis.special_functions.logb
import for_mathlib.pi_induced
import laurent_measures.thm69
-- import data.real.basic

/-
This files introduces the maps `Θ`, `Φ` (***and `Ψ` ???***), which are the "measurifications" of
`θ`, `ϕ` (*** and `ψ` ???***)
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


noncomputable theory

universe u

namespace laurent_measures_ses

open laurent_measures pseudo_normed_group comphaus_filtered_pseudo_normed_group
  comphaus_filtered_pseudo_normed_group_hom
open_locale big_operators nnreal

section phi_to_hom

-- parameter {p : ℝ≥0}
-- variables [fact(0 < p)] [fact (p < 1)]
-- local notation `r` := @r p
-- local notation `ℳ` := real_measures p

variable {r : ℝ≥0}
variables [fact (0 < r)]
variable {S : Fintype}

local notation `ℒ` := laurent_measures r
local notation `ϖ` := Fintype.of punit

variables {M₁ M₂ : Type u} [comphaus_filtered_pseudo_normed_group M₁]
  [comphaus_filtered_pseudo_normed_group M₂]

def cfpng_hom_add (f g : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
begin
  apply mk_of_bound (f.to_add_monoid_hom + g.to_add_monoid_hom) (f.bound.some + g.bound.some),
  intro c,
  refine ⟨_, _⟩,
  { intros x hx,
      simp only [comphaus_filtered_pseudo_normed_group_hom.coe_mk],
      simp only [add_monoid_hom.add_apply, coe_to_add_monoid_hom],
      convert pseudo_normed_group.add_mem_filtration (f.bound.some_spec hx) (g.bound.some_spec hx),
      rw add_mul, },
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := λ x, ⟨f x, f.bound.some_spec x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  let g₀ : filtration M₁ c → filtration M₂ (g.bound.some * c) := λ x, ⟨g x, g.bound.some_spec x.2⟩,
  have hg₀ : continuous g₀ := g.continuous _ (λ x, rfl),
  simp only [add_monoid_hom.add_apply, coe_to_add_monoid_hom],
  haveI : fact ((f.bound.some * c + g.bound.some * c) ≤ ((f.bound.some + g.bound.some) * c) ) :=
    fact.mk (le_of_eq (add_mul _ _ _).symm),
  let ι : filtration M₂ (f.bound.some * c + g.bound.some * c) → filtration M₂
    ((f.bound.some + g.bound.some) * c) := cast_le,
  have hι : continuous ι := continuous_cast_le _ _,
  let S₀ : filtration M₂ (f.bound.some * c) × filtration M₂ (g.bound.some * c) →
    filtration M₂ (f.bound.some * c + g.bound.some * c) :=
      λ x, ⟨x.fst + x.snd, add_mem_filtration x.fst.2 x.snd.2⟩,
  have hS₀ := continuous_add' (f.bound.some * c) (g.bound.some * c),
  exact hι.comp (hS₀.comp (continuous.prod_mk hf₀ hg₀)),
end

def cfpng_hom_neg (f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :
  (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
begin
  apply mk_of_bound (- f.to_add_monoid_hom) (f.bound.some),
  intro c,
  refine ⟨_, _⟩,
  { intros x hx,
    simp only [comphaus_filtered_pseudo_normed_group_hom.coe_mk],
    convert pseudo_normed_group.neg_mem_filtration (f.bound.some_spec hx) },
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := λ x, ⟨f x, f.bound.some_spec x.2⟩,
  have hf₀ : continuous f₀ := f.continuous _ (λ x, rfl),
  exact (continuous_neg' _).comp hf₀,
end

instance : add_comm_group (comphaus_filtered_pseudo_normed_group_hom M₁ M₂) :=
{ add := cfpng_hom_add,
  add_assoc := by {intros, ext, apply add_assoc},
  zero := 0,
  zero_add := by {intros, ext, apply zero_add},
  add_zero := by {intros, ext, apply add_zero},
  neg := cfpng_hom_neg,
  add_left_neg := by {intros, ext, apply add_left_neg},
  add_comm := by {intros, ext, apply add_comm} }

variable (S)

def Φ : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := 2 • shift (-1) - id
-- variable {S}

lemma Φ_eq_ϕ (F : ℒ S) : Φ S F = ϕ F := rfl

end phi_to_hom

section theta

open theta

parameter (p : ℝ≥0)
local notation `r` := @r p
local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

variable {S : Fintype.{u}}

local notation `ϖ` := Fintype.of (punit : Type u)

def seval_ℒ_c (c : ℝ≥0) (s : S) : filtration (ℒ S) c → (filtration (ℒ ϖ) c) :=
λ F,
  begin
  refine ⟨seval_ℒ S s F, _⟩,
  have hF := F.2,
  simp only [filtration, set.mem_set_of_eq, seval_ℒ, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at ⊢ hF,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hF,
end

variable [fact (0 < p)]

lemma θ_zero : θ (0 : ℒ S) = 0 :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [zero_apply, int.cast_zero, zero_mul, tsum_zero, real_measures.zero_apply],
end

variable [fact (p < 1)]

lemma θ_add (F G : ℒ S) : θ (F + G) = θ F + θ G :=
begin
  dsimp only [θ, theta.ϑ],
  funext,
  simp only [laurent_measures.add_apply, int.cast_add, one_div, inv_zpow', zpow_neg₀, real_measures.add_apply, tsum_add],
  rw ← tsum_add,
  { congr,
    funext,
    rw add_mul },
  all_goals {apply summable_of_summable_norm, simp_rw [norm_mul, norm_inv, norm_zpow, real.norm_two,
    ← inv_zpow₀, inv_eq_one_div] },
  exact aux_thm69.summable_smaller_radius_norm F.d r_half (F.summable s) (λ n, lt_d_eq_zero _ _ _),
  exact aux_thm69.summable_smaller_radius_norm G.d r_half (G.summable s) (λ n, lt_d_eq_zero _ _ _),
end

--for mathlib
lemma nnreal.rpow_int_cast (x : ℝ≥0) (n : ℤ) : x ^ n = x ^ (n : ℝ) := by {
  rw [← nnreal.coe_eq, nnreal.coe_zpow, ← real.rpow_int_cast, ← nnreal.coe_rpow] }

lemma nnreal.rpow_le_rpow_of_exponent_le {x : ℝ≥0} (x1 : 1 ≤ x) {y z : ℝ}
  (hyz : y ≤ z) :
  x ^ y ≤ x ^ z :=
by { cases x with x hx, exact real.rpow_le_rpow_of_exponent_le x1 hyz }


lemma nnreal.tsum_geom_arit_inequality (f: ℤ → ℝ) (r' : ℝ) : ∥ tsum (λ n, (f n : ℝ)) ∥₊ ^ r' ≤
  tsum (λ n, ∥ (f n)∥₊ ^ r' ) :=
begin
  sorry--asked Heather, use nnreal.rpow_sum_le_sum_rpow in `real_measures.lean`
end


lemma aux_bound (F : ℒ S) (s : S) : ∀ (b : ℤ), ∥(F s b : ℝ) ∥₊ ^ (p : ℝ) *
  (2⁻¹ ^ (p : ℝ)) ^ (b : ℝ) ≤ ∥F s b∥₊ * r ^ b :=
begin
  intro b,
  rw [inv_eq_one_div, nnreal.rpow_int_cast],
  refine mul_le_mul_of_nonneg_right _ (real.rpow_nonneg_of_nonneg (nnreal.coe_nonneg _) _),
  have p_le_one : (p : ℝ) ≤ 1,
  { rw ← nnreal.coe_one,
    exact (nnreal.coe_lt_coe.mpr $ fact.out _).le },
  by_cases hF_nz : F s b = 0,
  { rw [hF_nz, int.cast_zero, nnnorm_zero, nnnorm_zero, nnreal.zero_rpow],
    rw [ne.def, ← nnreal.coe_zero, nnreal.coe_eq, ← ne.def],
    exact ne_of_gt (fact.out _) },
  { convert nnreal.rpow_le_rpow_of_exponent_le _ p_le_one,
    { rw nnreal.rpow_one,
      refl },
    { refine not_lt.mp (λ hf, hF_nz (int.eq_zero_iff_abs_lt_one.mp _)),
      suffices : (|F s b| : ℝ) < 1, exact_mod_cast this,
      rw ← int.norm_eq_abs,
      rwa [← nnreal.coe_lt_coe, ← nnnorm_norm, real.nnnorm_of_nonneg (norm_nonneg _)] at hf } }
end

lemma θ_bound : ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  (1 * c) :=
begin
  intros c F hF,
  rw mem_filtration_iff at hF,
  dsimp only [laurent_measures.has_nnnorm] at hF,
  rw [one_mul, real_measures.mem_filtration_iff],
  dsimp only [real_measures.has_nnnorm, θ, theta.ϑ],
  let T := S.2.1,
  have ineq : ∀ (s ∈ T), ∥∑' (n : ℤ), ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ) ≤ ∑' (n : ℤ),
    ∥ ((F s n) : ℝ) * (1 / 2) ^ n∥₊ ^ (p : ℝ),
  { intros s hs,
    apply nnreal.tsum_geom_arit_inequality (λ n, ((F s n) * (1 / 2) ^ n)) (p : ℝ), },
  apply (finset.sum_le_sum ineq).trans,
  simp_rw [nnnorm_mul, ← inv_eq_one_div, nnnorm_zpow, nnnorm_inv, nnreal.mul_rpow, real.nnnorm_two,
    nnreal.rpow_int_cast, ← nnreal.rpow_mul (2 : ℝ≥0)⁻¹, mul_comm, nnreal.rpow_mul (2 : ℝ≥0)⁻¹],
  apply le_trans _ hF,
  apply finset.sum_le_sum,
  intros s hs,
  apply tsum_le_tsum,
  exact aux_bound p F s,
  refine nnreal.summable_of_le _ (F.2 s),
  exacts [aux_bound p F s, F.2 s],
end


lemma θ_bound' :  ∀ c : ℝ≥0, ∀ F : (ℒ S), F ∈ filtration (ℒ S) c → (θ F) ∈ filtration (ℳ S)
  c :=by { simpa [one_mul] using (θ_bound p)}

def θ_to_add : (ℒ S) →+ (ℳ S) :=
{ to_fun := λ F, θ F,
  map_zero' := θ_zero,
  map_add' := θ_add, }

variable (S)

open theta metric real_measures

def seval_ℳ_c (c : ℝ≥0) (s : S) : filtration (ℳ S) c → (filtration (ℳ ϖ) c) :=
λ x,
  begin
  refine ⟨(λ _, x.1 s), _⟩,
  have hx := x.2,
  simp only [filtration, set.mem_set_of_eq, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at ⊢ hx,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hx,
end

--not sure if these are needed
-- def cast_ℳ_c (c : ℝ≥0) : filtration (ℳ S) c → (S → {x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c}) :=
-- begin
--   intros x s,
--   refine ⟨x.1 s, _⟩,
--   have hx := x.2,
--   simp only [filtration, set.mem_set_of_eq, seval_ℒ, nnnorm, laurent_measures.coe_mk,
--     fintype.univ_punit, finset.sum_singleton] at hx,
--   have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
--   rw finset.sum_singleton at this,
--   apply le_trans this hx,
-- end


-- **[FAE]** From here everything might be useless until `lemma inducing_cast_ℳ`: check
-- also the `variable (c : ℝ≥0)` issue; the idea is to replace cast_ℳ_c with α, for which
-- everything seems to work

variable (c : ℝ≥0)

def box := {F : (ℳ S) // ∀ s, ∥ F s ∥₊ ^ (p : ℝ) ≤ c }

instance : has_coe (box S c) (ℳ S) := by {dsimp only [box], apply_instance}
instance : topological_space (ℳ S) := by {dsimp only [real_measures], apply_instance}
instance : topological_space (box S c) := by {dsimp only [box], apply_instance}
instance : module ℝ (ℳ S) := by {dsimp only [real_measures], apply_instance}


-- **[FAE]** The problem is that the `equiv` below is only a type equivalence, not an iso of png's.
def equiv_S_pi_ϖ : (Π s : S, ℳ ϖ) ≃  ℳ S :=
begin
  fconstructor,
  { use λ g s, g s punit.star },
  { use λ F s, λ _, F s},
  { intro _,
    funext,
    apply congr_arg,
    simp only [eq_iff_true_of_subsingleton] },
  { intro _,
    refl }
end

def homeo_S_pi_ϖ : (Π s : S, ℳ ϖ) ≃ₜ ℳ S :=
{ to_equiv := equiv_S_pi_ϖ S,
  continuous_to_fun := continuous_pi (λ _, continuous_apply_apply _ punit.star),
  continuous_inv_fun := continuous_pi (λs,  continuous_pi (λ _, continuous_apply s)) }

example : filtration (Π (s : S), ℳ ϖ) c ≃ Π (s : S), filtration (ℳ ϖ) c :=
begin
  fconstructor,
  { intros F s,
    exact ⟨F.1 s, F.2 s⟩ },
  { intros F,
    use λ s, (F s).1,
    rw mem_filtration_pi,
    intro s,
    exact (F s).2 },
  all_goals { intro, simp only [subtype.val_eq_coe, subtype.coe_eta] },
end



lemma equiv_S_ϖ_c : filtration (Π s : S, ℳ ϖ) c ≃ filtration (ℳ S) c :=
begin
  fconstructor,
  { intro F,
    refine ⟨(equiv_S_pi_ϖ p S).to_fun F.1,_⟩,
    -- refine ⟨(1 /  S.card) • ((equiv_S_ϖ p S).to_fun F.1),_⟩,
    have hF := F.2,
    rw mem_filtration_pi at hF,
    simp_rw [real_measures.mem_filtration_iff, nnnorm] at hF ⊢,
    dsimp only [equiv_S_pi_ϖ],
    simp only [filtration, set.mem_set_of_eq, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at hF,
    sorry,--finally something false but reasonable!
  },
  sorry,
  sorry,
  sorry,
end

def equiv_box_ϖ : (box S c) ≃ Π (s : S), (filtration (ℳ ϖ) c) := sorry
-- { to_fun :=
--   begin
--     let := λ F : (box p S c), (equiv_S_ϖ p S).symm.to_fun F.1,
--     have mah : ∀ F, (this F) ∈ filtration (real_measures p (Fintype.of punit)) c, sorry,
--     use ⟨this, mah⟩,
--   end,
--   inv_fun := _,
--   left_inv := _,
--   right_inv := _ }
-- begin
--   fconstructor,
--   { intros F s,
--     use seval_ℳ S s F.1,
--     simp only [real_measures.mem_filtration_iff, nnnorm, fintype.univ_punit,
--       finset.sum_singleton, seval_ℳ],
--     exact F.2 s },
--   { intro G,
--     use λ s, (G s).1 punit.star,
--     intro s,
--     simpa only [real_measures.mem_filtration_iff, nnnorm, fintype.univ_punit,
--       finset.sum_singleton, seval_ℳ] using (G s).2 },
--   { intro _,
--     ext s,
--     simpa only [seval_ℳ] },
--   { intro G,
--     ext s,
--     simp only [seval_ℳ, subtype.val_eq_coe, subtype.coe_mk],
--     induction x,
--     refl }
-- end

-- def equiv_box_ϖ' : (box S c) ≃ { F : (Π (s : S), ℳ ϖ) // ∀ s, F s ∈ filtration (ℳ ϖ) c } :=
-- def homeo_box_ϖ' : (box S c) ≃ₜ { F : (Π (s : S), ℳ ϖ) // ∀ s, F s ∈ filtration (ℳ ϖ) c } :=

example : (inducing (coe : (box S c) → (ℳ S))) :=
begin
  apply inducing_coe,
end

-- example : inducing (coe : (filtration (Π (s : S), ℳ ϖ) c) → Π (s : S), ℳ ϖ) :=
-- begin
--   refine {induced := _},
--   -- apply_instance,
-- end


-- lemma filtration_pi_equiv' : filtration (Π (s : S), (ℳ ϖ)) c ≃ Π (s : S), (filtration (ℳ ϖ) c) :=
-- begin
--   equiv_rw @filtration_pi_equiv S (λ s, ℳ ϖ) _ c,
--   refine equiv.Pi_congr of_lex _,
--   intro t,
--   fconstructor,
--   { intro x,
--     refine ⟨λ _, x.1 punit.star, x.2⟩ },
--   { intro x,
--     refine ⟨x.1 ,x.2⟩ },
--   sorry,
--   sorry,
-- end


-- def homeo_box_ϖ' : (box S c) ≃ₜ filtration (Π (s : S), (ℳ ϖ)) c :=
-- { to_equiv := (equiv_box_ϖ S c).trans (filtration_pi_equiv(λ s : S, (ℳ ϖ)) c).symm,
--   continuous_to_fun := sorry,
--   continuous_inv_fun := sorry,
-- }

def homeo_box_ϖ : (box S c) ≃ₜ Π (s : S), (filtration (ℳ ϖ) c) :=
{ to_equiv := equiv_box_ϖ S c,
  continuous_to_fun := begin



  -- let ι : (Π s : S, filtration (ℳ ϖ) c) → (Π s : S, ℳ ϖ) := λ F s, (F s).1,
  -- have : inducing ι,

    -- sorry;{
    -- have : has_coe (filtration (Π s : S, (ℳ ϖ)) c) (Π s : S, (ℳ ϖ)),
    -- exact has_coe,
    -- simp,
    -- have sette : inducing (λ F : filtration (Π s : S, (ℳ ϖ)) c, F.1),
    -- simp_rw subtype.val_eq_coe,
    -- refine inducing_coe,
    -- have := inducing (Π (s : S), filtration (ℳ ϖ) c) → (Π s : S, ℳ ϖ)),
    have quattro := @inducing_coe (Π s : S, (ℳ ϖ)) _ (filtration (Π s : S, (ℳ ϖ)) c),
    let e_pi := (filtration_pi_equiv(λ s : S, (ℳ ϖ)) c).symm ∘
      (equiv_box_ϖ p S c).to_fun,

    -- equiv_rw this at quattro,
    -- have tre : inducing (cast_remah p S c) := by {exact inducing_coe},
    -- have uno := @inducing_coe (Π (s : S), (ℳ ϖ)) _ (Π (s : S), (filtration (ℳ ϖ) c)),
    -- have := @coe_to_lift (filtration (Π s : S, (ℳ ϖ)) c) (Π s : S, ℳ ϖ),
    have := @inducing.continuous_iff (box p S c)
      (filtration (Π s : S, (ℳ ϖ)) c)
      (Π s : S, (ℳ ϖ)) _ _ _--e_pi (λ F, F.1) _ _,
      e_pi (λ F, F.1),
    -- simp at e_pi this,
    -- simp at quattro,
    -- simp_rw [subtype.val_eq_coe] at this,
    -- apply this quattro,
    -- simp at this,-- coe quattro,
    --  _ _ _ _ _ _ (((equiv_box_ϖ p S c).to_fun))
    --    _ quattro,
    --  ((equiv_box_ϖ p S c).to_fun)
    --   coe (inducing_coe),
    --  (coe : (Π (s : S), filtration (ℳ ϖ) c) → (Π (s : S), (ℳ ϖ))),
      -- (cast_remah p S c),
      -- ((equiv_box_ϖ p S c).to_fun) _ uno,
  -- },
  sorry,
  end,
  continuous_inv_fun := sorry, }

--- **[FAE]**: FROM HERE ON, EVERYTHING HAS BEEN CLEANED UP

def α : filtration (ℳ S) c → box S c :=
begin
  intro x,
  use x,
  have hx := x.2,
  intro s,
  simp only [filtration, set.mem_set_of_eq, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at hx,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hx,
end


lemma coe_α_coe : (coe : (box S c) → (ℳ S)) ∘ (α S c) = coe := by {funext _, refl}

lemma inducing_α : inducing (α S c) :=
begin
  have ind_ind := @induced_compose _ _ (ℳ S) _ (α p S c) coe,
  rw [coe_α_coe p S c] at ind_ind,
  exact {induced := eq.symm ind_ind},
end


-- lemma M_inj : function.injective (cast_ℳ_c S c) :=
-- begin
--   rintros F G h,
--   dsimp only [cast_ℳ_c] at h,
--   ext s,
--   have := congr_fun h s,
--   simpa only,
-- end

-- lemma inducing_cast_ℳ (c : ℝ≥0) : inducing (cast_ℳ_c S c) :=
-- begin
--   -- let f :
--   -- let := cast_ℳ_c p S c,
--   -- let M := ℳ S,
--   -- unfold [ℳ S],
--   -- have := @pi_induced_induced S (λ i, ℝ) (λ i, { x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c}) _ ,--(cast_ℳ_c p S c),
--   -- fconstructor,
--   -- dsimp [real_measures.topological_space],
--   sorry,
--   -- apply pi_induced_induced,
--   -- sorry,
--   -- simp,
--   -- sorry,
-- end

-- lemma cont_cast_ℳ (c : ℝ≥0) : continuous (cast_ℳ_c S c) := sorry
-- def equiv_ball_ℳ (c : ℝ≥0) : filtration (ℳ ϖ) c ≃ₜ {x : ℝ // ∥ x ∥ ^ (p : ℝ) ≤ c} := sorry

-- lemma seval_cast_ℳ_commute (c : ℝ≥0) (s : S) :
--  (λ x, (cast_ℳ_c S c x s)) = (equiv_ball_ℳ c) ∘ seval_ℳ_c S c s := sorry

-- lemma seval_cast_ℳ_commute' {X : Type*} (c : ℝ≥0) {f : X → filtration (ℳ S) c} (s : S)  :
--  (λ x, (cast_ℳ_c S c (f x) s)) = (equiv_ball_ℳ c) ∘ seval_ℳ_c S c s ∘ f :=
--  begin
--   ext z,
--   have h_commute := @seval_cast_ℳ_commute p S _ _ c s,
--   have := congr_fun h_commute (f z),
--   simp only at this,
--   rw this,
--  end


lemma seval_ℳ_α_commute (c : ℝ≥0) (s : S) :
 (λ F, ((homeo_box_ϖ S c) ∘ (α S c)) F s) = (λ F, seval_ℳ_c S c s F) :=
begin
  sorry; {
  funext,
  simp,

}
end

 lemma seval_ℳ_α_commute' {X : Type*} (c : ℝ≥0) {f : X → filtration (ℳ S) c} (s : S)  :
 (λ x, ((homeo_box_ϖ S c) ∘ (α S c)) (f x) s) = (λ x, seval_ℳ_c S c s (f x)) :=
 begin
  ext z,
  have h_commute := @seval_ℳ_α_commute p S _ _ c s,
  have := congr_fun h_commute (f z),
  simp only at this,
  rw this,
 end

@[nolint unused_arguments]
def seval_ℒ_bdd_c (c : ℝ≥0) (S : Fintype) (A : finset ℤ) (s : S) :
laurent_measures_bdd r S A c → laurent_measures_bdd r ϖ A c :=
begin
  intro F,
  use λ _, F s,
  have hF := F.2,
  simp only [filtration, set.mem_set_of_eq, seval_ℒ, nnnorm, laurent_measures.coe_mk,
    fintype.univ_punit, finset.sum_singleton] at ⊢ hF,
  have := finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr $ finset.mem_univ_val _),
  rw finset.sum_singleton at this,
  apply le_trans this hF,
end

lemma continuous_seval_ℒ_c (c : ℝ≥0) (s : S) : continuous (seval_ℒ_c c s) :=
begin
  rw laurent_measures.continuous_iff,
  intro A,
  let := seval_ℒ_bdd_c p c S A s,
  have h_trunc : (@truncate r ϖ c A) ∘ (seval_ℒ_c p c s) =
    (seval_ℒ_bdd_c p c S A s) ∘ (@truncate r S c A),
  { ext ⟨F, hF⟩ π k,
    dsimp only [seval_ℒ_bdd_c, seval_ℒ_c],
    refl },
  rw h_trunc,
  apply continuous.comp,
  apply continuous_of_discrete_topology,
  apply truncate_continuous,
end

open metric

--**[FAE]** Probably needed, but check before proving it!
lemma continuous_iff_for_all_closed (c : ℝ≥0) {X : Type*} [topological_space X]
  (f : X → closed_ball (0 : ℝ) c) (H : ∀ a : ℝ≥0, ∀ (H : a ≤ c), is_closed
    (f⁻¹' ((closed_ball ⟨(0 : ℝ), (mem_closed_ball_self c.2)⟩ a) : set ((closed_ball (0 : ℝ) c)))))
    : continuous f :=
 begin
   sorry,
 end


def θ_c (c : ℝ≥0) (T : Fintype) : (filtration (laurent_measures r T) c) →
  (filtration (real_measures p T) c) :=
begin
  intro f,
  rw [← one_mul c],
  use ⟨θ f, θ_bound p c f f.2⟩,
end

lemma commute_seval_ℒ_ℳ (c : ℝ≥0) (s : S) :
  (θ_c c (Fintype.of punit)) ∘ (seval_ℒ_c c s) = (seval_ℳ_c S c s) ∘ (θ_c c S) :=
begin
  ext F x,
  simp only [seval_ℳ_c, seval_ℒ_c, seval_ℒ, θ_c, one_mul, subtype.coe_mk, eq_mpr_eq_cast,
    set_coe_cast],
  refl,
end


-- **[FAE]** This is the right lemma, in the proof we should introduce α and use it is inducing
-- OLD lemma continuous_of_seval_ℳ_comp_continuous (c : ℝ≥0) {X : Type*} [topological_space X]
--   {f : X → (filtration (ℳ S) c)} : (∀ s, continuous ((seval_ℳ_c S c s) ∘ f)) → continuous f :=
-- begin
--   intro H,
--   replace H : ∀ (s : S), continuous (λ x : X, (cast_ℳ_c p S c) (f x) s),
--   { intro s,
--     rw @seval_cast_ℳ_commute' p S _ _ X c f s,
--     apply ((equiv_ball_ℳ p c).comp_continuous_iff).mpr,
--     exact H s },
--   rw ← continuous_pi_iff at H,
--   convert_to (continuous (λ x, cast_ℳ_c p S c (f x))) using 0,
--   exacts [eq_iff_iff.mpr (inducing_cast_ℳ p S c).continuous_iff, H],
--   end

lemma continuous_of_seval_ℳ_comp_continuous (c : ℝ≥0) {X : Type*} [topological_space X]
  {f : X → (filtration (ℳ S) c)} : (∀ s, continuous ((seval_ℳ_c S c s) ∘ f)) → continuous f :=
begin
  intro H,
  replace H : ∀ (s : S), continuous (λ x : X, ((homeo_box_ϖ p S c) ∘ (α p S c)) (f x) s),
  { intro,
    rw [seval_ℳ_α_commute' p S c s],
    exact H s },
  rw ← continuous_pi_iff at H,
  convert_to (continuous (λ x, (homeo_box_ϖ p S c) (α p S c (f x)))) using 0,
  { apply eq_iff_iff.mpr,
    rw [homeomorph.comp_continuous_iff, (inducing_α p S c).continuous_iff] },
  exact H,
  end

-- This is the main continuity property needed in `ses2.lean`
lemma continuous_θ_c (c : ℝ≥0) : continuous (θ_c c S) :=
begin
  apply continuous_of_seval_ℳ_comp_continuous,
  intro s,
  rw ← commute_seval_ℒ_ℳ,
  refine continuous.comp _ (continuous_seval_ℒ_c p S c s),
  sorry,




  -- dsimp only [θ_c],
  -- apply cont_at_cast_ℳ c (θ_c S c),
  -- rw aux_commutative_θ,
  -- apply continuous.comp _ (cont_cast_ℒ c),
  -- apply continuous_pi,
  -- intro s,
  -- sorry,







  --**[FAE]** Old version
  -- sorry;
  -- {
  -- dsimp only [θ_c],
  -- apply cont_at_cast_ℳ c (θ_c S c),
  -- apply continuous_pi,
  -- intro s,
  -- apply ((equiv_ball_ℓp c).comp_continuous_iff).mp,
  -- let f := (equiv_ball_ℓp c) ∘ (λ a,
  --   (cast_ℳ_c c ∘ θ_c S c) a s),
  -- apply cont_at_closed (c ^ (1 / p : ℝ)) f,
  -- intros a ha,
  -- dsimp [f],
  -- --from here, it is clearly broken
  -- convert is_closed_empty,
  -- apply aux_6 S a c s ha,
  -- }
  -- unfold,
  -- dsimp [f, cast_ℳ_c, θ_c],

  -- sorry,



  --all_goals {apply_instance},
end


variable {S}

end theta

end laurent_measures_ses
