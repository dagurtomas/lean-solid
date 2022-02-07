-- import for_mathlib.short_exact_sequence
import data.int.interval
import data.finset.nat_antidiagonal
import laurent_measures.aux_lemmas
import laurent_measures.basic
import laurent_measures.theta
import linear_algebra.basic
import order.filter.at_top_bot tactic.linarith


/-
This file introduces the maps
* `θ`, which is the specialization of evaluation-at-ξ map `ϑ` from `laurent_measures.theta`
  at `ξ=1/2`.
* `ϕ` which corresponds to multiplying a Laurent series in `ℒ S = (laurent_measures r S)`
  for `r = 2^(1/p)` by `2T-1`.
* `ψ` corresponds to multiplying a Laurent series by `(2T-1)^-1`. It is defined only on series
  vanishing at `1/2`, so that it again takes values in `ℒ S`
* The maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ`,
  so they are morphisms in the right category (**[FAE]** Not here any more!)

The main results are
* `injective_ϕ` stating that `ϕ` is injective;
* `θ_ϕ_complex` stating that `ϕ ∘ θ = 0`; and
* `θ_ϕ_exact` stating that the kernel of `θ` coincides with the image of `ϕ`.
Together with `ϑ_surjective` from `laurent_measures.theta` (specialized at `ξ=1/2`, so that `ϑ` is
`θ`) this is the statement of Theorem 6.9 of `Analytic.pdf` of interest to us, although only "on
elements" and not yet as a Short Exact Sequence in the right category.
-/

noncomputable theory

open nnreal theta laurent_measures aux_thm69 finset
open_locale nnreal classical big_operators topological_space

section mem_exact

parameter {p : ℝ≥0}

def r : ℝ≥0 := (1 / 2) ^ (p:ℝ)

variables [fact(0 < p)] [fact (p < 1)]
variable {S : Fintype}

lemma r_half : 1 / 2 < r :=
begin
  calc (1/2:ℝ≥0)
      = (1/2) ^ (1:ℝ) : (rpow_one (1/2:ℝ≥0)).symm
  ... < r : rpow_lt_rpow_of_exponent_gt (half_pos zero_lt_one) (half_lt_self one_ne_zero) _,
  rw [← nnreal.coe_one, nnreal.coe_lt_coe],
  exact fact.out _
end

lemma r_pos : 0 < r := lt_of_le_of_lt zero_le' r_half

lemma r_lt_one : r < 1 :=
begin
  refine rpow_lt_one zero_le' (half_lt_self one_ne_zero) _,
  rw nnreal.coe_pos,
  exact fact.out _
end


local notation `ℳ` := real_measures p
local notation `ℒ` := laurent_measures r

variables {S}

def laurent_measures.d (F : ℒ S) : ℤ := (exists_bdd_filtration r_pos r_lt_one F).some

lemma lt_d_eq_zero (F : ℒ S) (s : S) (n : ℤ) :
  n < F.d → F s n = 0 := (exists_bdd_filtration r_pos r_lt_one F).some_spec s n

lemma laurent_measures.summable_half (F : ℒ S) (s : S) : summable (λ n, ((F s n) : ℝ) *
  (1 / 2) ^ n) := @summable_smaller_radius _ _ F.d (F.summable s) (lt_d_eq_zero _ _) r_half

def θ : ℒ S → ℳ S := ϑ (1 / 2 : ℝ) r p S

variables [fact (0 < r)]

def ϕ : ℒ S → ℒ S :=
λ F, 2 • shift (-1) F - F

lemma ϕ_apply (F : ℒ S) (s : S) (n : ℤ) : ϕ F s n = 2 * F s (n-1) - F s n :=
by simp only [ϕ, sub_apply, nsmul_apply, shift_to_fun_to_fun, nsmul_eq_mul]; refl

lemma injective_ϕ (F : ℒ S) (H : ϕ F = 0) : F = 0 :=
begin
  dsimp only [ϕ] at H, rw [sub_eq_zero] at H,
  replace H : ∀ n : ℤ, ∀ s : S, 2 * F s (n - 1) = F s n,
  { intros n s,
    conv_rhs { rw ← H },
    simp only [nsmul_apply, shift_to_fun_to_fun, int.add_neg_one, nsmul_eq_mul,
      int.nat_cast_eq_coe_nat, int.coe_nat_bit0, int.coe_nat_succ, int.coe_nat_zero, zero_add,
      mul_eq_mul_left_iff, eq_self_iff_true, bit0_eq_zero, one_ne_zero, or_false],
    refl },
  ext s n,
  simp only [zero_apply],
  apply int.induction_on' n (F.d - 1),
  { apply lt_d_eq_zero _ _ (F.d - 1),
    simp only [sub_lt_self_iff, zero_lt_one] },
  { intros k h hk₀,
    specialize H (k + 1) s,
    rw [← H, add_sub_cancel, hk₀, mul_zero] },
  { intros k h hk₀,
    specialize H k s,
    simp only [hk₀, mul_eq_zero, (@two_ne_zero ℝ _ _), bit0_eq_zero, one_ne_zero, false_or] at H,
    exact H },
end


lemma θ_ϕ_complex (F : ℒ S) : (θ ∘ ϕ) F = 0 :=
begin
  funext s,
  convert_to ∑' (n : ℤ), ((2 * F s (n - 1) - F s n) : ℝ) * (1 / 2) ^ n = 0,
  { apply tsum_congr,
    intro b,
    rw ← inv_eq_one_div,
    apply (mul_left_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
    have : (2 : ℝ) * (F s (b - 1)) = ((2 : ℤ) * (F s (b - 1))),
    { rw [← int.cast_one, int.cast_bit0] },
    rw [this, ← int.cast_mul, ← int.cast_sub, ϕ_apply], },
  have h_pos : has_sum (λ n, ((2 * F s (n - 1)) : ℝ) * (1 / 2) ^ n)
    (F.summable_half s).some,
  { let e : ℤ ≃ ℤ := ⟨λ n : ℤ, n - 1, λ n, n + 1, by {intro, simp}, by {intro, simp}⟩,
    convert (equiv.has_sum_iff e).mpr (F.summable_half s).some_spec using 1,
    ext n,
    have div_half : ∀ b : ℤ, (1 / 2 : ℝ) ^ b * (2 : ℝ) = (1 / 2) ^ (b - 1),
    { intro b,
      rw [← inv_eq_one_div, @zpow_sub_one₀ ℝ _ _ (inv_ne_zero two_ne_zero) b],
      apply (mul_right_inj' (@zpow_ne_zero ℝ _ _ b (inv_ne_zero two_ne_zero))).mpr,
      exact (inv_inv₀ 2).symm },
    rw [mul_comm, ← mul_assoc, div_half, mul_comm],
    refl, },
  simp_rw [sub_mul],
  rw [tsum_sub h_pos.summable, sub_eq_zero, h_pos.tsum_eq],
  exacts [(F.summable_half s).some_spec.tsum_eq.symm,
    (F.summable_half s)],
end


lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
 2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1)⁻¹ :=
begin
  have h_sum := F.summable_half s,
  simp_rw [one_div, inv_zpow'] at h_sum,
  have h_shift := int_tsum_shift (λ n, (F s n : ℝ) * (2 ^ (-n))) N,
  simp only at h_shift,
  simp_rw [subtype.val_eq_coe, ← zpow_neg₀],
  rw [← h_shift, ← _root_.tsum_mul_left, tsum_congr],
  intro n,
  nth_rewrite_rhs 0 [mul_comm],
  rw [mul_assoc, ← (zpow_add₀ (@two_ne_zero ℝ _ _)), neg_add_rev, neg_add_cancel_comm, zpow_neg₀,
    zpow_coe_nat, add_comm],
end

def ψ (F : ℒ S) (hF : θ F = 0) : ℒ S :=
begin
  let b : S → ℤ → ℤ := λ s n,
    if hn : n - F.d ≥ 0 then - ∑ l in range ((int.eq_coe_of_zero_le hn).some.succ),
      (F s (n -l) * (2 ^ l))
    else 0,
  use b,
  intro s,
  have h_θ : ∀ n : ℤ, ∥ b s n ∥ * r ^ (n : ℤ)  =
    (1 / 2) * ∥ tsum (λ i : ℕ, ((F s (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ (n : ℤ),
  { dsimp only [b],
    intro n,
    simp only [one_div, sub_nonneg, ge_iff_le, inv_pow₀, mul_eq_mul_right_iff],
    apply or.intro_left,
    by_cases h_event : n - F.d < 0,
    { replace h_event := not_le_of_gt h_event,
      rw sub_nonneg at h_event,
      rw [dif_neg h_event, tsum_reindex],
      simp only [subtype.val_eq_coe, norm_zero],
      suffices : ∑' (m : {m // n + 1 ≤ m}), (F s ↑m : ℝ) * (2 ^ (- ↑m)) =
        ∑' (m : ℤ), (F s m) * (2 ^ (-m)),
      { simp_rw [← zpow_neg₀],
        rw this,
        simp only [θ, ϑ, one_div, inv_zpow'] at hF,
        replace hF := congr_fun hF s,
        rw real_measures.zero_apply at hF,
        simp only [zero_eq_mul, mul_eq_zero, norm_eq_zero],
        repeat {apply or.intro_right},
        apply hF, },
      { rw tsum_eq_tsum_of_has_sum_iff_has_sum,
        intro z,
        apply @has_sum_subtype_iff_of_support_subset _ _ _ _ (λ m, (F s m : ℝ) * (2 ^ (- m))) z
          {m : ℤ | n + 1 ≤ m},
        rw function.support_subset_iff',
        intros a ha,
        simp only [int.cast_eq_zero, inv_eq_zero, mul_eq_zero],
        apply or.intro_left,
        simp only [not_le, set.mem_set_of_eq, int.lt_add_one_iff] at ha,
        apply lt_d_eq_zero,
        rw ← sub_nonneg at h_event,
        replace h_event := sub_neg.mp (not_le.mp h_event),
        exact lt_of_le_of_lt ha h_event,
        } },
    { rw not_lt at h_event,
      let m := (int.eq_coe_of_zero_le h_event).some,
      rw sub_nonneg at h_event,
      rw dif_pos h_event,
      simp_rw [← int.norm_cast_real, int.cast_neg, int.cast_sum, int.cast_mul, int.cast_pow,
        int.cast_two],
      rw ← sub_nonneg at h_event,
      rw [sum_range_sum_Icc (coe ∘ (F s)) n F.d h_event,
        sum_Icc_sum_tail (F s) n F.d _ (lt_d_eq_zero F s) h_event],
      { rw [← (abs_eq_self.mpr (inv_nonneg.mpr (@zero_le_two ℝ _))), ← real.norm_eq_abs,
          ← normed_field.norm_mul, real.norm_eq_abs, real.norm_eq_abs, abs_eq_abs,
          ← (sub_add_cancel n 1), (sub_eq_add_neg n 1), (add_assoc n _), (add_comm n _),
          (add_assoc (-1 : ℤ) _ _), (add_comm 1 n), zpow_add₀ (@two_ne_zero ℝ _ _),
          ← (add_assoc (-1 : ℤ) _ _), neg_add_cancel_comm, ← int.succ, mul_assoc, zpow_neg₀,
          zpow_one],
        apply or.intro_left,
        rw ← tsum_reindex F n.succ s },
      { simp only [θ, ϑ, one_div] at hF,
        replace hF := congr_fun hF s,
        simp only [real_measures.zero_apply, inv_eq_one_div] at hF,
        simp_rw [← inv_zpow₀, inv_eq_one_div],
        exact (summable.has_sum_iff
          (F.summable_half s)).mpr hF }}},
  have : ∀ (n : ℤ), n < F.d → ∥∑' (i : ℕ), (F s (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ = 0,
  { intros n hn,
    replace hn := not_le_of_gt (sub_neg.mpr hn),
    specialize h_θ n,
    simp only [mul_eq_mul_right_iff, zpow_ne_zero n (nnreal.coe_ne_zero.mpr (ne_of_lt r_pos).symm),
      or_false] at h_θ,
    convert_to 1 / 2 * ∥∑' (i : ℕ), (F s (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ = 0 using 0,
    simp only [one_div, mul_eq_zero, inv_eq_zero, bit0_eq_zero, one_ne_zero, false_or],
    rw [← h_θ, norm_eq_zero],
    dsimp [b],
    rw dif_neg hn },
  simp only [←nnreal.summable_coe, nonneg.coe_mul, _root_.coe_nnnorm, coe_zpow, summable_congr h_θ],
  exact aux_thm69.summable_convolution r_pos r_half (F s) F.d (F.summable s) (lt_d_eq_zero F s) this
end

theorem θ_ϕ_exact (F : ℒ S) (hF : θ F = 0) : ∃ G, ϕ G = F :=
begin
  use ψ F hF,
  ext s n,
  dsimp [ϕ, ψ],
  simp,
  by_cases hn : F.d ≤ n - 1,
  { rw [dif_pos hn, dif_pos $ hn.trans $ sub_le_self n zero_le_one, neg_eq_neg_one_mul, ← mul_assoc,
      mul_comm (2 : ℤ) (-1 : ℤ), mul_assoc, mul_sum, ← neg_eq_neg_one_mul,
      neg_sub_neg, finset.sum_range_succ', sub_eq_iff_eq_add'],
    simp only [pow_zero, sub_zero, mul_one, int.coe_nat_zero, int.coe_nat_add, int.coe_nat_one,
      add_comm _ (1 : ℤ), ← sub_sub n 1],
    congr' 1,
    refine finset.sum_congr _ _,
    { congr' 1,
      apply int.coe_nat_inj,
      rw ← sub_nonneg at hn,
      have := (int.eq_coe_of_zero_le hn).some_spec,
      simp only [int.coe_nat_succ, ← sub_eq_iff_eq_add],
      convert this using 1,
      transitivity n - F.d - 1,
      { congr' 1,
        have : 0 ≤ n - F.d, { linarith },
        symmetry, exact (int.eq_coe_of_zero_le this).some_spec },
      { ring_nf } },
    { intros i hi, rw pow_succ, ring_nf, }, },
  { rw [dif_neg hn, mul_zero, zero_sub],
    by_cases hn' : F.d ≤ n,
    { rw [dif_pos hn', neg_neg],
      have hn'' : F.d = n,
      { apply eq_of_le_of_not_lt hn',
        rw not_lt,
        exact int.le_of_sub_one_lt (not_le.mp hn) },
      replace hn'' : n - F.d = 0 := by {rw [hn'', sub_self]},
      simp_rw [hn'', ← int.coe_nat_zero, int.coe_nat_inj', (@exists_eq' ℕ 0).some_spec.symm,
        sum_range_one],
      simp only [int.coe_nat_zero, sub_zero, pow_zero, mul_one] },
    { rw dif_neg hn',
      exact (lt_d_eq_zero F s n (not_le.mp hn')).symm }},
end

end mem_exact
