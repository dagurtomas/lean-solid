import topology.category.Profinite.default
import solid.injective_map
import algebra.free_algebra
import data.finset.basic
import group_theory.free_abelian_group
import linear_algebra.free_module.basic

noncomputable theory

universe u

def bool_to_Z : bool → ℤ := λ x, ite (x = tt) 1 0

instance totally_separated_of_profinite (S : Profinite.{u}) : totally_separated_space S :=
  totally_separated_of_totally_disconnected_compact_hausdorff S

def I (S : Profinite.{u}) : Type u :=
  {fI : S → bool // continuous fI}

def inj_map (S : Profinite.{u}) : S → ((I S) → bool) :=
  map_to_I' S

def CSZ (S : Profinite.{u}) : Type u := {f : S → ℤ // continuous f}

instance ring_SZ (S : Profinite.{u}) : comm_ring (S → ℤ) := pi.comm_ring

def subring_CSZ (S : Profinite.{u}) : subring (S → ℤ) :=
{ carrier := {f : S → ℤ | continuous f},
  zero_mem' := begin
    simp only [set.mem_set_of_eq],
    refine continuous_def.mpr _,
    intros s hs,
    by_cases hzero : (0 : ℤ) ∈ s,
    { have : (0 ⁻¹' s : set S) = set.univ,
      { ext1,
        simp only [set.mem_preimage, set.mem_univ, pi.zero_apply, iff_true],
        assumption },
      rw this,
      exact is_open_univ, },
    { have : (0 ⁻¹' s : set S) = ∅,
      { ext1,
        simp only [set.mem_preimage, pi.zero_apply],
        rw ← not_iff_not,
        split, tauto, exact λ h, hzero, },
      rw this,
      exact is_open_empty, },
  end,
  one_mem' := begin
    simp only [set.mem_set_of_eq],
    refine continuous_def.mpr _,
    intros s hs,
    by_cases hzero : (1 : ℤ) ∈ s,
    { have : (1 ⁻¹' s : set S) = set.univ,
      { ext1,
        simp only [set.mem_preimage, set.mem_univ, pi.zero_apply, iff_true],
        assumption },
      rw this,
      exact is_open_univ, },
    { have : (1 ⁻¹' s : set S) = ∅,
      { ext1,
        simp only [set.mem_preimage, pi.zero_apply],
        rw ← not_iff_not,
        split, tauto, exact λ h, hzero, },
      rw this,
      exact is_open_empty, },
  end,
  add_mem' := λ f g hf hg, continuous.add hf hg,
  mul_mem' := λ f g hf hg, continuous.mul hf hg,
  neg_mem' := λ f hf, continuous.neg hf,
}

instance ring_CSZ (S : Profinite.{u}) : comm_ring (CSZ S) := (subring_CSZ S).to_comm_ring

instance alg_CSZ (S : Profinite.{u}) : algebra ℤ (CSZ S) := algebra_int (CSZ S)

def prod_N (I : Type u) : Type u := Π (n : ℕ), I

def N_order : (ℕ → ℕ → Prop) := λ n m, n ≤ m

def prod_order (I : Type u) : Π (n : ℕ), I → I → Prop := λ n, @well_ordering_rel I

def lex_order (I : Type u) : (prod_N I) → (prod_N I) → Prop :=
  λ x y, pi.lex N_order (prod_order I) x y

def sub_prod (I : Type u) : Type u :=
  {x : prod_N I // (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 →
    (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧
    (∀ n : ℕ, (ordinal.typein (well_ordering_rel) (x n) ≥ ordinal.typein (well_ordering_rel) (x n.succ))) ∧
    {n : ℕ | ordinal.typein (well_ordering_rel) (x n) > 0}.finite }

def subset_prod (I : Type u) : set (prod_N I) :=
  {x : prod_N I | (∀ n : ℕ, ordinal.typein (well_ordering_rel) (x n) ≠ 0 →
    (ordinal.typein (well_ordering_rel) (x n) > ordinal.typein (well_ordering_rel) (x n.succ))) ∧
    (∀ n : ℕ, (ordinal.typein (well_ordering_rel) (x n) ≥ ordinal.typein (well_ordering_rel) (x n.succ))) ∧
    {n : ℕ | ordinal.typein (well_ordering_rel) (x n) > 0}.finite }

instance decidable_eq_IS (S : Profinite.{u}) : decidable_eq (I S) := classical.dec_eq _

def e_indices {I : Type u} (L : sub_prod I) [decidable_eq I] : finset I :=
  finset.image L.val (set.finite.to_finset L.property.2.2)

def e_cont {S : Profinite.{u}} (i : I S) :
  continuous (bool_to_Z ∘ (λ ι : (I S → bool), ι i) ∘ map_to_I' S) :=
  continuous_bot.comp ((continuous_apply i).comp (inj_to_prod' S).1)

def e {S : Profinite.{u}} (i : I S) : CSZ S :=
  ⟨bool_to_Z ∘ (λ ι : (I S → bool), ι i) ∘ map_to_I' S, e_cont i⟩

def prod_e {S : Profinite.{u}} (L : sub_prod (I S)) : CSZ S := finset.prod (e_indices L) e

def Eset (S : Profinite.{u}) : set (sub_prod (I S)) := {L : sub_prod (I S) | ∀ s : finset (sub_prod (I S)),
  (∀ L' : sub_prod (I S), L' ∈ s → (lex_order (I S)) L'.val L.val) → finset.sum s prod_e ≠ prod_e L}

-- def Eset' (S : Profinite.{u}) : set (prod_N (I S)) := {L | ∀ s : finset (sub_prod (I S)),
--   (∀ L' : sub_prod (I S), L' ∈ s → (lex_order (I S)) L'.val L.val) → finset.sum s prod_e ≠ prod_e L}

def Imu (S : Profinite.{u}) (mu : ordinal.{u}) : set (I S) := {i : (I S) | ordinal.typein well_ordering_rel i < mu}

def Smu (S : Profinite.{u}) (mu : ordinal.{u}) : set S := (map_to_I' S) ⁻¹' {f : (I S) → bool | f ⁻¹' {tt} ⊆ Imu S mu}

instance Smu_closed (S : Profinite.{u}) (mu : ordinal.{u}) : is_closed (Smu S mu) :=
begin
  refine is_closed.preimage (inj_to_prod' S).1 (is_compact.is_closed _),
  let s : Π (i : (I S)), set bool :=
    λ i, ite ((ordinal.typein well_ordering_rel i) < mu) (set.univ : set bool) {ff},
  have h : {f : I S → bool | f ⁻¹' {tt} ⊆ Imu S mu} = {x : (I S) → bool | ∀ (i : (I S)), x i ∈ s i},
  { ext f, split,
    { intros hf i,
      have hs : s i = ite ((ordinal.typein well_ordering_rel i) < mu) (set.univ : set bool) {ff} := rfl,
      rw hs,
      split_ifs, { tauto },
      by_contra',
      apply h,
      have hf' : i ∈ f ⁻¹' {tt} := by tidy,
      exact hf hf', },
    { intros hf i hi,
      unfold Imu,
      have hi' : f i = tt := hi,
      simp only [set.mem_set_of_eq],
      have h' := hf i,
      rw hi' at h',
      have hs : s i = ite ((ordinal.typein well_ordering_rel i) < mu) (set.univ : set bool) {ff} := rfl,
      rw hs at h',
      split_ifs at h', { exact h },
      exfalso,
      tauto } },
  rw h,
  exact is_compact_pi_infinite (λ i, topological_space.noetherian_space.is_compact (s i)),
end

lemma Smu_compact (S : Profinite.{u}) (mu : ordinal.{u}) : is_compact (Smu S mu) :=
  is_closed.is_compact (Smu_closed S mu)

instance Smu_top (S : Profinite.{u}) (mu : ordinal.{u}) : topological_space (Smu S mu) :=
  subtype.topological_space

instance Smu_comp (S : Profinite.{u}) (mu : ordinal.{u}) : compact_space (Smu S mu) :=
  is_compact_iff_compact_space.mp (Smu_compact S mu)

instance Smu_t2  (S : Profinite.{u}) (mu : ordinal.{u}) : t2_space (Smu S mu) :=
  subtype.t2_space

instance Smu_tot_disc (S : Profinite.{u}) (mu : ordinal.{u}) : totally_disconnected_space (Smu S mu) :=
  subtype.totally_disconnected_space

def Smu_prof (S : Profinite.{u}) (mu : ordinal.{u}) : Profinite.{u} :=
  Profinite.of (Smu S mu)

def I_map_ord (I : Type*) : I → ordinal := ordinal.typein (@well_ordering_rel I)

def I_lsub (I : Type*) : ordinal := ordinal.lsub (I_map_ord I)

def I_lsub_zero_iff (I : Type*) := @ordinal.lsub_eq_zero_iff I (I_map_ord I)

lemma Imu_zero_is_empty (S : Profinite.{u}) : Imu S 0 = ∅ :=
begin
  unfold Imu,
  ext, split,
  { intros hx,
    exfalso,
    have hx₁ : ordinal.typein well_ordering_rel x < 0 := hx,
    have hx₂ : 0 ≤ ordinal.typein well_ordering_rel x := ordinal.zero_le _,
    rw ← not_le at hx₁,
    exact hx₁ hx₂ },
  { tauto },
end

lemma Smu_zero_is_subsingleton (S : Profinite.{u}) : (Smu S 0).subsingleton :=
begin
  unfold Smu,
  rw Imu_zero_is_empty S,
  have h : {f : I S → bool | f ⁻¹' {tt} ⊆ ∅} = {function.const (I S) ff},
  { ext f, split,
    { intros hf,
      apply set.mem_singleton_of_eq,
      ext,
      simp only [function.const_apply],
      by_contra',
      rw eq_tt_eq_not_eq_ff at this,
      have hx : x ∈ f ⁻¹' {tt} := this,
      exact hf hx },
    { intros hf,
      rw (set.eq_of_mem_singleton hf),
      exact subset_of_eq (set.preimage_const_of_not_mem (λ hff, bool.ff_ne_tt (set.eq_of_mem_singleton hff))) } },
  rw h,
  exact set.subsingleton.preimage set.subsingleton_singleton (inj_to_prod' S).2,
end

lemma unique_Smu_zero (S : Profinite.{u}) [inhabited S] : unique (Smu S 0) :=
begin
  sorry,
end

lemma Smu_prof_subsingleton (S : Profinite.{u}) : subsingleton (Smu_prof S 0) :=
 (Smu S 0).subsingleton_coe.mpr (Smu_zero_is_subsingleton S)

lemma Eset_zero_subsingleton (S : Profinite.{u}) [hS : subsingleton S] : (Eset S).subsingleton :=
begin
  unfold Eset,
  intros a ha b hb,
  ext,
  sorry,
  -- apply (map_to_I' S),
end

instance no_zero_smul_divisors_CSZ (S : Profinite.{u}) : no_zero_smul_divisors ℤ (CSZ S) :=
begin
  refine {eq_zero_or_eq_zero_of_smul_eq_zero := _},
  intros n f hnf,
  by_cases n = 0,
  { left, exact h },
  right,
  ext,
  sorry,
end

theorem nobeling_mu (S : Profinite.{u}) (mu : ordinal) :
  linear_independent ℤ ((Eset (Smu_prof S mu)).restrict prod_e) ∧
  submodule.span ℤ (prod_e '' (Eset (Smu_prof S mu))) = (⊤ : submodule ℤ (CSZ (Smu_prof S mu))) :=
begin
  induction mu using ordinal.induction with mu IH,
  simp only [] at IH,
  cases ordinal.zero_or_succ_or_limit mu,
  { split,
    { rw h,
      -- apply linear_independent_unique,
      sorry, },
    { sorry, }, },
  cases h,
  { sorry },
  { sorry },
end

theorem nobeling (S : Profinite.{u}) : linear_independent ℤ ((Eset S).restrict prod_e) ∧ submodule.span ℤ (prod_e '' Eset S) = (⊤ : submodule ℤ (CSZ S)) :=
begin
  sorry,
  -- let lambda := ordinal.typein well_ordering_rel (I S),
  -- induction lambda using ordinal.induction with lambda IH,
end

theorem nobelings_thm (S : Profinite.{u}) : module.free ℤ (CSZ S) := -- ≅ free_abelian_group (Eset S) :=
begin
  rw module.free_iff_set _ _,
  use prod_e '' (Eset S),
  have hs : submodule.span ℤ (prod_e '' (Eset S)) = ⊤,
  { sorry },
  have hli : linear_independent ℤ (coe : ((prod_e) '' (Eset S)) → CSZ S),
  { sorry },
  sorry,
  -- let b := basis.mk hli,
  -- use ⟨hli, hs⟩,
end
