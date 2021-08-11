import analysis.specific_limits
import category_theory.Fintype
import analysis.normed_space.basic

import overconvergent_measures.bounded
import pseudo_normed_group.basic
import pseudo_normed_group.category

universe u

noncomputable theory
open_locale big_operators nnreal

section definitions

/-
structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, (∥ to_fun s n ∥₊ * r ^ n)))
(bdd        : ∀ s, tsum (λ n, (∥ to_fun s n ∥₊ * r ^ n)) ≤ c)
-/

structure oc_measures (r : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable'   : ∀ s, summable (λ n, ∥ to_fun s n ∥ * r ^ n))

variables {r : ℝ≥0} {S : Fintype.{u}}

instance : has_coe_to_fun (oc_measures r S) :=
⟨λ F, S → ℤ → ℤ, λ F, F.to_fun⟩

@[ext]
lemma oc_measures.ext (F G : oc_measures r S) : (F : S → ℤ → ℤ) = G → F = G :=
by { intros h, cases F, cases G, simpa }

lemma oc_measures.summable (F : oc_measures r S) (s : S) : summable (λ n, ∥ F s n ∥ * r ^ n) :=
  F.2 _

def add : oc_measures r S → oc_measures r S → oc_measures r S := λ F G,
{ to_fun := F + G,
  summable' := begin
    intros s,
    dsimp,
    have : ∀ n, ∥ F s n + G s n ∥ * r ^ n ≤ ∥ F s n ∥ * r ^ n + ∥ G s n ∥ * r ^ n,
    { intros n,
      rw ← add_mul,
      refine mul_le_mul (norm_add_le _ _) (le_refl _) _
        (add_nonneg (norm_nonneg _) (norm_nonneg _)),
      refine fpow_nonneg _ _,
      exact nnreal.coe_nonneg r },
    apply summable_of_nonneg_of_le _ this,
    { apply summable.add,
      exact F.summable s,
      exact G.summable s },
    { intros n,
      refine mul_nonneg (norm_nonneg _) _,
      refine fpow_nonneg _ _,
      exact nnreal.coe_nonneg r }
  end }

instance : has_add (oc_measures r S) := ⟨add⟩

@[simp]
lemma add_apply (F G : oc_measures r S) (s : S) (n : ℤ) : (F + G) s n = F s n + G s n := rfl

def zero : oc_measures r S :=
{ to_fun := 0,
  summable' := λ s, by simp [summable_zero] }

instance : has_zero (oc_measures r S) := ⟨zero⟩

@[simp]
lemma zero_apply (s : S) (n : ℤ) : (0 : oc_measures r S) s n = 0 := rfl

def neg : oc_measures r S → oc_measures r S := λ F,
{ to_fun := - F,
  summable' := λ s, by simp [F.summable] }

instance : has_neg (oc_measures r S) := ⟨neg⟩

@[simp]
lemma neg_apply (F : oc_measures r S) (s : S) (n : ℤ) : (-F) s n = - (F s n) := rfl

def sub : oc_measures r S → oc_measures r S → oc_measures r S := λ F G,
{ to_fun := F - G,
  summable' := (add F (neg G)).summable }

instance : has_sub (oc_measures r S) := ⟨sub⟩

@[simp]
lemma sub_apply (F G : oc_measures r S) (s : S) (n : ℤ) : (F - G) s n = F s n - G s n := rfl

example (a m : ℤ) : (-a)*m=a*(-m) := neg_mul_comm a m

instance : add_comm_monoid (oc_measures r S) :=
{ add_assoc := λ a b c, by { ext, simp [add_assoc] },
  add_comm := λ F G, by { ext, simp [add_comm] },
  zero_add := λ a, by { ext, simp },
  add_zero := λ a, by { ext, simp },
  nsmul := λ n F,
  { to_fun := λ s k, n • (F s k),
    summable' := begin
      intro s,
      have := summable.mul_left (↑n : ℝ) (F.2 s),
      simp_rw [pi.has_mul, ← mul_assoc, int.norm_eq_abs, ← int.cast_abs] at this,
      simp_rw [int.norm_eq_abs, ← int.cast_abs, abs_nsmul, nsmul_eq_mul],
      simp only [int.cast_coe_nat, int.cast_mul, int.nat_cast_eq_coe_nat,
      int.cast_abs] at *,
      exact this,
    end },
  nsmul_zero' := λ F, by { ext, refl },
  nsmul_succ' := λ n F, by { ext, refl },
  ..(infer_instance : has_add _),
  ..(infer_instance : has_zero _) }

instance : add_comm_group (oc_measures r S) :=
{ neg := neg,
  sub := sub,
  sub_eq_add_neg := λ F G, by { ext, refl },
  gsmul := λ n F,
  { to_fun := λ s m, gsmul n (F s m),
    summable' := begin
      intro s,
      have := summable.mul_left (↑n : ℝ) (F.2 s),
      simp only [pi.has_mul, ← mul_assoc, int.norm_eq_abs, ← int.cast_abs] at this,
      simp only [int.norm_eq_abs, ← int.cast_abs, gsmul_eq_smul, abs_gsmul],
      by_cases hn : n ≥ 0,
      { simp only [abs_of_nonneg hn, smul_eq_mul, int.cast_mul],
        exact this },
      { simp only [abs_of_neg (lt_of_not_ge hn), smul_eq_mul, int.cast_mul,
        int.cast_neg, neg_mul_eq_neg_mul_symm],
        apply summable.neg this },
    end },
  gsmul_zero' := λ F, by { ext, simpa, },
  gsmul_succ' := λ n F, by { ext, simpa [add_apply, int.coe_nat_succ, int.of_nat_eq_coe,
    gsmul_eq_smul, smul_eq_mul, add_mul, add_comm, one_mul], },
  gsmul_neg' := λ n F, by { ext, simp only [int.coe_nat_succ, int.of_nat_eq_coe,
    int.neg_succ_of_nat_coe, add_comm, gsmul_eq_smul, smul_eq_mul], ring_nf},
  add_left_neg := λ F, by { ext, simp, },
  add_comm := λ a b, by { ext, dsimp, rw add_comm },
  ..(infer_instance : add_comm_monoid _),
  ..(infer_instance : has_neg _),
  ..(infer_instance : has_sub _) }.

instance : has_norm (oc_measures r S) :=
⟨λ F, ∑ s, ∑' n, ∥ F s n ∥ * (r : ℝ) ^ n⟩

@[simp]
lemma norm_def (F : oc_measures r S) : ∥ F ∥ = ∑ s, ∑' n, ∥ F s n ∥ * (r : ℝ)^n := rfl

lemma norm_add (F G : oc_measures r S) : ∥ F + G ∥ ≤ ∥ F ∥ + ∥ G ∥ :=
begin
  dsimp,
  rw ← finset.sum_add_distrib,
  apply finset.sum_le_sum,
  intros s hs,
  rw ← tsum_add (F.summable _) (G.summable _),
  apply tsum_le_tsum _ ((F + G).summable _),
  { apply summable.add (F.summable s) (G.summable s) },
  { intros b,
    dsimp,
    rw ← add_mul,
    refine mul_le_mul (norm_add_le _ _) (le_refl _) (fpow_nonneg (nnreal.coe_nonneg _) _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) }
end

/-
lemma exists_c (F : oc_measures r S) : ∃ (c : ℝ≥0),
  ∀ s : S, ∑' n, ∥ F s n ∥ * r ^ n ≤ c :=
begin
  use ∑ s, ∑' n, ∥ F s n ∥ * r ^ n,
  { apply finset.sum_nonneg,
    rintros s -,
    apply tsum_nonneg,
    intros n,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r, },
  { sorry },
end
-/

/-- This lemma puts bounds on where `F s n` can be nonzero. -/
lemma eq_zero_of_filtration (F : oc_measures r S) (c : ℝ≥0) :
  ∥ F ∥ ≤ c → ∀ (s : S) (n : ℤ), (c : ℝ) < (r : ℝ)^n → F s n = 0 :=
begin
  intros hF s n h,
  suffices : ∥ F s n ∥ < 1,
  { change abs (F s n : ℝ) < 1 at this,
    norm_cast at this,
    rwa ← int.eq_zero_iff_abs_lt_one },
  have : ∥ F s n ∥ * r ^ n ≤ ∑' k, ∥ F s k ∥ * r ^ k,
  { apply le_tsum (F.summable s),
    rintros k -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r },
  replace this := lt_of_le_of_lt (le_trans this _) h,
  have hr₁ : 0 < (r : ℝ)^n := lt_of_le_of_lt (nnreal.coe_nonneg c) h,
  have hr₂ : (r: ℝ)^n ≠ 0 := ne_of_gt hr₁,
  convert mul_lt_mul this (le_refl ((r : ℝ) ^ n)⁻¹) _ _,
  { field_simp [hr₂] },
  { field_simp [hr₂] },
  { simp [hr₁] },
  { exact le_of_lt hr₁ },
  { refine le_trans _ hF,
    apply @finset.single_le_sum S ℝ _ (λ s, ∑' n, ∥ F s n ∥ * (r : ℝ)^n),
    { rintros s -,
      dsimp,
      apply tsum_nonneg,
      intros k,
      refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
      exact nnreal.coe_nonneg r },
    { simp } }
end

section profinite_structure

def index_category := ulift (ℤ × ℤ)

def index_category.fst : index_category → ℤ := λ a, a.down.fst
def index_category.snd : index_category → ℤ := λ a, a.down.snd

@[ext] lemma index_category.ext (A B : index_category) :
  A.fst = B.fst → A.snd = B.snd → A = B :=
begin
  rintro h h',
  ext,
  { exact h },
  { exact h' }
end

-- A ≤ B implies Icc B.fst B.snd ⊆ Icc A.fst A.snd
instance : partial_order index_category :=
{ le := λ A B, A.fst ≤ B.fst ∧ B.snd ≤ A.snd,
  --lt := _,
  le_refl := λ a, ⟨le_refl _, le_refl _⟩,
  le_trans := λ a b c h₁ h₂, ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩,
  le_antisymm := λ a b h₁ h₂, begin
    ext,
    { exact le_antisymm h₁.1 h₂.1 },
    { exact le_antisymm h₂.2 h₁.2 }
  end }

def truncate {c : ℝ≥0} (A : index_category) :
  { F : oc_measures r S | ∥ F ∥ ≤ c } → oc_measures_bdd r S A.fst A.snd c := λ F,
{ to_fun := λ s i, F s i,
  bound' := begin
    refine le_trans _ F.2,
    dsimp,
    apply finset.sum_le_sum,
    rintros s -,
    let T : finset ℤ := finset.univ.image (coe : set.Icc A.fst A.snd → ℤ),
    convert sum_le_tsum T _ ((F : oc_measures r S).summable s) using 1,
    { rw finset.sum_image,
      intros x hx y hy h,
      exact subtype.ext h },
    { intros b hb,
      refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
      exact nnreal.coe_nonneg r },
  end }

lemma eq_iff_truncate_eq (c : ℝ≥0) (F G : {F : oc_measures r S | ∥ F ∥ ≤ c}) :
  (∀ k, truncate k F = truncate k G) → F = G :=
begin
  intros h,
  ext s i,
  specialize h ⟨⟨i, i⟩⟩,
  apply_fun (λ e, e s ⟨i, le_refl _, le_refl _⟩) at h,
  exact h,
end


def Icc_transition {A B : index_category} (h : A ≤ B) :
  set.Icc B.fst B.snd → set.Icc A.fst A.snd := λ i,
⟨i, le_trans h.1 i.2.1, le_trans i.2.2 h.2⟩

def transition {c : ℝ≥0} {A B : index_category} (h : A ≤ B) :
  oc_measures_bdd r S A.fst A.snd c → oc_measures_bdd r S B.fst B.snd c := λ F,
⟨λ s i, F s (Icc_transition h i), begin
  refine le_trans _ F.2,
  apply finset.sum_le_sum,
  rintros s -,
  have : ∑ i : set.Icc B.fst B.snd, ∥ F s (Icc_transition h i) ∥ * (r : ℝ)^(i : ℤ) =
    ∑ i in finset.univ.image (Icc_transition h), ∥ F s i ∥ * (r : ℝ)^(i : ℤ),
  { rw finset.sum_image,
    { refl },
    { rintros i - j - hh,
      apply subtype.ext,
      apply_fun (λ e, e.val) at hh,
      exact hh } },
  rw this, clear this,
  apply finset.sum_le_sum_of_subset_of_nonneg,
  { apply finset.subset_univ },
  { rintros i - -,
    refine mul_nonneg (norm_nonneg _) (fpow_nonneg _ _),
    exact nnreal.coe_nonneg r }
end⟩

def index_category.single : ℤ → index_category := λ i, ⟨⟨i,i⟩⟩

lemma index_category.mem_single {i} :
  i ∈ set.Icc (index_category.single i).fst (index_category.single i).snd :=
⟨le_refl _, le_refl _⟩

def mk_seq {c} (F : Π (A : index_category), oc_measures_bdd r S A.fst A.snd c) :
  S → ℤ → ℤ := λ s i, F (index_category.single i) s ⟨i, index_category.mem_single⟩

lemma mk_seq_compat {c} (F : Π (A : index_category), oc_measures_bdd r S A.fst A.snd c)
  (compat : ∀ (A B : index_category) (h : A ≤ B), transition h (F _) = F _) (s : S)
  (A : index_category) (i : set.Icc A.fst A.snd) : mk_seq F s i = F A s i :=
begin
  have : A ≤ index_category.single i := ⟨i.2.1, i.2.2⟩,
  specialize compat _ _ this,
  dsimp [mk_seq],
  rw ← compat,
  change (F A) s _ = _,
  congr,
  ext,
  refl,
end

lemma mk_seq_compat_summable {c} (F : Π (A : index_category), oc_measures_bdd r S A.fst A.snd c)
  (compat : ∀ (A B : index_category) (h : A ≤ B), transition h (F _) = F _) (s : S) :
  summable (λ k : ℤ, ∥ mk_seq F s k ∥ * (r : ℝ)^k) := sorry

lemma mk_seq_compat_sum_le {c} (F : Π (A : index_category), oc_measures_bdd r S A.fst A.snd c)
  (compat : ∀ (A B : index_category) (h : A ≤ B), transition h (F _) = F _)  :
  ∑ (s : S), ∑' (k : ℤ), ∥ mk_seq F s k ∥ * (r : ℝ)^k ≤ c := sorry

lemma exists_of_compat {c} (F : Π (A : index_category), oc_measures_bdd r S A.fst A.snd c)
  (compat : ∀ (A B : index_category) (h : A ≤ B),
    transition h (F _) = F _) :
  ∃ (G : {H : oc_measures r S | ∥ H ∥ ≤ c }), ∀ (k : index_category), truncate k G = F k :=
begin
  let G : oc_measures r S := ⟨mk_seq F, mk_seq_compat_summable _ compat⟩,
  use G,
  { apply mk_seq_compat_sum_le _ compat },
  { intros k,
    ext s i,
    change F _ _ _ = _,
    have := compat k ⟨⟨i, i⟩⟩ ⟨i.2.1,i.2.2⟩,
    apply_fun (λ e, e s ⟨i, le_refl _, le_refl _⟩) at this,
    erw ← this,
    change F k _ _ = F k _ _,
    congr,
    ext, refl }
end

variables (r S)
def oc_measures_bdd_functor (c : ℝ≥0) [fact (0 < r)] : index_category ⥤ Fintype :=
{ obj := λ A, Fintype.of $ oc_measures_bdd r S A.fst A.snd c,
  map := λ A B f, transition $ category_theory.le_of_hom f }

def oc_measures_bdd_equiv (c : ℝ≥0) [fact (0 < r)] : { F : oc_measures r S | ∥ F ∥ ≤ c } ≃
  (Profinite.limit_cone (oc_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
equiv.of_bijective (λ F, ⟨λ A, truncate A F, begin
  intros A B f,
  ext,
  refl,
end⟩)
begin
  split,
  { intros F G h,
    apply eq_iff_truncate_eq,
    intros k,
    apply_fun (λ e, e.1 k) at h,
    exact h },
  { rintros ⟨F, hF⟩,
    dsimp at F hF,
    obtain ⟨G,hG⟩ := exists_of_compat F _,
    { use G,
      ext : 2,
      apply hG },
    { intros A B h,
      apply hF (category_theory.hom_of_le h) } }
end

instance (c : ℝ≥0) [fact (0 < r)] : topological_space {F : oc_measures r S | ∥ F ∥ ≤ c} :=
topological_space.induced (oc_measures_bdd_equiv r S c) infer_instance

def oc_measures_bdd_homeo (c : ℝ≥0) [fact (0 < r)] : { F : oc_measures r S | ∥ F ∥ ≤ c } ≃ₜ
  (Profinite.limit_cone (oc_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X :=
{ continuous_to_fun := continuous_induced_dom,
  continuous_inv_fun := begin
    have : inducing (oc_measures_bdd_equiv r S c) := ⟨rfl⟩,
    rw this.continuous_iff,
    dsimp,
    convert continuous_id,
    ext,
    simp,
  end,
  ..(oc_measures_bdd_equiv _ _ _) }

instance (c : ℝ≥0) [fact (0 < r)] : t2_space { F : oc_measures r S | ∥ F ∥ ≤ c } :=
⟨λ x y h, separated_by_continuous (oc_measures_bdd_homeo r S c).continuous
(λ cc, h $ by simpa using congr_arg (oc_measures_bdd_homeo r S c).symm cc)⟩

instance (c : ℝ≥0) [fact (0 < r)] : totally_disconnected_space
  { F : oc_measures r S | ∥ F ∥ ≤ c } :=
begin
  constructor,
  rintros A - hA,
  suffices : ((oc_measures_bdd_homeo r S c) '' A).subsingleton,
  { intros x hx y hy,
    apply_rules [(oc_measures_bdd_homeo r S c).injective, this, set.mem_image_of_mem] },
  obtain ⟨h⟩ := (infer_instance : totally_disconnected_space
   (Profinite.limit_cone (oc_measures_bdd_functor r S c ⋙ Fintype.to_Profinite)).X),
  refine h _ (by tauto) (is_preconnected.image hA _ _),
  exact (oc_measures_bdd_homeo r S c).continuous.continuous_on,
end

instance (c : ℝ≥0) [fact (0 < r)] : compact_space {F : oc_measures r S | ∥ F ∥ ≤ c} :=
begin
  constructor,
  rw (oc_measures_bdd_homeo r S c).embedding.is_compact_iff_is_compact_image,
  simp [compact_univ],
end

@[continuity]
lemma truncate_continuous (c : ℝ≥0) [fact (0 < r)] (A : index_category.{u}) :
  continuous (truncate A : _ → oc_measures_bdd r S _ _ c) :=
begin
  let g₁ :=
    (Profinite.limit_cone (oc_measures_bdd_functor.{u} r S c ⋙ Fintype.to_Profinite)).π.app A,
  let g₂ := (oc_measures_bdd_homeo r S c),
  change continuous (g₁ ∘ g₂),
  continuity,
end

lemma continuous_iff (c : ℝ≥0) [fact (0 < r)] {α : Type*} [topological_space α]
  (f : α → { F : oc_measures r S | ∥ F ∥ ≤ c }) :
  continuous f ↔ ∀ (A : index_category.{u}), continuous ((truncate A) ∘ f) :=
begin
  split,
  { intros hf A, continuity },
  { intros h,
    rw ← (oc_measures_bdd_homeo r S c).comp_continuous_iff,
    apply continuous_subtype_mk,
    apply continuous_pi,
    exact h }
end

end profinite_structure

/-
--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → oc_measures r S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma oc_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : oc_measures r S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := sorry
-/

--needed?
instance pnf_oc_measures : pseudo_normed_group (oc_measures r S) :=
{ filtration := λ c, { F | ∥ F ∥ ≤ c },
  filtration_mono := λ c₁ c₂ h F hF, by {dsimp at *, exact le_trans hF h},
  zero_mem_filtration := λ c, by simp,
  neg_mem_filtration := λ c F h, by {dsimp at *, simp [h]},
  add_mem_filtration := λ c₁ c₂ F₁ F₂ h₁ h₂, begin
    refine le_trans (norm_add _ _) _,
    rw nnreal.coe_add,
    exact add_le_add h₁ h₂,
  end }

instance pfpng_oc_measures [fact (0 < r)] :
  profinitely_filtered_pseudo_normed_group (oc_measures r S) :=
{ continuous_add' := begin
    intros c₁ c₂,
    rw continuous_iff,
    intros A,
    let E : oc_measures_bdd r S A.fst A.snd c₁ × oc_measures_bdd r S A.fst A.snd c₂ →
      oc_measures_bdd r S A.fst A.snd (c₁ + c₂) := λ G, ⟨G.1 + G.2, _⟩,
    swap, {
      rw nnreal.coe_add,
      refine le_trans _ (add_le_add G.fst.2 G.snd.2),
      rw ← finset.sum_add_distrib,
      apply finset.sum_le_sum,
      intros i hi,
      rw ← finset.sum_add_distrib,
      apply finset.sum_le_sum,
      intros j hj,
      rw ← add_mul,
      refine mul_le_mul (norm_add_le _ _) (le_refl _)
        (fpow_nonneg (nnreal.coe_nonneg _) _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) },
    have :
      (truncate A : _ → oc_measures_bdd r S A.fst A.snd (c₁ + c₂)) ∘ pseudo_normed_group.add' =
      E ∘ (prod.map (truncate A) (truncate A)),
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply continuous.prod_map,
      all_goals {apply truncate_continuous} }
  end,
  continuous_neg' := begin
    intros c,
    rw continuous_iff,
    intros A,
    let E : oc_measures_bdd r S A.fst A.snd c → oc_measures_bdd r S A.fst A.snd c :=
      λ G, ⟨- G, _⟩,
    swap, {
      convert G.2 using 1,
      apply finset.sum_congr rfl,
      intros s hs,
      apply finset.sum_congr rfl,
      intros x hx,
      congr' 1,
      simpa },
    have : (truncate A : _ → oc_measures_bdd r S A.fst A.snd c) ∘ pseudo_normed_group.neg' =
      E ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  continuous_cast_le := begin
    introsI c₁ c₂ h,
    rw continuous_iff,
    intros A,
    let g : oc_measures_bdd r S A.fst A.snd c₁ → oc_measures_bdd r S A.fst A.snd c₂ :=
      λ g, ⟨g, le_trans g.2 h.out⟩,
    have : (truncate A : _ → oc_measures_bdd r S A.fst A.snd c₂) ∘ pseudo_normed_group.cast_le =
      g ∘ truncate A,
    { ext, refl },
    rw this,
    apply continuous.comp,
    { exact continuous_of_discrete_topology },
    { apply truncate_continuous }
  end,
  ..(infer_instance : (pseudo_normed_group (oc_measures r S))) }

variable {α : Type*}

/-
def oc_functor (r : ℝ≥0) : Fintype.{u} ⥤ ProFiltPseuNormGrp.{u} :=
{ obj := λ S, ProFiltPseuNormGrp.of $ oc_measures r S,
  map := λ S T f,
  { to_fun := _,
    map_zero' := _,
    map_add' := _,
    bound' := _,
    continuous' := _ },
  map_id' := _,
  map_comp' := _ }
-/

end definitions
