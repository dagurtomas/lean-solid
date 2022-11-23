import topology.connected

/-! Submitted to mathlib as PR #17070 -/

lemma preimage_subtype_coe_eq_compl {α : Type*} {s u v : set α} (hsuv : s ⊆ u ∪ v)
  (H : s ∩ (u ∩ v) = ∅) : (coe : s → α) ⁻¹' u = (coe ⁻¹' v)ᶜ :=
begin
ext ⟨x, x_in_s⟩,
split,
{ intros x_in_u x_in_v,
  exact set.eq_empty_iff_forall_not_mem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩ },
{ intro hx,
  exact or.elim (hsuv x_in_s) id (λ hx', hx.elim hx') }
end

open bool

namespace set
variables {α : Type*} (s : set α)

/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def bool_indicator (x : α) :=
@ite _ (x ∈ s) (classical.prop_decidable _) tt ff

lemma mem_iff_bool_indicator (x : α) : x ∈ s ↔ s.bool_indicator x = tt :=
by { unfold bool_indicator, split_ifs ; tauto }

lemma not_mem_iff_bool_indicator (x : α) : x ∉ s ↔ s.bool_indicator x = ff :=
by { unfold bool_indicator, split_ifs ; tauto }

lemma preimage_bool_indicator_tt : s.bool_indicator ⁻¹' {tt} = s :=
ext (λ x, (s.mem_iff_bool_indicator x).symm)

lemma preimage_bool_indicator_ff : s.bool_indicator ⁻¹' {ff} = sᶜ :=
ext (λ x, (s.not_mem_iff_bool_indicator x).symm)

open_locale classical

lemma preimage_bool_indicator_eq_union (t : set bool) :
  s.bool_indicator ⁻¹' t = (if tt ∈ t then s else ∅) ∪ (if ff ∈ t then sᶜ else ∅) :=
begin
  ext x,
  dsimp [bool_indicator],
  split_ifs ; tauto
end

lemma preimage_bool_indicator (t : set bool) :
  s.bool_indicator ⁻¹' t = univ ∨ s.bool_indicator ⁻¹' t = s ∨
  s.bool_indicator ⁻¹' t = sᶜ ∨ s.bool_indicator ⁻¹' t = ∅ :=
begin
  simp only [preimage_bool_indicator_eq_union],
  split_ifs ; simp [s.union_compl_self]
end

end set

section clopen

variables {X : Type*} [topological_space X]

lemma continuous_bool_indicator_iff_clopen (U : set X) :
  continuous U.bool_indicator ↔ is_clopen U :=
begin
  split,
  { intros hc,
    rw ← U.preimage_bool_indicator_tt,
    exact
      ⟨hc.is_open_preimage _ trivial, continuous_iff_is_closed.mp hc _ (is_closed_discrete _)⟩ },
  { refine λ hU, ⟨λ s hs, _⟩,
    rcases U.preimage_bool_indicator s with (h|h|h|h) ; rw h,
    exacts [is_open_univ, hU.1, hU.2.is_open_compl, is_open_empty] },
end

lemma continuous_on_indicator_iff_clopen (s U : set X) :
  continuous_on U.bool_indicator s ↔ is_clopen ((coe : s → X) ⁻¹' U) :=
begin
  rw [continuous_on_iff_continuous_restrict, ← continuous_bool_indicator_iff_clopen],
  refl
end

end clopen

section connected

variables {α : Type*} [topological_space α]

/-- A set `s` is preconnected if and only if every
map into `bool` that is continuous on `s` is constant on `s` -/
lemma is_preconnected.constant {Y : Type*} [topological_space Y] [discrete_topology Y]
  {s : set α} (hs : is_preconnected s) {f : α → Y} (hf : continuous_on f s)
  {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
(hs.image f hf).subsingleton (set.mem_image_of_mem f hx) (set.mem_image_of_mem f hy)

lemma is_preconnected_of_forall_constant {s : set α}
  (hs : ∀ f : α → bool, continuous_on f s → ∀ x ∈ s, ∀ y ∈ s, f x = f y) : is_preconnected s :=
begin
  unfold is_preconnected,
  by_contra',
  rcases this with ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩,
  rw [set.not_nonempty_iff_eq_empty] at H,
  have hy : y ∉ u,
    from λ y_in_u, set.eq_empty_iff_forall_not_mem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩,
  have : continuous_on u.bool_indicator s,
  { apply (continuous_on_indicator_iff_clopen _ _).mpr ⟨_, _⟩,
    { exact continuous_subtype_coe.is_open_preimage u u_op },
    { rw preimage_subtype_coe_eq_compl hsuv H,
      exact (continuous_subtype_coe.is_open_preimage v v_op).is_closed_compl } },
  simpa [(u.mem_iff_bool_indicator _).mp x_in_u, (u.not_mem_iff_bool_indicator _).mp hy] using
    hs _ this x x_in_s y y_in_s
end

lemma preconnected_space.constant {Y : Type*} [topological_space Y] [discrete_topology Y]
  (hp : preconnected_space α) {f : α → Y} (hf : continuous f) {x y : α} : f x = f y :=
is_preconnected.constant hp.is_preconnected_univ (continuous.continuous_on hf) trivial trivial

lemma preconnected_space_of_forall_constant (hs : ∀ f : α → bool, continuous f → ∀ x y, f x = f y) :
  preconnected_space α :=
⟨is_preconnected_of_forall_constant
  (λ f hf x hx y hy, hs f (continuous_iff_continuous_on_univ.mpr hf) x y)⟩

end connected