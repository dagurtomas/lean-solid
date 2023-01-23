import solid.Profinite_ulift

open category_theory
open Profinite

noncomputable theory

universes u v

-- {X : Type u} {Y : Type v}

instance fintype_set_range_of_compact_to_discrete {X Y : Type*} {f : X → Y}
  [topological_space X] [topological_space Y] [discrete_topology Y] [compact_space X]
  (hf : continuous f) : fintype (set.range f) :=
  set.finite.fintype (is_compact_iff_finite.mp (is_compact_range hf))

def finset_range_of_map {X Y : Type*} {f : X → Y} [topological_space X]
  [topological_space Y] [discrete_topology Y] [compact_space X] (hf : continuous f) :
  finset Y := @set.to_finset Y (set.range f) (fintype_set_range_of_compact_to_discrete hf)

instance {X Y : Type*} (f : X → Y) (A : finset X) : fintype (f '' A) := fintype.of_finite (f '' A)

def parts_of_map {X Y : Type*} {f : X → Y} [topological_space X] [topological_space Y]
  [discrete_topology Y] [compact_space X] (hf : continuous f) : finset (set X) :=
  set.to_finset ((λ i, f ⁻¹' {i}) '' (finset_range_of_map hf))

-- def parts_of_map_as_set {X Y : Type*} {f : X → Y} [topological_space X] [topological_space Y]
--   [discrete_topology Y] [compact_space X] (hf : continuous f) : set (set X) :=
--   parts_of_map hf

instance {X Y : Type*} {f : X → Y} [topological_space X] [topological_space Y]
  [discrete_topology Y] [compact_space X] (hf : continuous f) : fintype (parts_of_map hf) :=
  fintype.of_finset (parts_of_map hf) (λ x, iff.rfl)

def funSX_of {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : S → X :=
  f.to_fun ∘ ulift.up.{u+1 u}

lemma cont_funSX_of {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : continuous (funSX_of f) :=
continuous.comp f.continuous_to_fun (ulift_up_continuous _)

instance part_compact {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (T : parts_of_map (cont_funSX_of f)) :
  compact_space T :=
begin
  cases T,
  dsimp,
  rw ← is_compact_iff_compact_space,
  unfold parts_of_map at T_property,
  simp only [set.mem_image, set.mem_to_finset] at T_property,
  obtain ⟨x, h⟩ := T_property,
  rw ← h.2,
  exact is_closed.is_compact (is_closed.preimage (cont_funSX_of f) (is_closed_discrete _)),
end

lemma Profinite_is_iso_iff_bijective {S T : Profinite.{u}} (f : S ⟶ T) :
  is_iso f ↔ function.bijective f :=
  ⟨by {introsI hf, exact concrete_category.bijective_of_is_iso f },
    λ hf, Profinite.is_iso_of_bijective f hf⟩

def map_parts_to_Profinite {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  parts_of_map (cont_funSX_of f) → Profinite.{u} :=
λ T, Profinite.of T

def Profinite_hom_sigma_of_parts {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : Profinite.sigma (map_parts_to_Profinite f) ⟶ S :=
Profinite.sigma.desc (map_parts_to_Profinite f) (λ T, ⟨((λ t, t) : T → S), by continuity⟩)

lemma is_iso_Profinite_hom_sigma_of_parts {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : is_iso (Profinite_hom_sigma_of_parts f) :=
begin
  rw Profinite_is_iso_iff_bijective _,
  split,
  { intros a b h,
    cases a,
    cases b,
    sorry, },
  intros s,
  sorry,
end

variables {X Y : Type*} {f : X → Y} [topological_space X] [topological_space Y]
  [discrete_topology Y] [compact_space X] (hf : continuous f)

#check parts_of_map hf
#check set X
#check set (set X)
#check finset (set X)
#check continuous f

#exit

def decompostition_disjoint_of_map {X Y : Top.{u}} [discrete_topology Y] (f : X ⟶ Y) : Top.{u} :=
  Top.of (Σ (i : set.range f), f ⁻¹' {i})

def map_of_decomposition_disjoint {X Y : Top.{u}} [discrete_topology Y] (Z : set Y)
  (h : Z → set X) : X ⟶ Y := sorry

instance {X Y : Top.{u}} [compact_space X] [discrete_topology Y] (f : X ⟶ Y) :
  fintype (set.range f) :=
  set.finite.fintype (is_compact_iff_finite.mp (is_compact_range f.continuous_to_fun))

def finset_range_of_map {X Y : Top.{u}} [compact_space X] [discrete_topology Y] (f : X ⟶ Y) :
  finset Y := set.to_finset (set.range f)

instance {X Y : Type*} (f : X → Y) (A : finset X) : fintype (f '' A) := fintype.of_finite (f '' A)

def parts_of_map {X Y : Top.{u}} [compact_space X] [discrete_topology Y] (f : X ⟶ Y) :
  finset (set X) := set.to_finset ((λ i, f ⁻¹' {i}) '' (finset_range_of_map f))

def finpartition_of_map {X Y : Top.{u}} [compact_space X] [discrete_topology Y] (f : X ⟶ Y) :
  finpartition (set.univ : set X) :=
{ parts := parts_of_map f,
  sup_indep := begin
    intros t ht A hA hnA x hx,
    cases hx,
    apply hnA,
    unfold parts_of_map at hA,
    simp only [set.mem_image, set.mem_to_finset] at hA,
    obtain ⟨y, hA'⟩ := hA,
    simp at hx_right,
    obtain ⟨B, hx'⟩ := hx_right,
    have hB := ht hx'.1,
    unfold parts_of_map at hB,
    simp only [set.mem_image, set.mem_to_finset] at hB,
    obtain ⟨y', hB'⟩ := hB,
    simp only [id.def] at hx_left,
    rw ← hA'.2 at hx_left,
    cases hx',
    rw ← hB'.2 at hx'_right,
    have : f x = y := hx_left,
    have h₁ : f x = y' := hx'_right,
    rw this at h₁,
    rw h₁ at hA',
    rw hA'.2 at hB',
    rw hB'.2,
    exact hx'_left,
  end,
  sup_parts := begin
    ext,
    split, { tauto },
    intros hx,
    simp only [set.mem_Union, finset.sup_set_eq_bUnion],
    use f ⁻¹' {f x},
    split,
    { unfold parts_of_map,
      simp only [set.mem_image, set.mem_to_finset],
      use f x,
      unfold finset_range_of_map,
      simp only [set.mem_range_self, eq_self_iff_true, and_self, set.coe_to_finset], },
    { tauto },
  end,
  not_bot_mem := begin
    simp only [set.bot_eq_empty],
    unfold parts_of_map,
    unfold finset_range_of_map,
    simp only [not_exists, set.mem_image,
      set.mem_to_finset,
      exists_exists_eq_and,
      set.coe_to_finset],
    intros y,
    intros hy,
    obtain ⟨x, hx⟩ := hy.1,
    have : x ∈ f ⁻¹' {y} := hx,
    rw hy.2 at this,
    exact this,
  end, }

lemma parts_of_map_clopen_Profinite {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} {Si : set _} (hSi : Si ∈ parts_of_map f) :
  is_clopen Si :=
begin
  unfold parts_of_map at hSi,
  simp at hSi,
  obtain ⟨x, h⟩ := hSi,
  rw ← h.2,
  exact ⟨continuous_def.mp f.continuous_to_fun {x} (is_open_discrete _),
    is_closed.preimage f.continuous_to_fun (is_closed_discrete _)⟩,
end

instance Profinite_set_range_fintype {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  fintype (set.range f) :=
  set.finite.fintype (is_compact_iff_finite.mp (is_compact_range f.continuous_to_fun))

instance {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} {x : X} (hx : x ∈ set.range f) :
  is_closed (f ⁻¹' {x}) := is_closed.preimage f.continuous_to_fun (is_closed_discrete _)

instance (S : Profinite.{u}) : totally_disconnected_space (to_Top.obj S).α :=
  S.is_totally_disconnected

instance fibre_totally_disconnected {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (x : set.range f) :
  totally_disconnected_space ((f ∘ ulift.up.{u+1 u}) ⁻¹' {x}) :=
  subtype.totally_disconnected_space

instance fibre_totally_disconnected' {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (x : set.range f) :
  totally_disconnected_space (f ⁻¹' {x}) :=
  subtype.totally_disconnected_space

instance (S : Profinite.{u}) : compact_space (to_Top.obj S).α :=
  S.to_CompHaus.is_compact

instance fibre_compact {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (x : set.range f) :
  compact_space ((f ∘ ulift.up.{u+1 u}) ⁻¹' {x}) :=
  is_compact_iff_compact_space.mp (is_closed.is_compact
  (is_closed.preimage (continuous.comp f.continuous_to_fun (ulift_up_continuous _))
  (is_closed_discrete _)))

instance fibre_compact' {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (x : set.range f) :
  compact_space (f ⁻¹' {x}) :=
  is_compact_iff_compact_space.mp (is_closed.is_compact
  (is_closed.preimage f.continuous_to_fun (is_closed_discrete _)))

instance (S : Profinite.{u}) : t2_space (to_Top.obj S).α :=
  S.to_CompHaus.is_hausdorff

instance fibre_hausdorff {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (x : set.range f) :
  t2_space ((f ∘ ulift.up.{u+1 u}) ⁻¹' {x}) := subtype.t2_space

instance fibre_hausdorff' {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (x : set.range f) :
  t2_space (f ⁻¹' {x}) := subtype.t2_space

def set_range_as_type_u {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : Type u :=
  ulift.{u} (fin (finite.exists_equiv_fin (set.range f)).some)

instance {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : fintype (set_range_as_type_u f) :=
  ulift.fintype _

def set_range_as_type_u_equiv {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  set.range f ≃ fin (classical.some (finite.exists_equiv_fin (set.range f))) :=
  (classical.some_spec (finite.exists_equiv_fin (set.range f))).some

def parts_of_map_as_Profinite₂ {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : (set.range f) → Profinite.{u} :=
  λ x, Profinite.of ((f ∘ ulift.up.{u+1 u}) ⁻¹' {x})

def parts_of_map_as_Profinite  {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : set_range_as_type_u f → Profinite.{u} :=
  (parts_of_map_as_Profinite₂ f) ∘ (set_range_as_type_u_equiv f).inv_fun ∘ ulift.down.{u 0}

def parts_of_map_as_Profinite' {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) : (set.range f) → Profinite.{u+1} :=
  λ x, Profinite.of (f ⁻¹' {x})

lemma product_condition_general_finite {α : Type u} (X : CondensedSet.{u}) [fintype α]
  (S : α → Profinite.{u}) : function.bijective (λ (t : X.val.obj (op $ Profinite.sigma S)),
  ((λ a, X.val.map (Profinite.sigma.ι S a).op t) : Π (a : α), X.val.obj $ op $ S a)) :=
begin
  -- basically done in condensed.is_proetale_sheaf:
  have : X.val.is_proetale_sheaf_of_types,
  { rw (functor.is_proetale_sheaf_of_types_tfae X.val).out 1 0,
    rw ← is_sheaf_iff_is_sheaf_of_type,
    exact X.cond },
  exact (functor.finite_product_condition_of_is_proetale_sheaf_of_types X.val this)
    (Fintype.of α) S
end

instance compact_of_closed_Profinite {S : Profinite.{u}} (C : set S) [is_closed C] :
  compact_space C := is_compact_iff_compact_space.mp (is_closed.is_compact _inst_1)

def ι_to_Profinite {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  {f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X} (a : set_range_as_type_u f) :
  parts_of_map_as_Profinite f a ⟶ S :=
  ⟨((λ x, x) : (ulift.up.{u+1 u} : S → Profinite_ulift.obj S) ⁻¹'
  (f ⁻¹' {(set_range_as_type_u_equiv f).inv_fun a.down}) → S), by continuity⟩

def map_for_iso_cover {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  sigma (parts_of_map_as_Profinite f) ⟶ S :=
  sigma.desc (parts_of_map_as_Profinite f) (λ a, ι_to_Profinite a)

instance sigma_parts_of_map_is_iso_Profinite_ulift {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  is_iso $ Profinite_ulift.map $ map_for_iso_cover f :=
  sorry

lemma Profinite_is_iso_iff_bijective {S T : Profinite.{u}} (f : S ⟶ T) :
  is_iso f ↔ function.bijective f :=
  ⟨by {introsI hf, exact concrete_category.bijective_of_is_iso f },
    λ hf, Profinite.is_iso_of_bijective f hf⟩

instance sigma_parts_of_map_is_iso_Profinite {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  is_iso $ map_for_iso_cover f :=
begin
  rw Profinite_is_iso_iff_bijective (map_for_iso_cover f),
  dsimp,
  split,
  { intros a b h, -- ⟨a, xa⟩ ⟨b, xb⟩ h,
    obtain ⟨xa, a', ha⟩ := sigma.ι_jointly_surjective (parts_of_map_as_Profinite f) a,
    obtain ⟨xb, b', hb⟩ := sigma.ι_jointly_surjective (parts_of_map_as_Profinite f) b,
    rw ← ha,
    rw ← hb,
    have : xa = xb := by sorry,
    rw this at a',
    cases a',
    -- change ⟨a'_val, a'_property⟩ with a',
    -- apply sigma.ι_injective,
    -- cases a,
    -- cases a_fst,
    -- cases b,
    -- cases b_fst,
    -- ext,
    sorry,
    -- simp only [],
    -- apply sigma.ι_injective,
     },
    -- obtain ⟨xa, a', ha⟩ := sigma.ι_jointly_surjective (parts_of_map_as_Profinite f) a,
    -- obtain ⟨xb, b', hb⟩ := sigma.ι_jointly_surjective (parts_of_map_as_Profinite f) b,
    -- rw ← ha,
    -- rw ← hb,
    -- unfold map_for_iso_cover at h,
    -- unfold sigma.desc at h, },
  { sorry, }
  -- unfold sigma.desc._match_1,
  -- unfold parts_of_map_as_Profinite,
  -- unfold ι_to_Profinite,
end
  -- is_iso_of_fully_faithful Profinite_ulift _

def parts_of_map_cover_Profinite {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  sigma (parts_of_map_as_Profinite f) ≅ S :=
  as_iso $ map_for_iso_cover f

lemma parts_of_map_cover_Profinite' {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  Profinite_ulift.obj S = Profinite.sigma (parts_of_map_as_Profinite'.{u} f) := sorry

-- set_option pp.universes true
