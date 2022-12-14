import condensed.top_comparison
import solid.discrete
import category_theory.adjunction.basic
--import tactic.fin_cases

open category_theory
open category_theory.adjunction
open Profinite
open opposite

noncomputable theory

universes u v

instance topology_ulift (X : Type u) [topological_space X] : topological_space (ulift.{u+1 u} X) :=
  topological_space.coinduced ulift.up.{u+1 u} _inst_1

lemma ulift_up_continuous (X : Type u) [topological_space X] :
  continuous (ulift.up.{u+1 u} : X → ulift.{u+1 u} X) :=
  continuous_coinduced_rng

lemma ulift_down_continuous (X : Type u) [topological_space X] :
  continuous (ulift.down.{u+1 u} : ulift.{u+1 u} X → X) :=
begin
  have : topological_space.coinduced ulift.up.{u+1 u} =
    topological_space.induced ulift.down.{u+1 u} :=
    (equiv.induced_symm (⟨ulift.up.{u+1 u}, ulift.down.{u+1 u},
    ulift.down_up, ulift.up_down⟩ : X ≃ ulift.{u+1 u} X)).symm,
  have h : topology_ulift X = topological_space.induced ulift.down.{u+1 u} _inst_1,
  { rw ← this,
    refl },
  rw h,
  exact continuous_induced_dom,
end

lemma ulift_down_inducing (X : Type u) [topological_space X] :
  inducing (ulift.down.{u+1 u} :  ulift.{u+1 u} X → X) :=
{ induced := congr_fun ((equiv.induced_symm (⟨ulift.up.{u+1 u}, ulift.down.{u+1 u},
    ulift.down_up, ulift.up_down⟩ : X ≃ ulift.{u+1 u} X)).symm) _inst_1 }

def ulift_down_embedding (X : Type u) [topological_space X] :
  embedding (ulift.down.{u+1 u} : ulift.{u+1 u} X → X) :=
  ⟨ulift_down_inducing X, ulift.down_injective⟩

def Top_ulift : Top.{u} ⥤ Top.{u+1} :=
{
  obj := λ X, ⟨ulift.{u+1 u} X.α, topology_ulift X.α⟩,
  map := λ X Y f, ⟨ulift.up.{u+1 u} ∘ f ∘ ulift.down.{u+1 u}, continuous.comp
    (ulift_up_continuous Y.α) (continuous.comp f.continuous_to_fun (ulift_down_continuous X.α))⟩,
}

instance compact_of_ulift (X : Profinite.{u}) :
  compact_space (Top_ulift.{u}.obj (Profinite.to_Top.obj X)) :=
begin
  haveI hc : compact_space (Profinite.to_Top.obj X) := CompHaus.compact_space,
  have hcr := is_compact_range (ulift_up_continuous.{u} (Profinite.to_Top.obj X)),
  fconstructor,
  suffices h : (set.univ : set (Top_ulift.{u}.obj (Profinite.to_Top.obj X))) =
    set.range ulift.up.{u+1 u},
  { rw h, exact hcr, },
  have hs : function.surjective (ulift.up.{u+1 u} : Profinite.to_Top.obj X →
    Top_ulift.obj (Profinite.to_Top.obj X)) :=
    ulift.up_surjective,
  ext,
  split,
  { intros hx,
    obtain ⟨t,hs'⟩ := hs x,
    rw ← hs',
    tauto },
  tauto,
end

instance t2_of_ulift (X : Profinite.{u}) :
  t2_space (Top_ulift.{u}.obj (Profinite.to_Top.obj X)) :=
begin
  haveI : t2_space (Profinite.to_Top.obj X) := CompHaus.t2_space,
  exact embedding.t2_space (ulift_down_embedding X),
end

instance tot_disc_of_ulift (X : Profinite.{u}) :
  totally_disconnected_space (Top_ulift.{u}.obj (Profinite.to_Top.obj X)) :=
begin
  haveI : totally_disconnected_space (Profinite.to_Top.obj X) := X.is_totally_disconnected,
  have hi : is_totally_disconnected ((ulift.down.{u+1 u} '' set.univ) : set (Profinite.to_Top.obj X)) :=
    is_totally_disconnected_of_totally_disconnected_space _,
  exact ⟨embedding.is_totally_disconnected (ulift_down_embedding X) hi⟩,
end

def Profinite_ulift : Profinite.{u} ⥤ Profinite.{u+1} :=
{
  obj := λ X, Profinite.of (Top_ulift.{u}.obj (Profinite.to_Top.obj X)),
  map := λ X Y f, Top_ulift.map f,
}

lemma Profinite_ulift_map_to_pullback_cond {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  (Profinite_ulift.{u}.map (pullback.fst f g)) ≫ (Profinite_ulift.{u}.map f) =
  (Profinite_ulift.{u}.map (pullback.snd f g)) ≫ (Profinite_ulift.{u}.map g) :=
begin
  rw ← Profinite_ulift.map_comp' _ _,
  rw ← Profinite_ulift.map_comp' _ _,
  rw pullback.condition _ _,
end

def Profinite_ulift_map_to_pullback {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  Profinite_ulift.{u}.obj (pullback f g) ⟶ pullback (Profinite_ulift.{u}.map f)
  (Profinite_ulift.{u}.map g) :=
  pullback.lift _ _ _ _ (Profinite_ulift_map_to_pullback_cond f g)

instance Profinite_ulift_map_to_pullback_is_epi {X B : Profinite.{u}} (f g : X ⟶ B) :
  epi (Profinite_ulift_map_to_pullback f g) :=
begin
  refine (Profinite.epi_iff_surjective (Profinite_ulift_map_to_pullback f g)).mpr _,
  intros x,
  have h : f (ulift.down.{u+1 u} x.1.1) = g (ulift.down.{u+1 u} x.1.2),
  { cases x,
    cases x_val,
    cases x_val_snd,
    cases x_val_fst,
    dsimp at *,
    injections_and_clear,
    assumption },
  use ulift.up.{u+1 u} ⟨⟨(ulift.down.{u+1 u} x.1.1), (ulift.down.{u+1 u} x.1.2)⟩, h⟩,
  cases x,
  cases x_val,
  cases x_val_snd,
  cases x_val_fst,
  refl,
end

instance to_Top_Profinite_ulift_map_pullback_is_epi {X B : Profinite.{u}} (f g : X ⟶ B) :
  epi $ to_Top.map $ Profinite_ulift_map_to_pullback f g :=
(Top.epi_iff_surjective (Profinite_ulift_map_to_pullback f g)).mpr
  ((Profinite.epi_iff_surjective (Profinite_ulift_map_to_pullback f g)).mp
  (Profinite_ulift_map_to_pullback_is_epi f g))

lemma Profinite_ulift_fst {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  (Profinite_ulift_map_to_pullback f g) ≫ pullback.fst _ _ =
  (Profinite_ulift.{u}.map (pullback.fst f g)) :=
  pullback.lift_fst _ _ _ _ (Profinite_ulift_map_to_pullback_cond f g)

lemma Profinite_ulift_snd {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  (Profinite_ulift_map_to_pullback f g) ≫ pullback.snd _ _ =
  (Profinite_ulift.{u}.map (pullback.snd f g)) :=
  pullback.lift_snd _ _ _ _ (Profinite_ulift_map_to_pullback_cond f g)

instance Profinite_ulift_faithful : faithful Profinite_ulift.{u} :=
{ map_injective' := begin
    intros X Y f g h,
    have hf : (Profinite_ulift.map f).to_fun = ulift.up.{u+1 u} ∘ f ∘ ulift.down.{u+1 u} := by refl,
    have hg : (Profinite_ulift.map g).to_fun = ulift.up.{u+1 u} ∘ g ∘ ulift.down.{u+1 u} := by refl,
    apply_fun (λ x, x.to_fun) at h,
    rw hf at h,
    rw hg at h,
    ext,
    obtain ⟨a', hh⟩ := ulift.down_surjective a,
    rw function.funext_iff at h,
    have h' := h a',
    norm_num at h',
    rw hh at h',
    exact h',
  end, }

instance Profinite_ulift_to_Top_faithful : faithful (Profinite_ulift.{u} ⋙ to_Top.{u+1}) :=
  faithful.comp Profinite_ulift to_Top

instance Profinite_ulift_full : full Profinite_ulift.{u} :=
begin
  have h : ∀ (X Y : Profinite.{u}), function.surjective (Profinite_ulift.{u}.map : (X ⟶ Y) →
    (Profinite_ulift.obj X ⟶ Profinite_ulift.obj Y)),
  intros X Y f,
  let a := ulift.down.{u+1 u} ∘ f ∘ ulift.up.{u+1 u},
  have ha : continuous a := continuous.comp (ulift_down_continuous Y.to_CompHaus.to_Top.α)
    (continuous.comp f.continuous_to_fun (ulift_up_continuous X.to_CompHaus.to_Top.α)),
  use ⟨a, ha⟩,
  ext,
  norm_num,
  have hf : ∀ (X Y : Profinite.{u}) (i : X ⟶ Y),
    (Profinite_ulift.map i).to_fun = ulift.up.{u+1 u} ∘ i ∘ ulift.down.{u+1 u} :=
    by { intros X Y i, refl },
  have hfidX := hf X X (𝟙 X),
  rw Profinite_ulift.{u}.map_id' X at hfidX,
  dsimp at hfidX,
  have hfidY := hf Y Y (𝟙 Y),
  rw Profinite_ulift.{u}.map_id' Y at hfidY,
  dsimp at hfidY,
  dsimp,
  have : ⇑(Profinite_ulift.map {to_fun := a, continuous_to_fun := ha}) =
    ulift.up.{u+1 u} ∘  a ∘ ulift.down.{u+1 u} := hf X Y ⟨a, ha⟩,
  rw this,
  have hfa : a = ulift.down.{u+1 u} ∘ f ∘ ulift.up.{u+1 u} := by refl,
  rw hfa,
  rw ← function.comp.assoc ulift.up _ ulift.down,
  rw ← function.comp.assoc ulift.up ulift.down (f ∘ ulift.up),
  rw ← hfidY,
  rw function.comp.assoc id _ ulift.down,
  rw function.comp.assoc f ulift.up ulift.down,
  rw ← hfidX,
  simp only [eq_self_iff_true, function.comp.right_id, function.comp.left_id],
  exact category_theory.functor.full_of_surjective _ h,
end

instance Profinite_ulift_to_Top_full : full (Profinite_ulift.{u} ⋙ to_Top.{u+1}) :=
  full.comp Profinite_ulift to_Top

-- Version of Top.to_Condensed without the universe bump. Proof just needs slight modifications.
def Top_ulift_to_Condensed_obj (T : Top.{u+1}) : CondensedSet.{u} :=
{ val := Profinite_ulift.{u}.op ⋙ Profinite.to_Top.op ⋙ yoneda'.{u+1}.obj T,
  cond := begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae
      (Profinite_ulift.{u}.op ⋙ Profinite.to_Top.op ⋙ yoneda'.{u+1}.obj T)).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      split,
      { rintros _ _ _,
        ext ⟨⟨⟩⟩ },
      { intros x,
        dsimp,
        refine ⟨⟨⟨λ x, x.down.elim, by continuity⟩⟩, _⟩,
        ext } },
    { intros X Y,
      split,
      { intros x y h,
        dsimp at x y h,
        ext (t|t),
        { apply_fun (λ e, e.fst.down (ulift.up.{u+1 u} t)) at h, exact h },
        { apply_fun (λ e, e.snd.down (ulift.up.{u+1 u} t)) at h, exact h } },
      { rintros ⟨⟨a⟩,⟨b⟩⟩,
        dsimp [ulift_functor] at a b,
        let fa : X → Top_ulift.obj X.to_CompHaus.to_Top := λ x, ⟨x⟩,
        have hfa : continuous fa := by tidy,
        let fb : Y → Top_ulift.obj Y.to_CompHaus.to_Top := λ x, ⟨x⟩,
        have hfb : continuous fb := by tidy,
        refine ⟨⟨⟨_,_⟩⟩,_⟩,
        { dsimp [Profinite.sum],
          intros t,
          exact sum.rec_on t.down (a ∘ fa) (b ∘ fb) },
        { simp only [auto_param_eq, id.def, continuous_sup_dom],
          refine continuous.comp _ continuous_coinduced_rng,
          simp only [continuous_sup_dom, continuous_coinduced_dom],
          have ha := continuous.comp a.continuous hfa,
          have hb := continuous.comp b.continuous hfb,
          exact ⟨ha, hb⟩ },
        { simp only [Profinite.to_Top_map,
            quiver.hom.unop_op,
            id.def,
            category_theory.functor.comp_map,
            prod.mk.inj_iff,
            category_theory.functor.op_map],
          split,
          { dsimp,
            simp only [ulift.up_inj],
            ext1, cases a_1, refl },
          dsimp, simp only [ulift.up_inj],
          ext1, cases a_1, refl } } },
    { intros X B π hh,
      have hh' : function.surjective (Profinite_ulift.map π) :=
        (function.surjective.of_comp_iff ulift.up
        ((function.surjective.of_comp_iff π ulift.down_surjective).mpr hh)).mpr
        ulift.up_surjective,
      split,
      { intros x y h,
        dsimp [yoneda, functor.map_to_equalizer] at h,
        ext t,
        dsimp only [Profinite.to_Top_obj, opposite.unop_op, category_theory.functor.op_obj] at t,
        obtain ⟨t, rfl⟩ := hh' t,
        apply_fun (λ e, e.val.down t) at h,
        exact h },
      { rintros ⟨⟨t⟩,ht⟩,
        dsimp only [opposite.unop_op, category_theory.functor.op_obj, yoneda] at t,
        refine ⟨⟨Profinite.descend_to_Top (Profinite_ulift.map π) t hh' _⟩, _⟩,
        dsimp [-to_Top_map] at ht,
        apply_fun (λ e, e.down) at ht,
        rw ← Profinite_ulift_fst π π at ht,
        rw ← Profinite_ulift_snd π π at ht,
        rw to_Top.map_comp' at ht,
        rw to_Top.map_comp' at ht,
        simp only [category.assoc'] at ht,
        exact epi.left_cancellation _ _ ht,
        dsimp [yoneda, ulift_functor, functor.map_to_equalizer],
        ext : 2,
        dsimp,
        apply Profinite.π_descend_to_Top,
    } }
  end }

@[simps]
def Top_ulift_to_Condensed : Top.{u+1} ⥤ CondensedSet.{u} :=
{ obj := λ X, Top_ulift_to_Condensed_obj X,
  map := λ X Y f, ⟨whisker_left _ $ whisker_left _ $ whisker_right (yoneda.map f) _⟩,
  map_id' := begin
    intros X,
    ext1,
    dsimp,
    erw [yoneda.map_id, whisker_right_id, whisker_left_id],
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    ext1,
    dsimp,
    erw [yoneda.map_comp, whisker_right_comp, whisker_left_comp],
  end }

def Type_to_Condensed : Type (u+1) ⥤ CondensedSet.{u} :=
  Top.discrete ⋙ Top_ulift_to_Condensed

def Condensed_to_Type : CondensedSet.{u} ⥤ Type (u+1) := CondensedSet.evaluation point

instance : faithful Top_ulift_to_Condensed := sorry
instance : full Type_to_Condensed := sorry
instance : faithful Type_to_Condensed := sorry

def evaluate_at_point_equiv_of_condensed (Y : CondensedSet.{u}) :
  Y.val.obj (opposite.op point) ≃ Condensed_to_Type.obj Y := by refl

def evaluate_at_point_equiv_of_type (X : Type (u+1)) :
  (Type_to_Condensed.obj X).val.obj (opposite.op point) ≃ X :=
{ to_fun := λ f, f.down.to_fun ⟨punit.star⟩,
  inv_fun := λ x, ⟨⟨λ f, x⟩⟩,
  left_inv := by tidy,
  right_inv := by tidy, } .

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

instance (S : Profinite.{u+1}) : compact_space (to_Top.obj S) := S.to_CompHaus.is_compact

instance compact_of_Profinite_ulift (S : Profinite.{u}) :
  compact_space ((Profinite_ulift ⋙ to_Top).obj S) :=
  (Profinite_ulift.obj S).to_CompHaus.is_compact

instance t2_of_Profinite_ulift (S : Profinite.{u}) :
  t2_space ((Profinite_ulift ⋙ to_Top).obj S) :=
  (Profinite_ulift.obj S).to_CompHaus.is_hausdorff

instance totally_disconnected_of_Profinite_ulift (S : Profinite.{u}) :
  totally_disconnected_space ((Profinite_ulift ⋙ to_Top).obj S) :=
  (Profinite_ulift.obj S).is_totally_disconnected

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

lemma parts_of_map_cover_Profinite {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  S = Profinite.sigma (parts_of_map_as_Profinite f) := sorry

lemma parts_of_map_cover_Profinite' {S : Profinite.{u}} {X : Top.{u+1}} [discrete_topology X]
  (f : (Profinite_ulift ⋙ to_Top).obj S ⟶ X) :
  Profinite_ulift.obj S = Profinite.sigma (parts_of_map_as_Profinite'.{u} f) := sorry

-- set_option pp.universes true

def map_for_counit {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) : X.val.obj S :=
begin
  let f' := f.down,
  let g := parts_of_map_as_Profinite f.down,
  have h := parts_of_map_cover_Profinite f.down,
  apply_fun op at h,
  simp at h,
  change (parts_of_map_as_Profinite f.down) with g at h,
  rw h,
  let i := (λ (t : X.val.obj (op (Profinite.sigma g))),
    ((λ a, X.val.map (Profinite.sigma.ι g a).op t) :
    Π (a : (set_range_as_type_u f.down)), X.val.obj (op (g a)))),
  have : function.bijective i := product_condition_general_finite X g,
  let e := equiv.of_bijective i this,
  equiv_rw e,
  intros a,
  let pmap : g a → point := (equiv.arrow_punit_equiv_punit (g a)).inv_fun punit.star,
  have hp : continuous pmap := continuous_const,
  let p : g a ⟶ point := ⟨pmap, hp⟩,
  apply X.val.map p.op,
  let x := ((set_range_as_type_u_equiv f.down).inv_fun ∘ ulift.down.{u 0}) a,
  let x' : Top.discrete.obj (Condensed_to_Type.obj X) := x,
  exact x',
end

def for_counit₁ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  set_range_as_type_u f.down → Profinite.{u} :=
  parts_of_map_as_Profinite f.down

lemma for_counit₂ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  S = op (sigma (for_counit₁ f)) :=
begin
  have h := parts_of_map_cover_Profinite f.down,
  apply_fun op at h,
  simp only [opposite.op_unop] at h,
  exact h,
end

def for_counit₂b {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  X.val.obj (op (sigma (for_counit₁ f))) → X.val.obj S := X.val.map (eq_to_hom (for_counit₂ f).symm)

def for_counit₃ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  X.val.obj (op (sigma (for_counit₁ f))) ≃
  Π (a : set_range_as_type_u f.down), X.val.obj (op ((for_counit₁ f) a)) :=
  equiv.of_bijective _ (product_condition_general_finite X (for_counit₁ f))

def for_counit₄ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  Π (a : set_range_as_type_u f.down), (for_counit₁ f) a ⟶ point :=
  λ a, ⟨(equiv.arrow_punit_equiv_punit ((for_counit₁ f) a)).inv_fun punit.star, continuous_const⟩

def map_for_counit' {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ} :
  (((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) → X.val.obj S :=
λ f, (for_counit₂b f) ((for_counit₃ f).inv_fun (λ a, X.val.map (for_counit₄ f a).op
    ((coe (((set_range_as_type_u_equiv f.down).inv_fun ∘ ulift.down.{u 0}) a)) :
    Top.discrete.obj (Condensed_to_Type.obj X))))

def Condensed_Type_hom_equiv : core_hom_equiv Type_to_Condensed Condensed_to_Type :=
{ hom_equiv := λ X T,
  { to_fun := λ f, (evaluate_at_point_equiv_of_type X).inv_fun ≫ (f.val.app $ opposite.op point) ≫
      (evaluate_at_point_equiv_of_condensed T).to_fun,
    inv_fun := sorry,
    left_inv := sorry,
    right_inv := sorry, },
  hom_equiv_naturality_left_symm' := sorry,
  hom_equiv_naturality_right' := sorry, }

def Condensed_Type_adjunction : Type_to_Condensed ⊣ Condensed_to_Type :=
  mk_of_unit_counit
  { unit := { app := λ X, (λ x, ⟨⟨λ f, x⟩⟩), },
    counit := { app := λ X, { val := { app:= λ S, (as_hom map_for_counit'),
      naturality' := begin
        intros S T g,
        unfold map_for_counit',
        dsimp,
        sorry,
      end, },}, }, }
  -- mk_of_hom_equiv Condensed_Type_hom_equiv

instance glob_sec_preserves_limits :
  limits.preserves_limits (CondensedSet.evaluation point) := by apply_instance

instance : limits.preserves_limits Condensed_to_Type := glob_sec_preserves_limits

def is_discrete (X: CondensedSet.{u}) : Prop :=
  ∃ (Y : Type (u+1)) (h : (Type_to_Condensed.obj Y) ⟶ X), is_iso h

def is_discrete_stronger (X : CondensedSet.{u}) : Prop :=
  is_iso ((counit Condensed_Type_adjunction).app X)
