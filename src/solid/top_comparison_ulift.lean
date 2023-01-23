import category_theory.limits.presheaf
import condensed.top_comparison
import condensed.adjunctions
import solid.discrete
import solid.Profinite_ulift

open category_theory
open Profinite
open opposite

noncomputable theory

universes u v

/- Version of Top.to_Condensed without the universe bump. Proof just needs slight modifications. -/
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

@[simps] /- Functorial version of Top_ulift_to_Condensed_obj -/
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

-- set_option pp.universes true
-- variables (C : Type (u+1)) [category C]
-- variables (X Y : C)

-- #check X
-- #check X ⟶ Y

variables (X Y : Type u) [topological_space X] [topological_space Y]

#check C(X,Y)

-- #check Top.{u}
-- #check X.α
-- #check X ⟶ Y
-- #check @yoneda
-- #check (Profinite_ulift.{u} ⋙ to_Top.{u+1})
-- #check Top.{u+1}
-- #check Profinite.{u}
-- #check colimit_adj.restricted_yoneda.{u+1 u+2} (Profinite_ulift.{u} ⋙ to_Top.{u+1})

-- instance : small_category Profinite.{u} :=
-- begin
--   sorry,
-- end

-- instance : category.{u+1} Top.{u+1} := by apply_instance

def Profinite_to_presheaf : Profinite.{u} ⥤ Profinite.{u}ᵒᵖ ⥤ Type u := @yoneda Profinite.{u} _

-- def Type_to_Presheaf : Type u ⥤ Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
--   Top.discrete.{u} ⋙ colimit_adj.restricted_yoneda (Profinite_ulift.{u} ⋙ to_Top)


def Type_to_presheaf : Type (u+1) ⥤ Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  Top.discrete.{u+1} ⋙ yoneda ⋙ (whiskering_left _ _ (Type (u+1))).obj
  (functor.op (Profinite_ulift.{u} ⋙ to_Top))

lemma Type_to_presheaf_is_continuous_maps (X : Type (u+1)) [topological_space X]
  [discrete_topology X] (S : Profinite.{u}) :
  (Type_to_presheaf.obj X).obj (op S) = C(S,X) :=
begin
  unfold Type_to_presheaf,
  simp only [category_theory.yoneda_obj_obj,
    Profinite.to_Top_obj,
    category_theory.whiskering_left_obj_obj,
    opposite.unop_op,
    category_theory.functor.comp_obj,
    category_theory.functor.op_obj],
  unfold Profinite_ulift,
  dsimp,

  -- unfold C(S,X)
  -- dsimp,
  -- simp,
end


#exit

instance small_category_ulift (C : Type (u+1)) [large_category C] : small_category.{u+1} C :=
{ hom := λ A B, ulift.{u+1} $ A ⟶ B,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩, }

instance : small_category.{u+1} (Type u) := by apply_instance
instance : small_category.{u+1} Profinite.{u} := by apply_instance
instance : small_category.{u+1} Top.{u} := by apply_instance
instance : category.{u} Profinite.{u} := by apply_instance

-- (colimit_adj.restricted_yoneda.{u+1 u+1} (Profinite_ulift.{u} ⋙ to_Top))

lemma Type_to_Condensed_eq_Type_to_Presheaf_sheafified :
  Type_to_Condensed = Type_to_Presheaf ⋙ presheaf_to_CondensedSet := sorry

instance : faithful Top_ulift_to_Condensed := sorry
instance : full Type_to_Condensed := sorry
instance : faithful Type_to_Condensed := sorry
/- TODO : define compactly generated and prove that Top_ulift_to_Condensed is
ff when restricted to CG -/
