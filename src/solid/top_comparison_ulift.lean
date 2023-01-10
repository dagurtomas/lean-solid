import condensed.top_comparison
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

instance : faithful Top_ulift_to_Condensed := sorry
instance : full Type_to_Condensed := sorry
instance : faithful Type_to_Condensed := sorry
/- TODO : define compactly generated and prove that Top_ulift_to_Condensed is
ff when restricted to CG -/
