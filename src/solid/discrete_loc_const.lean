import solid.discrete_condensed
import solid.discrete
import topology.locally_constant.algebra

noncomputable theory

universe u

open category_theory
open category_theory.limits
open Profinite
open Condensed

def loc_const_presheaf (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
{ obj := λ S, locally_constant S.unop X,
  map := λ S T f, locally_constant.comap f.unop,
  map_id' :=
  begin
    intro S,
    exact locally_constant.comap_id,
  end,
  map_comp' :=
  begin
    intros S T U f g,
    exact (locally_constant.comap_comp _ _ g.unop.continuous f.unop.continuous).symm,
  end  }

namespace Profinite

def descend_to_Type {X B : Profinite.{u}} {Y : Type (u+1)} (π : X ⟶ B) (t : locally_constant X Y)
  (hπ : function.surjective π)
  (w : locally_constant.comap (pullback.fst π π) t =
    locally_constant.comap (pullback.snd π π) t) : locally_constant B Y :=
{ to_fun := (λ i, quotient.lift_on' i t begin
    rintros a b (h : π _ = π _),
    apply_fun (λ e, e ⟨(a,b),h⟩) at w,
    rw locally_constant.coe_comap (pullback.fst π π) _ (pullback.fst π π).continuous at w,
    rw locally_constant.coe_comap (pullback.snd π π) _ (pullback.snd π π).continuous at w,
    exact w,
  end : quotient (setoid.ker π) → Y) ∘ (Profinite.quotient_map π hπ).homeomorph.symm,
  is_locally_constant := begin
    apply is_locally_constant.comp_continuous,
    { letI : topological_space Y := ⊥,
      haveI : discrete_topology Y := {eq_bot := rfl},
      rw @is_locally_constant.iff_continuous _ _ _ _inst _inst_1,
      apply continuous_quot_lift, exact t.continuous, },
    { exact (quotient_map π hπ).homeomorph.symm.continuous },
  end }

lemma π_descend_to_Type {X B : Profinite.{u}} {Y : Type (u+1)} (π : X ⟶ B) (t : locally_constant X Y)
  (hπ : function.surjective π)
  (w : locally_constant.comap (pullback.fst π π) t =
    locally_constant.comap (pullback.snd π π) t) :
  locally_constant.comap π (Profinite.descend_to_Type π t hπ w) = t :=
begin
  ext i,
  rw locally_constant.coe_comap π _ π.continuous,
  dsimp [descend_to_Type, setoid.quotient_ker_equiv_of_surjective,
    setoid.quotient_ker_equiv_of_right_inverse, quotient_map.homeomorph],
  let c : pullback π π := ⟨(function.surj_inv hπ (π i), i), function.surj_inv_eq hπ (π i)⟩,
  apply_fun (λ e, e c) at w,
  rw locally_constant.coe_comap (pullback.fst π π) _ (pullback.fst π π).continuous at w,
  rw locally_constant.coe_comap (pullback.snd π π) _ (pullback.snd π π).continuous at w,
  exact w,
end

end Profinite

def loc_const_CondensedSet (X : Type (u+1)) : CondensedSet.{u} :=
{ val := loc_const_presheaf X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae
      (loc_const_presheaf X)).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      split,
      { rintros _ _ _,
        ext ⟨⟩ },
      { intros x,
        dsimp [loc_const_presheaf],
        let a : locally_constant ↥empty X := ⟨pempty.elim, (λ s, is_open_discrete _)⟩,
        use a,
        exact (punit_eq_star _).symm, } },
    { intros S T,
      split,
      { intros f g h,
        dsimp at *,
        ext (t|t),
        { apply_fun (λ e, e.fst.to_fun t) at h,
          dsimp [loc_const_presheaf] at *,
          rw locally_constant.coe_comap (Profinite.sum.inl S T) _ continuous_inl at h,
          rw locally_constant.coe_comap (Profinite.sum.inl S T) _ continuous_inl at h,
          exact h, },
        { apply_fun (λ e, e.snd.to_fun t) at h,
          dsimp [loc_const_presheaf] at *,
          rw locally_constant.coe_comap (Profinite.sum.inr S T) _ continuous_inr at h,
          rw locally_constant.coe_comap (Profinite.sum.inr S T) _ continuous_inr at h,
          exact h, }, },
      { rintros ⟨a,b⟩,
        dsimp [loc_const_presheaf] at a b,
        refine ⟨⟨_,_⟩,_⟩,
        { dsimp [Profinite.sum],
          intros t,
          exact sum.rec_on t a.to_fun b.to_fun },
        { dsimp,
          intro s,
          have ha := a.is_locally_constant s,
          have hb := b.is_locally_constant s,
          rw is_open_sum_iff,
          exact ⟨ha, hb⟩, },
        { ext,
          { dsimp [loc_const_presheaf],
            rw locally_constant.coe_comap (Profinite.sum.inl S T) _ continuous_inl,
            refl },
          { dsimp [loc_const_presheaf],
            rw locally_constant.coe_comap (Profinite.sum.inr S T) _ continuous_inr,
            refl } } } },
    { intros S B π hh,
      split,
      { intros x y h,
        dsimp [functor.map_to_equalizer] at h,
        dsimp [loc_const_presheaf] at h,
        ext t,
        obtain ⟨t, rfl⟩ := hh t,
        apply_fun (λ e, e.val.to_fun t) at h,
        simp only [locally_constant.to_fun_eq_coe] at h,
        rw locally_constant.coe_comap π _ π.continuous at h,
        rw locally_constant.coe_comap π _ π.continuous at h,
        exact h },
      { rintros ⟨t, ht⟩,
        dsimp [functor.map_to_equalizer],
        dsimp [loc_const_presheaf] at *,
        use Profinite.descend_to_Type π t hh ht,
        congr,
        exact Profinite.π_descend_to_Type π t hh ht } }
  end}

def loc_const_Condensed_functor : Type (u+1) ⥤ CondensedSet.{u} :=
{ obj := loc_const_CondensedSet,
  map := λ X Y f, { val :=
  { app := λ S t, ⟨f ∘ t.to_fun, is_locally_constant.comp t.is_locally_constant _⟩,
    naturality' :=
    begin
      intros S T g,
      dsimp [loc_const_CondensedSet],
      dsimp [loc_const_presheaf],
      ext,
      simp only [category_theory.types_comp_apply, function.comp_app, locally_constant.coe_mk],
      rw locally_constant.coe_comap g.unop _ g.unop.continuous,
      rw locally_constant.coe_comap g.unop _ g.unop.continuous,
      refl,
    end, } },
  map_id' :=
  begin
    intro S,
    dsimp [loc_const_CondensedSet],
    dsimp [loc_const_presheaf],
    ext,
    simp only [function.comp_app,
      Sheaf.hom.id_val,
      locally_constant.coe_mk,
      nat_trans.id_app,
      types_id_apply],
  end,
  map_comp' :=
  begin
    intros S T U f g,
    dsimp [loc_const_CondensedSet],
    dsimp [loc_const_presheaf],
    ext,
    simp only [types_comp_apply,
      Sheaf.category_theory.category_comp_val,
      function.comp_app,
      category_theory.functor_to_types.comp,
      locally_constant.coe_mk],
  end, } .

variables (A : Type (u+1)) [ring A]

lemma comap_map_add {S T : Profinite.{u}} (f : S ⟶ T) (X : Module.{u+1} A)
  (x y : locally_constant T X) :
  locally_constant.comap f (x + y) = locally_constant.comap f x + locally_constant.comap f y :=
begin
  ext,
  rw locally_constant.coe_comap _ _ f.continuous,
  simp only [pi.add_apply, locally_constant.coe_add, function.comp_app],
  rw ← function.comp_app x f,
  rw ← locally_constant.coe_comap _ x f.continuous,
  rw ← function.comp_app y f,
  rw ← locally_constant.coe_comap _ y f.continuous,
end

lemma comap_map_smul {S T : Profinite.{u}} (f : S ⟶ T) (X : Module.{u+1} A)
  (r : A) (x : locally_constant T X) :
  locally_constant.comap f (r • x) = r • (locally_constant.comap f x) :=
begin
  ext,
  rw locally_constant.coe_comap _ _ f.continuous,
  simp only [ring_hom.id_apply, function.comp_app, locally_constant.coe_smul, pi.smul_apply],
  rw ← function.comp_app x f,
  rw ← locally_constant.coe_comap _ x f.continuous,
end

def loc_const_presheaf_Mod (X : Module.{u+1} A) : Profinite.{u}ᵒᵖ ⥤ Module.{u+1} A :=
{ obj := λ S,
  { carrier := locally_constant S.unop X,
    is_add_comm_group := locally_constant.add_comm_group,
    is_module := locally_constant.module},
  map := λ S T f,
  { to_fun := locally_constant.comap f.unop,
    map_add' := comap_map_add A f.unop X,
    map_smul' := comap_map_smul A f.unop X, },
  map_id' :=
  begin
    intro S,
    dsimp,
    simp only [locally_constant.comap_id],
    refl,
  end,
  map_comp' :=
  begin
    intros S T U f g,
    dsimp,
    ext,
    simp only [linear_map.coe_mk, function.comp_app, Module.coe_comp],
    rw ← locally_constant.comap_comp _ _ g.unop.continuous f.unop.continuous,
  end  }

#check presheaf.is_sheaf_iff_is_sheaf_forget
#check forget (Module.{u+1} A)

def loc_const_CondensedMod (X : Module.{u+1} A) : Condensed.{u} (Module.{u+1} A) :=
{ val := loc_const_presheaf_Mod A X,
  cond :=
  begin
    rw presheaf.is_sheaf_iff_is_sheaf_forget _ (loc_const_presheaf_Mod A X)
      (forget (Module.{u+1} A)),
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae
      (loc_const_presheaf_Mod A X ⋙ forget _)).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      split,
      { rintros _ _ _,
        ext ⟨⟩ },
      { intros x,
        dsimp,
        let a : locally_constant ↥empty X := ⟨pempty.elim, (λ s, is_open_discrete _)⟩,
        use a,
        exact (punit_eq_star _).symm, } },
    { intros S T,
      split,
      { intros f g h,
        dsimp at *,
        ext (t|t),
        { apply_fun (λ e, e.fst.to_fun t) at h,
          dsimp [loc_const_presheaf_Mod] at *,
          rw locally_constant.coe_comap (Profinite.sum.inl S T) _ continuous_inl at h,
          rw locally_constant.coe_comap (Profinite.sum.inl S T) _ continuous_inl at h,
          exact h, },
        { apply_fun (λ e, e.snd.to_fun t) at h,
          dsimp [loc_const_presheaf_Mod] at *,
          rw locally_constant.coe_comap (Profinite.sum.inr S T) _ continuous_inr at h,
          rw locally_constant.coe_comap (Profinite.sum.inr S T) _ continuous_inr at h,
          exact h, }, },
      { rintros ⟨a,b⟩,
        dsimp at a b,
        refine ⟨⟨_,_⟩,_⟩,
        { dsimp [Profinite.sum],
          intros t,
          exact sum.rec_on t a.to_fun b.to_fun },
        { dsimp,
          intro s,
          have ha := a.is_locally_constant s,
          have hb := b.is_locally_constant s,
          rw is_open_sum_iff,
          exact ⟨ha, hb⟩, },
        { ext,
          { dsimp [loc_const_presheaf_Mod],
            rw locally_constant.coe_comap (Profinite.sum.inl S T) _ continuous_inl,
            refl },
          { dsimp [loc_const_presheaf_Mod],
            rw locally_constant.coe_comap (Profinite.sum.inr S T) _ continuous_inr,
            refl } } } },
    { intros S B π hh,
      split,
      { intros x y h,
        dsimp [functor.map_to_equalizer] at h,
        dsimp [loc_const_presheaf_Mod] at h,
        ext t,
        obtain ⟨t, rfl⟩ := hh t,
        apply_fun (λ e, e.val.to_fun t) at h,
        simp only [locally_constant.to_fun_eq_coe] at h,
        rw locally_constant.coe_comap π _ π.continuous at h,
        rw locally_constant.coe_comap π _ π.continuous at h,
        exact h },
      { rintros ⟨t, ht⟩,
        dsimp [functor.map_to_equalizer],
        dsimp [loc_const_presheaf] at *,
        use Profinite.descend_to_Type π t hh ht,
        congr,
        exact Profinite.π_descend_to_Type π t hh ht } }
  end} .

def loc_const_CondensedMod_functor_map_app {X Y : Module.{u+1} A} (f : X ⟶ Y)
  (S : Profinite.{u}ᵒᵖ) :
  (loc_const_presheaf_Mod A X).obj S ⟶ (loc_const_presheaf_Mod A Y).obj S :=
{ to_fun := λ t, ⟨f ∘ t.to_fun, is_locally_constant.comp t.is_locally_constant _⟩,
  map_add' :=
  begin
    intros x y,
    ext,
    dsimp,
    simp only [map_add],
  end,
  map_smul' :=
  begin
    intros r x,
    ext,
    dsimp,
    simp only [map_smul],
  end, } .

def loc_const_CondensedMod_functor_map {X Y : Module.{u+1} A} (f : X ⟶ Y) :
  (loc_const_presheaf_Mod A X) ⟶ (loc_const_presheaf_Mod A Y) :=
{ app := loc_const_CondensedMod_functor_map_app A f,
  naturality' :=
  begin
      intros S T g,
      dsimp [loc_const_presheaf_Mod],
      dsimp [loc_const_CondensedMod_functor_map_app],
      ext,
      simp only [linear_map.coe_mk, function.comp_app, Module.coe_comp, locally_constant.coe_mk],
      rw locally_constant.coe_comap g.unop _ g.unop.continuous,
      rw locally_constant.coe_comap g.unop _ g.unop.continuous,
      dsimp,
      refl,
    end, } .

def loc_const_CondensedMod_functor : Module.{u+1} A ⥤ Condensed.{u} (Module.{u+1} A) :=
{ obj := loc_const_CondensedMod A,
  map := λ X Y f, { val := loc_const_CondensedMod_functor_map A f },
  map_id' :=
  begin
    intro S,
    dsimp [loc_const_CondensedMod_functor_map],
    ext,
    simp only [function.comp_app,
      Sheaf.hom.id_val,
      locally_constant.coe_mk,
      nat_trans.id_app,
      types_id_apply],
    dsimp [loc_const_CondensedMod_functor_map_app],
    refl,
  end,
  map_comp' :=
  begin
    intros S T U f g,
    dsimp [loc_const_CondensedMod_functor_map],
    ext,
    simp only [types_comp_apply,
      Sheaf.category_theory.category_comp_val,
      function.comp_app,
      category_theory.functor_to_types.comp,
      locally_constant.coe_mk],
    dsimp [loc_const_CondensedMod_functor_map_app],
    refl,
  end, } .

def loc_const_of_const {X : Type*} (x : X) :
  Condensed_to_Type.obj (loc_const_Condensed_functor.obj X) :=
{ to_fun := λ y, x,
  is_locally_constant := is_locally_constant.const _, }

def Type_to_Condensed_to_loc_const_Condensed_app (X : Type (u+1)) :
  Type_to_Condensed.obj X ⟶ loc_const_Condensed_functor.obj X :=
(Condensed_Type_adjunction.hom_equiv X (loc_const_Condensed_functor.obj X)).inv_fun
  loc_const_of_const

#exit

def Type_to_Condensed_to_loc_const_Condensed :
  Type_to_Condensed ⟶ loc_const_Condensed_functor :=
{ app := Type_to_Condensed_to_loc_const_Condensed_app,
  naturality' :=
  begin
    intros X Y f,
    -- dsimp [Type_to_Condensed,
    --   Type_to_Condensed_to_loc_const_Condensed_app,
    --   loc_const_Condensed_functor,
    --   loc_const_CondensedSet,
    --   loc_const_presheaf],
    dsimp [Type_to_Condensed_to_loc_const_Condensed_app],
    simp only [category.assoc, adjunction.hom_equiv_counit],
    dsimp [Condensed_Type_adjunction],
    dsimp [adjunction.comp],
    sorry,
  end}

/- TODO: Prove that Type_to_Condensed and loc_const_Condensed_functor are naturally isomorphic. -/

def Condensed_hom_equiv_presheaf_hom (X Y : CondensedSet.{u}) : (X ⟶ Y) ≃ (X.val ⟶ Y.val) :=
equiv_of_fully_faithful (Sheaf_to_presheaf _ _)

def yoneda'_equiv_condensed (X : CondensedSet.{u}) (T : Profinite.{u}) :
  X.val.obj (opposite.op T) ≃ (Profinite_to_Condensed.obj T ⟶ X) :=
equiv.trans (yoneda'_equiv.{u+1 u u+1} T X.val).symm
  (Condensed_hom_equiv_presheaf_hom (Profinite_to_Condensed.obj T) X).symm

def yoneda'_iso_condensed (X : CondensedSet.{u}) (T : Profinite.{u}) :
  X.val.obj (opposite.op T) ≅ (Profinite_to_Condensed.obj T ⟶ X) :=
equiv.to_iso.{u+1} (yoneda'_equiv_condensed _ _)

def Condensed_loc_const_hom_equiv : adjunction.core_hom_equiv loc_const_Condensed_functor
  Condensed_to_Type :=
{
  hom_equiv := λ X Y,
  begin

  end,
}

def Condensed_loc_const_adjunction : loc_const_Condensed_functor ⊣ Condensed_to_Type :=
sorry,


set_option pp.universes true

#check @can_map_from_colim_of_homs_to_hom_from_limit
variables (S : Profinite.{u}) (Si Sj : discrete_quotient S)
#check discrete_quotient S
#check Si ⟶ Sj
variables (X Y : CondensedSet.{u})
#check X ⟶ Y

lemma discreteness_condition_condensed (X : Type (u+1)) (S : Profinite.{u}) :
  is_iso (can_map_from_colim_of_homs_to_hom_from_limit.{u+2 u+1} (Type_to_Condensed.obj X) (S.diagram ⋙ (Profinite_to_Condensed : Profinite.{u} ⥤ CondensedSet.{u})))

def yoneda_nat_iso_condensed (X : CondensedSet.{u}) :
  X.val ≅ Profinite_to_Condensed.op ⋙ (yoneda.obj X) :=
sorry
