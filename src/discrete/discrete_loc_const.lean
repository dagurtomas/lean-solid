import discrete.discrete_condensed
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

def loc_const_map {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X) (p : X → Y) :
  locally_constant S Y :=
{ to_fun := p ∘ f, is_locally_constant := is_locally_constant.comp f.is_locally_constant _ }

def loc_const_Condensed_functor : Type (u+1) ⥤ CondensedSet.{u} :=
{ obj := loc_const_CondensedSet,
  map := λ X Y f, { val :=
  { app := λ S t, loc_const_map t f,
    naturality' :=
    begin
      intros S T g,
      dsimp [loc_const_CondensedSet],
      dsimp [loc_const_presheaf],
      dsimp [loc_const_map],
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
    dsimp [loc_const_map],
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
    dsimp [loc_const_map],
    ext,
    simp only [types_comp_apply,
      Sheaf.category_theory.category_comp_val,
      function.comp_app,
      category_theory.functor_to_types.comp,
      locally_constant.coe_mk],
  end, } .
