import solid.discrete_loc_const

noncomputable theory

universe u

open category_theory
open category_theory.limits
open Profinite

variables (S : Profinite.{u}) (X : Type (u+1))

def loc_const_as_cocone : cocone (S.diagram.op ⋙ loc_const_presheaf X) :=
{ X := locally_constant S X,
  ι := { app := λ i f, locally_constant.comap i.unop.proj f,
    naturality' :=
    begin
      intros i j ji,
      dsimp [loc_const_presheaf] at *,
      rw types_comp,
      simp only [category.comp_id],
      rw locally_constant.comap_comp _ _ j.unop.proj_continuous continuous_bot,
      congr,
    end } }

set_option pp.universes true

instance : has_colimits_of_shape (discrete_quotient S)ᵒᵖ (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u u} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (discrete_quotient S)ᵒᵖ,
end

set_option pp.universes false

def can_from_colim_loc_const : colimit (S.diagram.op ⋙ loc_const_presheaf X)
  ⟶ locally_constant S X :=
colimit.desc (S.diagram.op ⋙ loc_const_presheaf X) (loc_const_as_cocone S X)

theorem injective_can : function.injective (can_from_colim_loc_const S X) :=
begin
  intros a' b' h,
  obtain ⟨i, a, ha⟩ := types.jointly_surjective'.{u u+1} a',
  obtain ⟨j, b, hb⟩ := types.jointly_surjective'.{u u+1} b',
  rw ← ha,
  rw ← hb,
  obtain ⟨k, ki, kj, t⟩ := (category_theory.is_filtered_op_of_is_cofiltered
    (discrete_quotient S)).to_is_filtered_or_empty.cocone_objs i j,
  rw types.filtered_colimit.colimit_eq_iff.{u u+1},
  use k,
  use ki,
  use kj,
  dsimp [loc_const_presheaf],
  ext x',
  rw locally_constant.coe_comap _ _ continuous_bot,
  rw locally_constant.coe_comap _ _ continuous_bot,
  simp only [Fintype.to_Profinite_map_apply, function.comp_app],
  obtain ⟨x, hx⟩ := discrete_quotient.proj_surjective k.unop x',
  rw ← hx,
  have hki : S.fintype_diagram.map ki.unop (k.unop.proj x) = i.unop.proj x := by refl,
  rw hki,
  have hkj : S.fintype_diagram.map kj.unop (k.unop.proj x) = j.unop.proj x := by refl,
  rw hkj,
  rw ← ha at h,
  rw ← hb at h,
  dsimp [can_from_colim_loc_const] at h,
  rw ← types_comp_apply (colimit.ι (S.diagram.op ⋙ loc_const_presheaf X) i)
    (colimit.desc (S.diagram.op ⋙ loc_const_presheaf X) (loc_const_as_cocone S X)) a at h,
  simp only [colimit.ι_desc] at h,
  rw ← types_comp_apply (colimit.ι (S.diagram.op ⋙ loc_const_presheaf X) j)
    (colimit.desc (S.diagram.op ⋙ loc_const_presheaf X) (loc_const_as_cocone S X)) b at h,
  simp only [colimit.ι_desc] at h,
  dsimp [loc_const_as_cocone] at h,
  simp only [← locally_constant.to_fun_eq_coe],
  rw ← function.comp_apply a.to_fun i.unop.proj x,
  rw ← function.comp_apply b.to_fun j.unop.proj x,
  simp only [locally_constant.to_fun_eq_coe],
  rw ← locally_constant.coe_comap _ _ i.unop.proj_continuous,
  rw ← locally_constant.coe_comap _ _ j.unop.proj_continuous,
  congr,
  exact h,
end

theorem surjective_can : function.surjective (can_from_colim_loc_const S X) :=
begin
  intro f,
  obtain ⟨j, g, hg⟩ :=
    exists_locally_constant (S.as_limit_cone) S.as_limit f,
  use colimit.ι (S.diagram.op ⋙ loc_const_presheaf X) (opposite.op j) g,
  dsimp [can_from_colim_loc_const],
  rw ← types_comp_apply (colimit.ι (S.diagram.op ⋙ loc_const_presheaf X) (opposite.op j))
    (colimit.desc (S.diagram.op ⋙ loc_const_presheaf X) (loc_const_as_cocone S X)) g,
  simp only [category_theory.limits.colimit.ι_desc],
  dsimp [loc_const_as_cocone],
  rw hg,
  congr,
end
