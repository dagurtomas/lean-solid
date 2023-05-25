import discrete.extend_equiv_rke
import discrete.loc_const_colim

noncomputable theory

universe u

open category_theory
open Profinite
open opposite
open Fintype
open category_theory.limits

-- I get a weird bytecode error without the `noncomputable!` modifier
noncomputable! def fin_yoneda (X : Type (u+1)) : Fintype.{u}ᵒᵖ  ⥤ Type (u+1) :=
{ obj := λ Y, (unop Y) → X,
  map := λ Y Z f g z, g (f.unop z), }

set_option pp.universes true

instance has_colimits_for_Lan (S : Profinite.{u}ᵒᵖ) : has_colimits_of_shape
  (costructured_arrow to_Profinite.op S) (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u+1} (Type (u+1)) := by apply_instance,
  haveI : has_colimits_of_size.{u u+1} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u+1 u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (costructured_arrow to_Profinite.op S),
end

instance has_colimits_for_Lan₂ (S : Profinite.{u}) : has_colimits_of_shape
  (structured_arrow S to_Profinite)ᵒᵖ (Type (u+1)) :=
has_colimits_of_shape_of_equivalence (structured_arrow_op_equivalence to_Profinite S).symm

set_option pp.universes false

def loc_const_of_fintype_map {Y : Fintype.{u}ᵒᵖ} {X : Type (u+1)} (f : (unop Y) → X) :
  locally_constant ((unop (to_Profinite.op.obj Y) : Profinite)) X :=
{ to_fun := f,
  is_locally_constant :=
  begin
    rw is_locally_constant.iff_continuous_bot,
    continuity,
  end }

def fin_yoneda_to_loc_const (X : Type (u+1)) : fin_yoneda X ⟶
  to_Profinite.op ⋙ loc_const_presheaf X :=
{ app := λ Y f, loc_const_of_fintype_map f,
  naturality' :=
  begin
    intros Y Z f,
    ext g z,
    dsimp [fin_yoneda, loc_const_of_fintype_map, loc_const_presheaf],
    rw locally_constant.coe_comap _ _ (to_Profinite.map f.unop).continuous,
    dsimp,
    refl,
  end } .

def loc_const_to_fin_yoneda (X : Type (u+1)) : to_Profinite.op ⋙ loc_const_presheaf X ⟶
  fin_yoneda X :=
{ app := λ Y f, f.to_fun,
  naturality' :=
  begin
    intros Y Z f,
    ext g z,
    dsimp [fin_yoneda, loc_const_presheaf],
    rw locally_constant.coe_comap _ _ (to_Profinite.map f.unop).continuous,
    dsimp,
    refl,
  end }

def fin_yoneda_iso_loc_const (X : Type (u+1)) : fin_yoneda X ≅
  to_Profinite.op ⋙ loc_const_presheaf X :=
{ hom := fin_yoneda_to_loc_const X,
  inv := loc_const_to_fin_yoneda X,
  hom_inv_id' :=
  begin
    ext Y f y,
    dsimp [fin_yoneda_to_loc_const, loc_const_to_fin_yoneda],
    refl,
  end,
  inv_hom_id' :=
  begin
    ext Y f y,
    dsimp [fin_yoneda_to_loc_const, loc_const_to_fin_yoneda],
    refl,
  end } .

def sa_proj_op_triangle (S : Profinite.{u}) :
  ((structured_arrow_op_equivalence to_Profinite S).functor ⋙
  costructured_arrow.proj to_Profinite.op (op S)) ≅
  (structured_arrow.proj S to_Profinite).op := iso.refl _

def sa_proj_op_whiskered_triangle (S : Profinite.{u}) (X : Type (u+1)) :
  (structured_arrow_op_equivalence to_Profinite S).functor ⋙
  costructured_arrow.proj to_Profinite.op (op S) ⋙ (fin_yoneda X) ≅
  (structured_arrow.proj S to_Profinite).op ⋙ (fin_yoneda X) := iso.refl _
-- (functor.associator _ _ _).symm ≪≫ iso_whisker_right (sa_proj_op_triangle S) (fin_yoneda X)

def functors_lke_map (S : Profinite.{u}) :
  (structured_arrow.proj S to_Profinite).op ⟶
  (sa_dq_functor S).op ⋙ S.fintype_diagram.op :=
nat_trans.op (functors_extend_rke_nat_trans S)

def functors_lke_iso_aux (S : Profinite.{u}) :
  (dq_sa_functor S).op ⋙ (sa_dq_functor S).op ⋙ S.fintype_diagram.op ≅
  (dq_sa_functor S).op ⋙ (structured_arrow.proj S to_Profinite).op :=
(nat_iso.op (functors_extend_rke_iso_aux.{u} S)).symm

def functors_lke_iso (S : Profinite.{u}) (X : Type (u+1)) :
  (dq_sa_functor S).op ⋙ (sa_dq_functor S).op ⋙ S.fintype_diagram.op ⋙ (fin_yoneda X) ≅
  (dq_sa_functor S).op ⋙ (structured_arrow.proj S to_Profinite).op ⋙ (fin_yoneda X) :=
(functor.associator (dq_sa_functor S).op ((sa_dq_functor S).op ⋙ S.fintype_diagram.op)
  (fin_yoneda X)).symm ≪≫ (iso_whisker_right (functors_lke_iso_aux S) (fin_yoneda X)) ≪≫
  (functor.associator (dq_sa_functor S).op (structured_arrow.proj S to_Profinite).op (fin_yoneda X))

def colimits_iso1 (S : Profinite.{u}) (X : Type (u+1)) :
  colimit ((sa_dq_functor S).op ⋙ S.fintype_diagram.op ⋙ (fin_yoneda X)) ≅
  colimit ((dq_sa_functor S).op ⋙ (sa_dq_functor S).op ⋙ S.fintype_diagram.op ⋙ (fin_yoneda X)) :=
(functor.final.colimit_iso (dq_sa_functor S).op _).symm

def colimits_iso2 (S : Profinite.{u}) (X : Type (u+1)) :
  colimit ((dq_sa_functor S).op ⋙ (sa_dq_functor S).op ⋙ S.fintype_diagram.op ⋙ (fin_yoneda X)) ≅
  colimit ((dq_sa_functor S).op ⋙ (structured_arrow.proj S to_Profinite).op ⋙ (fin_yoneda X)) :=
has_colimit.iso_of_nat_iso (functors_lke_iso S X)

def colimits_iso3 (S : Profinite.{u}) (X : Type (u+1)) :
  colimit ((dq_sa_functor S).op ⋙ (structured_arrow.proj S to_Profinite).op ⋙ (fin_yoneda X)) ≅
  colimit ((structured_arrow.proj S to_Profinite).op ⋙ (fin_yoneda X)) :=
functor.final.colimit_iso (dq_sa_functor S).op _

lemma colimits123 (S : Profinite.{u}) (X : Type (u+1)) :
  ((colimits_iso3 S X).inv ≫ (colimits_iso2 _ _).inv) ≫ (colimits_iso1 _ _).inv =
  colim.map (whisker_right (functors_lke_map S) (fin_yoneda X)) :=
begin
  rw ← iso.cancel_iso_hom_left (colimits_iso3 S X) _ _,
  simp only [← category.assoc, category.id_comp, iso.hom_inv_id],
  dsimp [colimits_iso1, colimits_iso2, colimits_iso3],
  ext1,
  dsimp [functor.final.colimit_iso],
  simp only [has_colimit.iso_of_nat_iso_ι_inv_assoc, whisker_right_app,
    colimit.ι_map, colimit.ι_pre, colimit.ι_pre_assoc],
  dsimp [functors_lke_iso, functors_lke_iso_aux, functors_lke_map],
  dsimp [functors_extend_rke_iso_aux, functors_extend_rke_nat_trans],
  simp only [category.comp_id, category.id_comp],
end

def lan_presheaf (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  (Lan to_Profinite.op).obj (fin_yoneda X)

def lan_presheaf_iso_loc_const_presheaf (X : Type (u+1)) : lan_presheaf X ≅ loc_const_presheaf X :=
nat_iso.of_components (λ S,
(begin
  dsimp [loc_const_presheaf],
  let e := loc_const_iso_colimit S.unop X,
  refine _ ≪≫ e.symm,
  dsimp [lan_presheaf, Lan],
  change (unop S).diagram.op with (unop S).fintype_diagram.op ⋙ to_Profinite.op,
  change Lan.diagram to_Profinite.op (fin_yoneda X) S with
    costructured_arrow.proj to_Profinite.op S ⋙ (fin_yoneda X),
  let f := has_colimit.iso_of_nat_iso (iso_whisker_left (unop S).fintype_diagram.op
    (fin_yoneda_iso_loc_const X)),
  refine _ ≪≫ f,
  rw ← op_unop S,
  rw unop_op (unop S),
  let g := has_colimit.iso_of_equivalence (structured_arrow_op_equivalence to_Profinite (unop S))
    (sa_proj_op_whiskered_triangle (unop S) X),
  refine g.symm ≪≫ _,
  let h := functor.final.colimit_iso (sa_dq_functor (unop S)).op
    ((unop S).fintype_diagram.op ⋙ (fin_yoneda X)),
  refine _ ≪≫ h,
  exact ((colimits_iso1 (unop S) X) ≪≫ (colimits_iso2 (unop S) X) ≪≫
    (colimits_iso3 (unop S) X)).symm,
end))
(begin
  dsimp,
  intros S T f,
  rw colimits123 (unop S) X,
  rw colimits123 (unop T) X,
  dsimp [functor.final.colimit_iso],
  dsimp [loc_const_iso_colimit, can_from_colim_loc_const, equiv.of_bijective],
  simp only [equiv.symm_symm],
  dsimp,
  change (unop S).diagram.op ⋙ (loc_const_presheaf X) with
    (unop S).fintype_diagram.op ⋙ to_Profinite.op ⋙ (loc_const_presheaf X),
  change (unop T).diagram.op ⋙ (loc_const_presheaf X) with
    (unop T).fintype_diagram.op ⋙ to_Profinite.op ⋙ (loc_const_presheaf X),
  simp only [category_theory.limits.has_colimit.iso_of_nat_iso_hom_desc,
    category_theory.limits.colimit.pre_desc,
    category_theory.limits.colimit.map_desc,
    category_theory.category.assoc],
  dsimp [sa_proj_op_whiskered_triangle],
  dsimp [lan_presheaf],
  dsimp [has_colimit.iso_of_equivalence],
  simp only [category_theory.limits.colimit.pre_desc_assoc],
  dsimp [loc_const_presheaf],
  ext1,
  simp only [whisker_left_twice, category.comp_id, cocone.whisker_ι,
    colimit.cocone_ι, quiver.hom.unop_op,
    colimit.ι_desc_assoc, cocones.precompose_obj_ι,
    whisker_right_app, equivalence.equivalence_mk'_counit_inv,
    whisker_left_app, nat_trans.comp_app, category_theory.functor.comp_map,
    costructured_arrow.proj_map, category_theory.equivalence.inv_fun_id_assoc_inv_app,
    colimit.ι_desc, category.assoc, nat_trans.naturality_assoc,
    category_theory.functor.op_map, whisker_left_comp],
  change costructured_arrow.map f ⋙ Lan.diagram to_Profinite.op (fin_yoneda X) T with
    Lan.diagram to_Profinite.op (fin_yoneda X) S,
  simp only [whisker_left_twice, category.comp_id,
    cocone.whisker_ι, colimit.cocone_ι,
    quiver.hom.unop_op, colimit.ι_desc_assoc, cocones.precompose_obj_ι,
    whisker_right_app, category_theory.equivalence.equivalence_mk'_counit_inv,
    whisker_left_app, nat_trans.comp_app,
    category_theory.functor.comp_map, costructured_arrow.proj_map,
    category_theory.equivalence.inv_fun_id_assoc_inv_app, category.assoc,
    nat_trans.naturality_assoc, category_theory.functor.op_map, whisker_left_comp],
  congr' 2,
  dsimp [loc_const_as_cocone],
  simp only [← category.assoc, types_comp],
  rw locally_constant.comap_comp f.unop _ f.unop.continuous (discrete_quotient.proj_continuous _),
  rw locally_constant.comap_comp ((sa_dq_functor (unop T)).obj (unop
    ((structured_arrow_op_equivalence to_Profinite (unop T)).inverse.obj
    ((costructured_arrow.map f).obj j)))).proj _ (discrete_quotient.proj_continuous _)
    (continuous_map.continuous _),
  rw locally_constant.comap_comp _ _ (continuous.comp (discrete_quotient.proj_continuous _)
    f.unop.continuous) (continuous_map.continuous _),
  congr' 1,
  ext,
  dsimp [functors_lke_map, functors_extend_rke_nat_trans,
    hom_to_dq_to_right, proj_bot_inv],
  congr,
end) .

def lan_CondensedSet (X : Type (u+1)) : CondensedSet.{u} :=
{ val := lan_presheaf X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    exact presieve.is_sheaf_iso _ (lan_presheaf_iso_loc_const_presheaf X).symm
      ((is_sheaf_iff_is_sheaf_of_type _ _).mp (loc_const_CondensedSet X).cond),
  end }
