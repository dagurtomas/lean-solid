import topology.category.Profinite.as_limit
import topology.category.Profinite.cofiltered_limit
import condensed.adjunctions_module
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
  obtain ⟨j, g, hg⟩ := exists_locally_constant S.as_limit_cone S.as_limit f,
  use colimit.ι (S.diagram.op ⋙ loc_const_presheaf X) (opposite.op j) g,
  dsimp [can_from_colim_loc_const],
  rw ← types_comp_apply (colimit.ι (S.diagram.op ⋙ loc_const_presheaf X) (opposite.op j))
    (colimit.desc (S.diagram.op ⋙ loc_const_presheaf X) (loc_const_as_cocone S X)) g,
  simp only [category_theory.limits.colimit.ι_desc],
  dsimp [loc_const_as_cocone],
  rw hg,
  congr,
end

theorem bijective_can : function.bijective (can_from_colim_loc_const S X) :=
⟨injective_can _ _, surjective_can _ _⟩

def loc_const_iso_colimit : locally_constant S X ≅ colimit (S.diagram.op ⋙ loc_const_presheaf X) :=
  equiv.to_iso (equiv.of_bijective (can_from_colim_loc_const S X) (bijective_can S X)).symm

-- (loc_const_CondensedSet X).val.obj (opposite.op S)

def Condensed_hom_equiv_presheaf_hom (X Y : CondensedSet.{u}) : (X ⟶ Y) ≃ (X.val ⟶ Y.val) :=
equiv_of_fully_faithful (Sheaf_to_presheaf _ _)

def yoneda'_equiv_condensed (X : CondensedSet.{u}) (T : Profinite.{u}) :
  X.val.obj (opposite.op T) ≃ (Profinite_to_Condensed.obj T ⟶ X) :=
equiv.trans (yoneda'_equiv.{u+1 u u+1} T X.val).symm
  (Condensed_hom_equiv_presheaf_hom (Profinite_to_Condensed.obj T) X).symm

def yoneda'_iso_condensed (X : CondensedSet.{u}) (T : Profinite.{u}) :
  X.val.obj (opposite.op T) ≅ (Profinite_to_Condensed.obj T ⟶ X) :=
(yoneda'_equiv_condensed _ _).to_iso

-- : (Profinite_to_Condensed.obj S ⟶ loc_const_CondensedSet X) ≅
--   colimit (S.diagram.op ⋙ loc_const_presheaf X)

def discrete_condensed_hom_iso_colimit : (Profinite_to_Condensed.obj S ⟶ loc_const_CondensedSet X)
  ≅ (colimit (S.diagram.op ⋙ loc_const_presheaf X) : Type (u+1)) :=
((loc_const_iso_colimit S X).symm ≪≫ (yoneda'_iso_condensed (loc_const_CondensedSet X) S)).symm

variables (A : Type (u+1)) [ring A]

def Mod_presheaf_of_CondensedSet_with_module_inst (X : CondensedSet.{u})
  [∀ (T : Profinite.{u}ᵒᵖ), add_comm_group (X.val.obj T)]
  [∀ (T : Profinite.{u}ᵒᵖ), module A (X.val.obj T)]
  (h : ∀ (S T : Profinite.{u}ᵒᵖ) (f : S ⟶ T), is_linear_map A (X.val.map f)) :
  Profinite.{u}ᵒᵖ ⥤ (Module.{u+1} A) :=
{ obj := λ S,
  { carrier := X.val.obj S,
    is_add_comm_group := _inst_2 S,
    is_module := _inst_3 S },
  map := λ S T f,
  { to_fun := X.val.map f,
    map_add' := (h S T f).map_add,
    map_smul' := (h S T f).map_smul } } .

def CondensedMod_of_CondensedSet_with_module_inst (X : CondensedSet.{u})
  [∀ (T : Profinite.{u}ᵒᵖ), add_comm_group (X.val.obj T)]
  [∀ (T : Profinite.{u}ᵒᵖ), module A (X.val.obj T)]
  (h : ∀ (S T : Profinite.{u}ᵒᵖ) (f : S ⟶ T), is_linear_map A (X.val.map f)) :
  Condensed.{u} (Module.{u+1} A) :=
{ val := Mod_presheaf_of_CondensedSet_with_module_inst A X h,
  cond :=
  begin
    rw presheaf.is_sheaf_iff_is_sheaf_forget _
      (Mod_presheaf_of_CondensedSet_with_module_inst A X h)
      (forget (Module.{u+1} A)),
    exact X.cond,
  end }

#exit

instance (T : Profinite.{u}) : ∀ (S : Profinite.{u}ᵒᵖ), add_comm_group
  ((Profinite_to_Condensed.obj T).val.obj S) := sorry

instance (T : Profinite.{u}) : ∀ (S : Profinite.{u}ᵒᵖ), module A
  ((Profinite_to_Condensed.obj T).val.obj S) := sorry

lemma module_maps_profinite (T : Profinite.{u}) : ∀ (S W : Profinite.{u}ᵒᵖ) (f : S ⟶ W),
  is_linear_map A ((Profinite_to_Condensed.obj T).val.map f) := sorry

instance op_add_comm_group (T : Profinite.{u}ᵒᵖ) : ∀ (S : Profinite.{u}ᵒᵖ), add_comm_group
  ((Profinite_to_Condensed.obj T.unop).val.obj S) := sorry

instance op_module (T : Profinite.{u}ᵒᵖ) : ∀ (S : Profinite.{u}ᵒᵖ), module A
  ((Profinite_to_Condensed.obj T.unop).val.obj S) := sorry

lemma module_maps_profinite' (T : Profinite.{u}ᵒᵖ) : ∀ (S W : Profinite.{u}ᵒᵖ) (f : S ⟶ W),
  is_linear_map A ((Profinite_to_Condensed.obj T.unop).val.map f) := sorry

def CondensedMod_hom_equiv_presheaf_hom (X Y : Condensed.{u} (Module.{u+1} A)) :
  (X ⟶ Y) ≃ (X.val ⟶ Y.val) :=
equiv_of_fully_faithful (Sheaf_to_presheaf _ _)



-- def hom_Profinite_mod_iso_eval (T : Profinite.{u}) (X : Condensed.{u} (Module.{u+1} A))
--   [add_comm_group T] [module A T] :
--   (CondensedMod_of_CondensedSet_with_module_inst A (Profinite_to_Condensed.obj T)
--   (module_maps_profinite A T) ⟶ X) ≅ ((CondensedMod_to_CondensedSet A).obj X).val.obj
--   (opposite.op T) :=
-- (equiv.trans (CondensedMod_hom_equiv_presheaf_hom A
--   (CondensedMod_of_CondensedSet_with_module_inst A (Profinite_to_Condensed.obj T)
--   (module_maps_profinite A T)) X)
--   (yoneda'_equiv.{u+1 u u+1} T ((CondensedMod_to_CondensedSet A).obj X).val)).to_iso

-- variable (Y  : Condensed.{u} (Module.{u+1} A))
-- #check (yoneda'_equiv.{u+1 u u+1} S (Y.val ⋙ (forget (Module.{u+1} A) : (Module.{u+1} A) ⥤
-- Type (u+1)))).to_iso


-- def loc_const_colim_presheaf : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
--   coextend Fintype.to_Profinite.op ⋙ (loc_const_presheaf X)

-- def can_nat_map : loc_const_colim_presheaf X ⟶ loc_const_presheaf X :=
-- { app := λ S, can_from_colim_loc_const.{u} S.unop X,
-- }
