import condensed.adjunctions_module
import solid.discrete_condensed

open category_theory
open category_theory.limits
open Profinite
open Condensed

noncomputable theory

universe u

variables (A : Type (u+1)) [ring A]

def fin_free_Condensed_Mod : Fintype.{u} ⥤ Condensed.{u} (Module.{u+1} A) :=
  Fintype.to_Profinite ⋙ Profinite_to_Condensed ⋙ CondensedSet_to_CondensedMod A

def Prof_free_Condensed_Mod : Profinite.{u} ⥤ Condensed.{u} (Module.{u+1} A) :=
  Profinite_to_Condensed ⋙ CondensedSet_to_CondensedMod A

set_option pp.universes true

instance (X : Profinite.{u}) : category.{(u+1)} ((ulift_hom.{u+1} (structured_arrow X
  Fintype.to_Profinite.{u}))) :=
{ hom := λ A B, ulift.{u+1} $ A.obj_down ⟶ B.obj_down,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩}

instance has_limits_of_shape_CondMod (X : Profinite.{u}) : has_limits_of_shape
  ((structured_arrow X Fintype.to_Profinite.{u})) (Condensed.{u} (Module.{u+1} A)) :=
begin
  haveI : has_limits_of_shape (ulift_hom.{u+1} (ulift.{(u+1) (u+1)}
    (structured_arrow X Fintype.to_Profinite.{u}))) (Condensed.{u} Ab.{u+1}) := by apply_instance,
  haveI : has_limits_of_shape (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u}))
    (Condensed.{u} Ab.{u+1}) := by apply_instance,
  haveI h2 : (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u})) ≌
    (structured_arrow X Fintype.to_Profinite.{u}) := ulift_hom.equiv.symm,
  apply has_limits_of_shape_of_equivalence h2,
  apply_instance,
end .

set_option pp.universes false

def Asolid_functor : Profinite.{u} ⥤ Condensed.{u} (Module.{u+1} A) :=
Ran.loc Fintype.to_Profinite (fin_free_Condensed_Mod A)

def A_Solidification_profinite : Prof_free_Condensed_Mod A ⟶ Asolid_functor A :=
(Ran.equiv Fintype.to_Profinite (fin_free_Condensed_Mod A) (Prof_free_Condensed_Mod A)).symm
  (nat_trans.id _)

def is_solid_Mod (M : Condensed.{u} (Module.{u+1} A)) : Prop :=
  ∀ X : Profinite.{u}, is_iso ((yoneda.obj M).map ((A_Solidification_profinite A).app X).op)
