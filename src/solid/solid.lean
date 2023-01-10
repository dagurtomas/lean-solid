import condensed.ab
import category_theory.limits.kan_extension

open category_theory
open Profinite
open Condensed

noncomputable theory

universe u
variables (S T : Profinite.{u})

def FinCondensed : Fintype.{u} ⥤ CondensedSet.{u} :=
  Fintype.to_Profinite ⋙ Profinite.to_Top ⋙ Top_to_Condensed

def FinFreeCondensed : Fintype.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  FinCondensed ⋙ CondensedSet_to_Condensed_Ab.{u}

def ProfFreeCondensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  Profinite.to_Top ⋙ Top_to_Condensed ⋙ CondensedSet_to_Condensed_Ab.{u}

instance (X : Profinite.{u}) : category.{(u+1)} ((ulift_hom.{u+1} (structured_arrow X
  Fintype.to_Profinite.{u}))) :=
{ hom := λ A B, ulift.{u+1} $ A.obj_down ⟶ B.obj_down,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩}

instance (X : Profinite.{u}) : limits.has_limits_of_shape
  ((structured_arrow X Fintype.to_Profinite.{u})) (Condensed.{u} Ab.{u+1}) :=
begin
  haveI : limits.has_limits_of_shape (ulift_hom.{u+1} (ulift.{(u+1) (u+1)}
    (structured_arrow X Fintype.to_Profinite.{u}))) (Condensed.{u} Ab.{u+1}) := by apply_instance,
  haveI : limits.has_limits_of_shape (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u}))
    (Condensed.{u} Ab.{u+1}) := by apply_instance,
  haveI h2 : (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u})) ≌
    (structured_arrow X Fintype.to_Profinite.{u}) := ulift_hom.equiv.symm,
  apply limits.has_limits_of_shape_of_equivalence h2,
  apply_instance,
end

def Zsolid_functor : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Ran.loc Fintype.to_Profinite FinFreeCondensed

def Solidification_profinite : ProfFreeCondensed ⟶ Zsolid_functor :=
  (Ran.equiv Fintype.to_Profinite FinFreeCondensed ProfFreeCondensed).symm (nat_trans.id _)

def is_solid (A : Condensed.{u} Ab.{u+1}) : Prop :=
  ∀ X : Profinite.{u}, is_iso ((yoneda.obj A).map (Solidification_profinite.app X).op)
