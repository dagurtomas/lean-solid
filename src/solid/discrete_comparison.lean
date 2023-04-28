import solid.discrete_condensed
import solid.loc_const_underlying_adjunction
import solid.lan_presheaf

noncomputable theory

universe u

open category_theory
open category_theory.adjunction

def Type_to_loc_const_Condensed_iso : Type_to_Condensed ≅ loc_const_Condensed_functor :=
  left_adjoint_uniq Condensed_Type_adjunction loc_const_adjunction

def lan_loc_const_Condensed_iso (X : Type (u+1)) : lan_CondensedSet X ≅ loc_const_CondensedSet X :=
{ hom := { val := (lan_presheaf_iso_loc_const_presheaf X).hom },
  inv := { val := (lan_presheaf_iso_loc_const_presheaf X).inv } } .

def lan_Type_to_Condensed_iso (X : Type (u+1)) : lan_CondensedSet X ≅ Type_to_Condensed.obj X :=
  lan_loc_const_Condensed_iso X ≪≫ (Type_to_loc_const_Condensed_iso.app X).symm
