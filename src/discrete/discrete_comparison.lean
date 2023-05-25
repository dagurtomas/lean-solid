import discrete.discrete_condensed
import discrete.loc_const_underlying_adjunction
import discrete.lan_presheaf

noncomputable theory

universe u

open category_theory
open category_theory.adjunction

/-  Let `X : Type (u+1)`.
    `Type_to_Condensed.obj X : CondensedSet.{u}` is the constant sheaf at `X`.
    `loc_const_Condensed_functor.obj X` is `loc_const_CondensedSet X : CondensedSet.{u}` which
    is the sheaf taking a profinite set `T` to locally constant maps `T → X`.
    `lan_CondensedSet X` is the left Kan extension of the funtor
    `fin_yoneda X : Fintype.{u}ᵒᵖ ⥤ Type (u+1)`, taking a `Fintype` `Y` to `Y → X`
    along the embedding `to_Profinite.op : Fintype.{u}ᵒᵖ ⥤ Profinite.{u}ᵒᵖ.
    These are all isomorphic as shown below. -/

def Type_to_loc_const_Condensed_iso : Type_to_Condensed ≅ loc_const_Condensed_functor :=
  left_adjoint_uniq Condensed_Type_adjunction loc_const_adjunction

def lan_loc_const_Condensed_iso (X : Type (u+1)) : lan_CondensedSet X ≅ loc_const_CondensedSet X :=
{ hom := { val := (lan_presheaf_iso_loc_const_presheaf X).hom },
  inv := { val := (lan_presheaf_iso_loc_const_presheaf X).inv } } .

def lan_Type_to_Condensed_iso (X : Type (u+1)) : lan_CondensedSet X ≅ Type_to_Condensed.obj X :=
  lan_loc_const_Condensed_iso X ≪≫ (Type_to_loc_const_Condensed_iso.app X).symm

instance unit_iso : is_iso loc_const_adjunction.unit := unit_loc_const_is_iso

instance : faithful loc_const_Condensed_functor := L_faithful_of_unit_is_iso loc_const_adjunction

instance : full loc_const_Condensed_functor := L_full_of_unit_is_iso loc_const_adjunction

instance : faithful Type_to_Condensed := faithful.of_iso Type_to_loc_const_Condensed_iso.symm

instance : full Type_to_Condensed := full.of_iso Type_to_loc_const_Condensed_iso.symm
