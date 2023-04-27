import category_theory.limits.kan_extension
import solid.dq_sa_comparison
import solid.has_limits_fintype
import solid.loc_const_colim

noncomputable theory

universe u

open category_theory
open Profinite
open opposite
open Fintype
open category_theory.limits

noncomputable! def fin_yoneda (X : Type (u+1)) : Fintype.{u}ᵒᵖ  ⥤ Type (u+1) :=
{ obj := λ Y, (unop Y) → X,
  map := λ Y Z f g z, g (f.unop z), }

def fin_yoneda_iso_loc_const (X : Type (u+1)) : fin_yoneda X ≅
  to_Profinite.op ⋙ loc_const_presheaf X := sorry

set_option pp.universes true

instance has_colimits_for_Lan (S : Profinite.{u}ᵒᵖ) : has_colimits_of_shape
  (costructured_arrow to_Profinite.op S) (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u+1} (Type (u+1)) := by apply_instance,
  haveI : has_colimits_of_size.{u u+1} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u+1 u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (costructured_arrow to_Profinite.op S),
end

set_option pp.universes false

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
  sorry,
end))
sorry
