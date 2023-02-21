import category_theory.limits.kan_extension
import condensed.basic
import solid.dq_sa_comparison

noncomputable theory

universes u

open category_theory
open category_theory.limits
open Profinite
open opposite
open Fintype

set_option pp.universes true

instance (S : Profinite.{u}ᵒᵖ) : has_colimits_of_shape
  (costructured_arrow to_Profinite.op S) (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u+1} (Type (u+1)) := by apply_instance,
  haveI : has_colimits_of_size.{u u+1} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u+1 u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (costructured_arrow to_Profinite.op S),
end

set_option pp.universes false

def colim_as_Kan_extension (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  (Lan to_Profinite.op).obj (Fintype.incl.op ⋙ ulift_functor.{u+1}.op ⋙ (yoneda.obj X))

instance discrete_quotient_cofiltered (S : Profinite.{u}) :
  is_cofiltered (discrete_quotient S) := by fsplit

instance discrete_quotient_op_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (discrete_quotient S.unop)ᵒᵖ := by apply_instance

instance structured_arrow_inhabited (S : Profinite.{u}) :
  inhabited (structured_arrow S to_Profinite) :=
{ default := (dq_sa_functor S).obj ⊤ }

instance : full to_Profinite.{u} := by constructor

instance : faithful to_Profinite.{u} := by constructor

instance : reflects_limits to_Profinite.{u} := fully_faithful_reflects_limits _

def fintype_profinite_equiv (X : Fintype) : X ≃ to_Profinite.obj X :=
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  left_inv := by tauto,
  right_inv := by tauto, }

instance : Π (Y : Fintype), unique (Y ⟶ (Fintype.of punit)) := λ Y,
{ to_inhabited := { default := λ y, punit.star, },
  uniq := λ f, (by ext), }

instance : has_terminal Fintype :=
  has_terminal_of_unique (Fintype.of punit)

instance {X Y Z : Fintype} (f : X ⟶ Z) (g : Y ⟶ Z) : has_limit (cospan f g) := sorry

instance : has_pullbacks Fintype := has_pullbacks_of_has_limit_cospan _

instance : has_finite_limits Fintype := has_finite_limits_of_has_terminal_and_pullbacks

instance : preserves_finite_limits to_Profinite.{u} := sorry

instance structured_arrow_cofiltered (S : Profinite.{u}) :
  is_cofiltered (structured_arrow S to_Profinite) :=
(flat_of_preserves_finite_limits to_Profinite).cofiltered S

instance costructured_arrow_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (costructured_arrow to_Profinite.op S) :=
is_filtered.of_equivalence (structured_arrow_op_equivalence to_Profinite S.unop)

instance (X : Type (u+1)) : preserves_finite_limits (colim_as_Kan_extension X) :=
begin
  sorry,
end

def discrete_as_Kan_extension (X : Type (u+1)) : CondensedSet.{u} :=
{ val := colim_as_Kan_extension X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae (colim_as_Kan_extension X)).out 0 5,
    refine ⟨_,_,_⟩,
    { sorry },
    { sorry },
    { sorry },
  end, }
