import category_theory.limits.kan_extension
import category_theory.filtered
import condensed.basic
import solid.dq_sa_comparison
import solid.has_limits_fintype

noncomputable theory

universes v u

open category_theory
open Profinite
open opposite
open Fintype
open category_theory.limits

local attribute [instance] Fintype_bot_topology

local attribute [instance] Fintype_discrete_topology

set_option pp.universes true

instance (S : Profinite.{u}ᵒᵖ) : has_colimits_of_shape
  (costructured_arrow to_Profinite.op S) (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u+1} (Type (u+1)) := by apply_instance,
  haveI : has_colimits_of_size.{u u+1} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u+1 u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (costructured_arrow to_Profinite.op S),
end

-- instance (S : Profinite.{u}ᵒᵖ) : has_colimits_of_shape
--   (costructured_arrow to_Profinite.op S) (Type (max v u)) :=
-- begin
--   haveI : has_colimits_of_size.{(max v u)} (Type (max v u)) := by apply_instance,
--   haveI : has_colimits_of_size.{u (max v u)} (Type (max v u)) :=
--     has_colimits_of_size_shrink.{u (max v u) (max v u) (max v u)} (Type (max v u)),
--   exact has_colimits_of_size.has_colimits_of_shape (costructured_arrow to_Profinite.op S),
-- end

set_option pp.universes false

def colim_as_Kan_extension (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  (Lan to_Profinite.op).obj (Fintype.incl.op ⋙ ulift_functor.{u+1}.op ⋙ (yoneda.obj X))

-- variables X : Type v
-- #check yoneda.obj X

-- def colim_as_Kan_extension' (X : Type v) : Profinite.{u}ᵒᵖ ⥤ Type (max v u) :=
--   (Lan to_Profinite.op).obj (Fintype.incl.op ⋙ ulift_functor.op ⋙ (yoneda.obj X))

instance discrete_quotient_cofiltered (S : Profinite.{u}) :
  is_cofiltered (discrete_quotient S) := by fsplit

instance discrete_quotient_op_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (discrete_quotient S.unop)ᵒᵖ := by apply_instance

instance structured_arrow_inhabited (S : Profinite.{u}) :
  inhabited (structured_arrow S to_Profinite) :=
{ default := (dq_sa_functor S).obj ⊤ }

instance : full to_Profinite.{u} := by constructor

instance : faithful to_Profinite.{u} := by constructor

instance structured_arrow_cofiltered_nonempty (S : Profinite.{u}) [nonempty S] :
  is_cofiltered (structured_arrow S to_Profinite) :=
is_cofiltered.of_left_adjoint (dq_sa_adjunction S)

instance : is_cofiltered Fintype := category_theory.cofiltered_of_has_finite_limits

instance structured_arrow_cofiltered_empty (S : Profinite.{u}) [is_empty S] :
  is_cofiltered (structured_arrow S to_Profinite) :=
is_cofiltered.of_equivalence (sa_empty_equiv_Fintype S).symm

instance structured_arrow_cofiltered (S : Profinite.{u}) :
  is_cofiltered (structured_arrow S to_Profinite) :=
begin
  by_cases nonempty S,
  { haveI : nonempty S := h,
    apply_instance },
  rw not_nonempty_iff at h,
  haveI : is_empty S := h,
  apply_instance,
end

instance costructured_arrow_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (costructured_arrow to_Profinite.op S) :=
is_filtered.of_equivalence (structured_arrow_op_equivalence to_Profinite S.unop)

instance (X : Type (u+1)) : preserves_finite_limits (colim_as_Kan_extension X) :=
begin
  apply preserves_finite_limits_of_preserves_finite_limits_of_size,
  introsI K _ _,
  -- dsimp [colim_as_Kan_extension],
  constructor,
  intros F,
  -- dsimp [Lan],
  -- dsimp [Lan.loc],
  constructor,
  intros c hc,
  sorry,
  -- type_check Lan.diagram.{u} to_Profinite.op
  --   (Fintype.incl.op ⋙ ulift_functor.{u+1}.op ⋙ (yoneda.obj X)) (op Profinite.empty),
  -- exact limits.filtered_colim_preserves_finite_limits,
  -- constructor,
  -- dsimp,
  -- intros J hs hf,
  -- unfold colim_as_Kan_extension,
end

variables (S : Profinite.{u}ᵒᵖ)

instance (S : Profinite.{u}ᵒᵖ) : large_category (costructured_arrow to_Profinite.op S) :=
  by apply_instance

instance (S : Profinite.{u}ᵒᵖ) : small_category (discrete_quotient S.unop)ᵒᵖ := by apply_instance

-- This is the problem. Once we can index the colimit in a small category, we're much better off.

set_option pp.universes true

def discrete_as_Kan_extension (X : Type (u+1)) : CondensedSet.{u} :=
{ val := colim_as_Kan_extension X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae (colim_as_Kan_extension X)).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      dsimp [colim_as_Kan_extension],
      split,
      { rintros a b h,
        -- obtain ⟨j, a, ha⟩ := types.jointly_surjective'.{u+1 u} a,
        sorry,  },
      { sorry, }
      -- change (colim_as_Kan_extension X).obj (op empty) with
      --   to_Profinite.op.obj (op (Fintype.of empty)),
       },
    { sorry },
    { sorry },
  end, }
