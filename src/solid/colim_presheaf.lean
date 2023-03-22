import category_theory.limits.kan_extension
import category_theory.filtered
import for_mathlib.Profinite.extend
import condensed.basic
import solid.Profinite_ulift
import solid.dq_sa_comparison
import solid.has_limits_fintype
import condensed.filtered_colimits

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

def Fintype_to_Type_u : as_small.{u} Fintype.{u} ⥤ Type (u+1) :=
  as_small.down ⋙ Fintype.incl ⋙ ulift_functor.{u+1}

def Fintype_to_Type_u' : Fintype.{u} ⥤ Type (u+1) :=
  Fintype.incl ⋙ ulift_functor.{u+1}

def res_yoneda : Type (u+1) ⥤ (as_small.{u} Fintype.{u})ᵒᵖ ⥤ Type (u+1) :=
  (colimit_adj.restricted_yoneda Fintype_to_Type_u.{u})

def colim_as_Kan_extension₁ (X : Type (u+1)) : (as_small.{u} Profinite.{u})ᵒᵖ ⥤ Type (u+1) :=
  (Lan (as_small.down ⋙ to_Profinite ⋙ as_small.up).op).obj
  ((colimit_adj.restricted_yoneda Fintype_to_Type_u.{u}).obj X)

def colim_as_Kan_extension (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  (Lan to_Profinite.op).obj (Fintype.incl.op ⋙ ulift_functor.{u+1}.op ⋙ (yoneda.obj X))

def colim_as_Kan_extension' (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  Profinite_ulift.op ⋙ (extend (Fintype.incl.op ⋙ yoneda.obj X).right_op).left_op

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

instance : representably_flat to_Profinite := ⟨λ S, structured_arrow_cofiltered S⟩

instance : preserves_finite_limits to_Profinite := preserves_finite_limits_of_flat _

#exit

instance (X : Type (u+1)) : preserves_finite_limits (colim_as_Kan_extension' X) :=
begin
  constructor,
  intros J hJ hfJ,
  dsimp [colim_as_Kan_extension'],
  sorry,
  -- exact limits.filtered_colim_preserves_finite_limits,

end

-- variables (S : Profinite.{u}ᵒᵖ)

-- instance (S : Profinite.{u}ᵒᵖ) : large_category (costructured_arrow to_Profinite.op S) :=
--   by apply_instance

-- instance : essentially_small Fintype := essentially_small.mk' Fintype.skeleton.equivalence.symm

-- instance (S : Profinite.{u}ᵒᵖ) : essentially_small (costructured_arrow to_Profinite.op S) :=
--   sorry

-- instance (S : Profinite.{u}ᵒᵖ) : small_category (discrete_quotient S.unop)ᵒᵖ := by apply_instance

-- This is the problem. Once we can index the colimit in a small category, we're much better off.

-- set_option pp.universes true

def discrete_as_Kan_extension (X : Type (u+1)) : CondensedSet.{u} :=
{ val := colim_as_Kan_extension' X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae (colim_as_Kan_extension' X)).out 0 5,
    refine ⟨_,_,_⟩,
    { dsimp [functor.empty_condition],
      dsimp [colim_as_Kan_extension'],
      dsimp [Profinite_ulift],
      dsimp [Top_ulift],
      split,
      { rintros a b h,
        dsimp at *,
        -- obtain ⟨j, a, ha⟩ := types.jointly_surjective'.{u+1 u} a,
        sorry,  },
      { sorry, }
      -- change (colim_as_Kan_extension X).obj (op empty) with
      --   to_Profinite.op.obj (op (Fintype.of empty)),
       },
    { sorry },
    { sorry },
  end, }
