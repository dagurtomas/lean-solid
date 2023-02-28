import category_theory.limits.kan_extension
import category_theory.filtered
import condensed.basic
import solid.dq_sa_comparison
import solid.has_limits_fintype

noncomputable theory

universes u

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

instance structured_arrow_cofiltered_nonempty (S : Profinite.{u}) [nonempty S] :
  is_cofiltered (structured_arrow S to_Profinite) :=
is_cofiltered.of_left_adjoint (dq_sa_adjunction S)

instance (S : Profinite.{u}) [is_empty S] : faithful (structured_arrow.proj S to_Profinite) :=
  by apply_instance

lemma maps_out_of_empty {S T : Profinite.{u}} [is_empty S] (f g : S ⟶ T) : f = g :=
begin
  ext,
  rw is_empty_iff at _inst_1,
  exfalso,
  exact _inst_1 a,
end

instance (S : Profinite.{u}) [is_empty S] : full (structured_arrow.proj S to_Profinite) :=
  functor.full_of_surjective _ (λ f g p,
begin
  dsimp at *,
  have : f.hom ≫ to_Profinite.map p = g.hom,
  { ext,
    dsimp at *,
    exfalso,
    rw is_empty_iff at _inst_1,
    exact _inst_1 a, },
  use structured_arrow.hom_mk p this,
  refl,
end)

instance (S : Profinite.{u}) [is_empty S] : ess_surj (structured_arrow.proj S to_Profinite) :=
begin
  constructor,
  intros Y,
  let f : S → to_Profinite.obj Y := is_empty.elim' _inst_1,
  have : continuous f,
  { rw continuous_def,
    intros U hU,
    rw set.eq_empty_of_is_empty (f ⁻¹' U),
    exact is_open_empty },
  let f' : S ⟶ to_Profinite.obj Y := ⟨f, this⟩,
  use structured_arrow.mk f',
  use iso.refl Y,
end

instance (S : Profinite.{u}) [is_empty S] : is_equivalence (structured_arrow.proj S to_Profinite) :=
  equivalence.of_fully_faithfully_ess_surj (structured_arrow.proj S to_Profinite)

def sa_empty_equiv_Fintype (S : Profinite.{u}) [is_empty S] :
  structured_arrow S to_Profinite ≌ Fintype :=
functor.as_equivalence (structured_arrow.proj S to_Profinite)

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
