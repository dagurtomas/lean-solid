import topology.category.Profinite.as_limit
import category_theory.limits.kan_extension
import category_theory.equivalence
import category_theory.functor.flat
import condensed.basic

noncomputable theory

universes v u

open category_theory
open category_theory.limits
open Profinite
open opposite
open discrete_quotient
open Fintype

/-- Finite types are given the discrete topology. -/
def Fintype_bot_topology (A : Fintype) : topological_space A := ⊥

local attribute [instance] Fintype_bot_topology

local attribute [instance]
lemma Fintype_discrete_topology (A : Fintype) : discrete_topology ↥A := ⟨rfl⟩

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

lemma rel_proj {S : Profinite.{u}} (Si : discrete_quotient S) (x y : S) :
  Si.rel x y ↔ Si.proj x = Si.proj y := ⟨λ h, quotient.sound' h, λ h, quotient.exact' h⟩

def dq_to_hom {S : Profinite.{u}} (Si : discrete_quotient S) :
  S ⟶ to_Profinite.obj (S.fintype_diagram.obj Si) := ⟨Si.proj, Si.proj_continuous⟩

def dq_sa_functor (S : Profinite.{u}) :
  discrete_quotient S ⥤ structured_arrow S to_Profinite :=
{ obj := λ Si, structured_arrow.mk (dq_to_hom Si),
  map := λ Si Sj g,
    structured_arrow.hom_mk' (structured_arrow.mk (dq_to_hom Si)) (S.fintype_diagram.map g), }

def hom_to_dq {S : Profinite.{u}} {X : Fintype}
  (f : S ⟶ to_Profinite.obj X) : discrete_quotient S :=
comap ⊥ f.continuous_to_fun

lemma sa_to_dq_le {S : Profinite.{u}} {f g : structured_arrow S to_Profinite} (φ : f ⟶ g) :
  hom_to_dq f.hom ≤ hom_to_dq g.hom :=
begin
  have : g.hom = f.hom ≫ to_Profinite.map φ.right :=
    by simp only [structured_arrow.w],
  rw this,
  have h : hom_to_dq (f.hom ≫ to_Profinite.map φ.right) =
    comap (⊥ : discrete_quotient (to_Profinite.obj g.right))
    (continuous.comp (to_Profinite.map φ.right).continuous_to_fun f.hom.continuous_to_fun) :=
    by refl,
  rw comap_comp at h,
  rw h,
  unfold hom_to_dq,
  exact comap_mono _ bot_le,
end

def sa_dq_functor (S : Profinite.{u}) :
  structured_arrow S to_Profinite ⥤ discrete_quotient S :=
{ obj := λ f, hom_to_dq f.hom,
  map := λ f g φ, hom_of_le $ sa_to_dq_le φ, }

lemma htdq_comp_dqth_eq_id {S : Profinite.{u}} (Si : discrete_quotient S) :
  Si = hom_to_dq (dq_to_hom Si) :=
begin
  ext x y,
  rw rel_proj Si x y,
  refl,
end

def unit_iso_dq_sa (S : Profinite.{u}) :
  𝟭 (discrete_quotient S) ≅ (dq_sa_functor S) ⋙ (sa_dq_functor S) :=
{ hom := { app := λ Si, eq_to_hom (htdq_comp_dqth_eq_id Si), },
  inv := { app := λ Si, eq_to_hom (htdq_comp_dqth_eq_id Si).symm, }, }

instance (S : Profinite.{u}) : faithful (dq_sa_functor S) :=
  faithful.of_comp_iso (unit_iso_dq_sa S).symm

instance es_sadq (S : Profinite.{u}) : ess_surj (sa_dq_functor S) :=
begin
  constructor,
  intros Y,
  use (dq_sa_functor S).obj Y,
  use (unit_iso_dq_sa S).inv.app Y,
  exact (unit_iso_dq_sa S).hom.app Y,
end

instance structured_arrow_inhabited (S : Profinite.{u}) :
  inhabited (structured_arrow S to_Profinite) :=
{ default := (dq_sa_functor S).obj ⊤ }

instance : full to_Profinite := by constructor

instance : faithful to_Profinite := by constructor

instance : has_finite_limits Fintype := sorry

instance : preserves_finite_limits to_Profinite := sorry

instance structured_arrow_cofiltered (S : Profinite.{u}) :
  is_cofiltered (structured_arrow S to_Profinite) :=
(flat_of_preserves_finite_limits to_Profinite).cofiltered S

instance costructured_arrow_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (costructured_arrow to_Profinite.op S) :=
is_filtered.of_equivalence (structured_arrow_op_equivalence to_Profinite S.unop)

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
