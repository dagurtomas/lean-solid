import solid.discrete_condensed
import condensed.ab
import category_theory.limits.kan_extension
import category_theory.natural_isomorphism

open category_theory
open category_theory.limits
open Profinite
open Condensed

noncomputable theory

universe u

def FinCondensed : Fintype.{u} ⥤ CondensedSet.{u} :=
  Fintype.to_Profinite ⋙ Profinite_to_Condensed

def FinFreeCondensed : Fintype.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  FinCondensed ⋙ CondensedSet_to_Condensed_Ab.{u}

def ProfFreeCondensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  Profinite_to_Condensed ⋙ CondensedSet_to_Condensed_Ab.{u}

set_option pp.universes true

instance (X : Profinite.{u}) : category.{(u+1)} ((ulift_hom.{u+1} (structured_arrow X
  Fintype.to_Profinite.{u}))) :=
{ hom := λ A B, ulift.{u+1} $ A.obj_down ⟶ B.obj_down,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩}

instance (X : Profinite.{u}) : has_limits_of_shape
  ((structured_arrow X Fintype.to_Profinite.{u})) (Condensed.{u} Ab.{u+1}) :=
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

def Zsolid_functor : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
Ran.loc Fintype.to_Profinite FinFreeCondensed

def Solidification_profinite : ProfFreeCondensed ⟶ Zsolid_functor :=
  (Ran.equiv Fintype.to_Profinite FinFreeCondensed ProfFreeCondensed).symm (nat_trans.id _)

def is_solid (A : Condensed.{u} Ab.{u+1}) : Prop :=
  ∀ X : Profinite.{u}, is_iso ((yoneda.obj A).map (Solidification_profinite.app X).op)

set_option pp.universes true

instance has_limit_F {I : Type (u)} [category.{u} I] (F : I ⥤ Condensed.{u} Ab.{u+1}) :
  has_limit F :=
begin
  haveI : has_limits_of_size.{u u} (Condensed.{u} Ab.{u+1}) :=
    has_limits_of_size_shrink.{u u u+1 u+1} (Condensed.{u} Ab.{u+1}),
  apply_instance,
end

set_option pp.universes false

#exit

def cond_Z : Condensed.{u} Ab.{u+1} := Ab_to_Condensed.obj (⟨ulift ℤ⟩ : Ab.{u+1})

def index_for_prod (S : Profinite.{u}) : Type u := sorry

def map_for_prod (S : Profinite.{u}) : index_for_prod S → Condensed.{u} Ab.{u+1} := λ i, cond_Z

def Zsolid_iso_prod (S : Profinite.{u}) : Zsolid_functor.obj S ≅ ∏ (map_for_prod S) := sorry

theorem is_solid_discrete (M : Ab.{u+1}) : is_solid (Ab_to_Condensed.obj M) := sorry

theorem is_solid_Z : is_solid cond_Z := is_solid_discrete _

theorem is_solid_limit {I : Type u} [category.{u} I] {F : I ⥤ Condensed.{u} Ab.{u+1}}
  (h : ∀ i, (is_solid (F.obj i))) : is_solid (limit F) :=
begin
  intro S,
  sorry,
end

namespace nat_iso

universes u₁ u₂

/- From category_theory.natural_isomorphism in a newer version of mathlib -/
lemma is_iso_map_iff {C : Type u₁} [category C]  {D : Type u₂}  [category D]
  {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
  is_iso (F₁.map f) ↔ is_iso (F₂.map f) :=
begin
  revert F₁ F₂,
  suffices : ∀ {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) (hf : is_iso (F₁.map f)), is_iso (F₂.map f),
  { exact λ F₁ F₂ e, ⟨this e, this e.symm⟩, },
  introsI F₁ F₂ e hf,
  refine is_iso.mk ⟨e.inv.app Y ≫ inv (F₁.map f) ≫ e.hom.app X, _, _⟩,
  { simp only [nat_trans.naturality_assoc, is_iso.hom_inv_id_assoc, iso.inv_hom_id_app], },
  { simp only [category.assoc, ← e.hom.naturality, is_iso.inv_hom_id_assoc, iso.inv_hom_id_app], },
end

end nat_iso

theorem is_solid_iso {A B : Condensed.{u} Ab.{u+1}} (h : A ≅ B) (hA : is_solid A) : is_solid B :=
begin
  intro S,
  specialize hA S,
  let h' := yoneda.map_iso h,
  rw ← nat_iso.is_iso_map_iff h' _,
  assumption,
end

theorem is_solid_Zsolid (S : Profinite.{u}) : is_solid (Zsolid_functor.obj S) :=
is_solid_iso (Zsolid_iso_prod S).symm (is_solid_limit (λ i, is_solid_Z))
