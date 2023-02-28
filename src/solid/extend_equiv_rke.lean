import for_mathlib.Profinite.extend
import solid.dq_sa_comparison

noncomputable theory

open Profinite
open Fintype
open category_theory
open category_theory.limits

universes v u u'

variables {C : Type u} [category.{v} C] (F : Fintype.{v} ⥤ C)
variables {D : Type u'} [category.{v} D]
variables [∀ (X : Profinite), has_limit (X.fintype_diagram ⋙ F)]
variables [∀ (X : Profinite), has_limit (Ran.diagram to_Profinite F X)]
variables (S : Profinite.{v})

def functors_extend_rke_nat_trans :
  sa_dq_functor S ⋙ S.fintype_diagram ⟶ structured_arrow.proj S to_Profinite :=
{ app := λ f, hom_to_dq_to_right f,
  naturality' :=
  begin
    intros f g p,
    cases p,
    ext,
    dsimp at *,
    dsimp [sa_dq_functor] at *,
    dsimp [fintype_diagram] at *,
    obtain ⟨x', hx⟩ := discrete_quotient.proj_surjective _ x,
    rw ← hx,
    rw fhom_eq_proj_apply f x',
    simp only [discrete_quotient.of_le_proj_apply],
    rw fhom_eq_proj_apply g x',
    simp only [category_theory.category.id_comp] at p_w',
    rw p_w',
    refl,
  end }

lemma Fintype_is_iso_iff_bijective {X Y : Fintype} (f : X ⟶ Y) :
  is_iso f ↔ function.bijective f :=
begin
  split,
  { introsI hf,
    let h := as_iso f,
    let h' := Fintype.equiv_equiv_iso.inv_fun h,
    exact h'.bijective },
  intros hf,
  let h := equiv.of_bijective f hf,
  use h.inv_fun,
  split,
  { ext, exact h.left_inv x },
  { ext, exact h.right_inv x }
end

instance (Si : discrete_quotient S) :
  is_iso ((whisker_left (dq_sa_functor S) (functors_extend_rke_nat_trans S)).app Si) :=
begin
  rw Fintype_is_iso_iff_bijective,
  split,
  { intros a b h,
    exact inj_hom_to_dq_to_right _ h},
  intros a,
  exact surj_hom_to_dq_to_right_of_fhom_surj _ (discrete_quotient.proj_surjective _) _,
end

instance : is_iso (whisker_left (dq_sa_functor S) (functors_extend_rke_nat_trans S)) :=
  nat_iso.is_iso_of_is_iso_app _

def functors_extend_rke_iso_aux :
  dq_sa_functor S ⋙ sa_dq_functor S ⋙ S.fintype_diagram ≅
  dq_sa_functor S ⋙ structured_arrow.proj S to_Profinite :=
as_iso (whisker_left (dq_sa_functor S) (functors_extend_rke_nat_trans S))

def functors_extend_rke_iso :
  Ran.diagram to_Profinite F S ≅ sa_dq_functor S ⋙ S.fintype_diagram ⋙ F := sorry

def extend_equiv_rke : extend F ≅ Ran.loc to_Profinite F := sorry

/- Should follow from `sa_dq_initial` -/
