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
-- variables [∀ (X : Profinite), has_limits_of_shape (discrete_quotient X) C]
-- variables [∀ (X : Profinite), has_limits_of_shape (structured_arrow X to_Profinite) C]
variables (S : Profinite.{v})
variables [∀ (X : Profinite), has_limit (X.fintype_diagram ⋙ F)]
variables [∀ (X : Profinite), has_limit (Ran.diagram to_Profinite F X)]
variables [∀ (X : Profinite),
  has_limit (dq_sa_functor X ⋙ sa_dq_functor X ⋙ X.fintype_diagram ⋙ F)]

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
  dq_sa_functor S ⋙ sa_dq_functor S ⋙ S.fintype_diagram ⋙ F ≅
  dq_sa_functor S ⋙ Ran.diagram to_Profinite F S :=
(functor.associator (dq_sa_functor S) (sa_dq_functor S ⋙ S.fintype_diagram) F).symm ≪≫
  (iso_whisker_right (functors_extend_rke_iso_aux.{v} S) F) ≪≫
  (functor.associator (dq_sa_functor S) (structured_arrow.proj S to_Profinite) F)

def extend_to_rke : extend F ⟶ Ran.loc to_Profinite F :=
  (Ran.equiv to_Profinite F (extend F)).symm (extend_extends F).hom

def limits_iso1 : limit (S.fintype_diagram ⋙ F) ≅
  limit (sa_dq_functor S ⋙ S.fintype_diagram ⋙ F) :=
(functor.initial.limit_iso (sa_dq_functor S) (S.fintype_diagram ⋙ F)).symm

def limits_iso2 : limit (sa_dq_functor S ⋙ S.fintype_diagram ⋙ F) ≅
  limit (dq_sa_functor S ⋙ sa_dq_functor S ⋙ S.fintype_diagram ⋙ F) :=
(functor.initial.limit_iso (dq_sa_functor S) _).symm

def limits_iso3 : limit (dq_sa_functor S ⋙ sa_dq_functor S ⋙ S.fintype_diagram ⋙ F) ≅
  limit (dq_sa_functor S ⋙ Ran.diagram to_Profinite F S) :=
has_limit.iso_of_nat_iso (functors_extend_rke_iso F S)

def limits_iso4 : limit (dq_sa_functor S ⋙ Ran.diagram to_Profinite F S) ≅
  limit (Ran.diagram to_Profinite F S) :=
functor.initial.limit_iso (dq_sa_functor S) _

def limits_iso : limit (S.fintype_diagram ⋙ F) ≅ limit (Ran.diagram to_Profinite F S) :=
  (limits_iso1 F S) ≪≫ (limits_iso2 F S) ≪≫ (limits_iso3 F S) ≪≫ (limits_iso4 F S)

instance is_iso_extend_to_rke_app (S : Profinite) : is_iso ((extend_to_rke F).app S) :=
begin
  have : (extend_to_rke F).app S = (limits_iso F S).hom,
  { sorry,
    -- dsimp [limits_iso],
    -- rw ← iso.cancel_iso_inv_right _ _ (limits_iso4 F S),
    -- simp only [category.comp_id, iso.hom_inv_id, category.assoc],
    -- rw ← iso.cancel_iso_inv_right _ _ (limits_iso3 F S),
    -- simp only [category.comp_id, iso.hom_inv_id, category.assoc],
    -- dsimp [limits_iso1, limits_iso2, limits_iso3, limits_iso4],
    -- dsimp [functor.initial.limit_iso],
    -- ext,
    -- simp only [category.assoc, limit.pre_π, has_limit.iso_of_nat_iso_inv_π, limit.pre_π_assoc],
    -- dsimp [functors_extend_rke_iso],
    -- simp only [category.comp_id, category.id_comp],
    -- dsimp [functors_extend_rke_iso_aux],
    -- dsimp [functors_extend_rke_nat_trans],
    -- -- simp only [category_theory.functor.map_inv, whisker_left_app, nat_iso.is_iso_inv_app],
    -- -- rw limit.pre_π (Ran.diagram to_Profinite F S) (dq_sa_functor S) j,
    -- -- simp only [limit.pre_pre],
    -- dsimp [extend_to_rke],
    -- simp only [limit.lift_π_assoc, category.assoc],
    -- simp only [← functor.map_comp],
    -- simp only [whisker_left_app, nat_iso.is_iso_inv_app],
    -- dsimp [hom_to_dq_to_right],

    -- rw ← htdq_comp_dqth_eq_id_functors S j,
    -- congr' 2,

    -- dsimp [limit.pre],
    -- dsimp [is_limit.map],
    },
  rw this,
  apply_instance,
end

instance : is_iso (extend_to_rke F) := nat_iso.is_iso_of_is_iso_app _

def extend_equiv_rke : extend F ≅ Ran.loc to_Profinite F := as_iso (extend_to_rke _)

def extend_equiv_rke' : extend F ≅ Ran.loc to_Profinite F :=
nat_iso.of_components (λ S, limits_iso F S)
(begin
  intros S T f,
  ext,
  dsimp,
  sorry,
end)
