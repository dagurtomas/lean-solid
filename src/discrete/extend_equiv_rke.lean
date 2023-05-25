import for_mathlib.Profinite.extend
import discrete.dq_sa_comparison

noncomputable theory

open Profinite
open Fintype
open category_theory
open category_theory.limits

universes v v' u

variables {C : Type u} [category.{v'} C] (F : Fintype.{v} ⥤ C)
variables (S : Profinite.{v})
variables [∀ (X : Profinite.{v}), has_limits_of_shape (discrete_quotient X) C]
variables [∀ (X : Profinite.{v}), has_limits_of_shape (structured_arrow X to_Profinite) C]

instance forall_has_limit_extend : ∀ (X : Profinite), has_limit (X.fintype_diagram ⋙ F) :=
  by apply_instance

instance forall_has_limit_ran : ∀ (X : Profinite), has_limit (Ran.diagram to_Profinite F X) :=
  by apply_instance

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

lemma limits_12 : ((limits_iso1 F S) ≪≫ (limits_iso2 F S)).hom =
  limits.lim.map (whisker_right (unit_iso_dq_sa S).hom (S.fintype_diagram ⋙ F)) :=
begin
  dsimp [limits_iso1, limits_iso2],
  ext,
  dsimp [functor.initial.limit_iso],
  simp only [category_theory.limits.limit.pre_pre,
    category_theory.whisker_right_app,
    category_theory.functor.comp_map,
    category_theory.limits.lim_map_π],
  change dq_sa_functor S ⋙ sa_dq_functor S ⋙ S.fintype_diagram ⋙ F with
    (dq_sa_functor S ⋙ sa_dq_functor S) ⋙ (S.fintype_diagram ⋙ F),
  simp only [category_theory.limits.limit.pre_π],
  dsimp [unit_iso_dq_sa],
  have : F.map (S.fintype_diagram.map (eq_to_hom (htdq_comp_dqth_eq_id j))) =
    (S.fintype_diagram ⋙ F).map (eq_to_hom (htdq_comp_dqth_eq_id j)) := by refl,
  rw this,
  simp only [limit.w],
  refl,
end

lemma limits_234 : ((limits_iso2 F S) ≪≫ (limits_iso3 F S) ≪≫ (limits_iso4 F S)).hom =
  limits.lim.map (whisker_right (functors_extend_rke_nat_trans S) F) :=
begin
  dsimp,
  rw ← iso.cancel_iso_inv_right _ _ (limits_iso4 F S),
  simp only [category.comp_id, iso.hom_inv_id, category.assoc],
  dsimp [limits_iso2, limits_iso3, limits_iso4],
  ext,
  dsimp [functor.initial.limit_iso],
  simp only [limit.pre_π, has_limit.iso_of_nat_iso_hom_π, whisker_right_app,
    limit.pre_π_assoc, lim_map_π, category.assoc],
  dsimp [functors_extend_rke_iso],
  dsimp [functors_extend_rke_iso_aux],
  simp only [category.comp_id, category.id_comp],
end

instance : is_iso (limits.lim.map (whisker_right (functors_extend_rke_nat_trans S) F)) :=
begin
  rw ← limits_234 F S,
  apply_instance,
end

instance is_iso12 :
  is_iso (limits.lim.map (whisker_right (unit_iso_dq_sa S).hom (S.fintype_diagram ⋙ F))) :=
begin
  rw ←limits_12 F S,
  apply_instance,
end

def limits_iso : limit (S.fintype_diagram ⋙ F) ≅ limit (Ran.diagram to_Profinite F S) :=
  (limits_iso1 F S) ≪≫ (limits_iso2 F S) ≪≫ (limits_iso3 F S) ≪≫ (limits_iso4 F S)

variables {D : Type u} [category.{v} D] (G : Fintype.{v} ⥤ D)
variables [∀ (X : Profinite.{v}), has_limits_of_shape (discrete_quotient X) D]
variables [∀ (X : Profinite.{v}), has_limits_of_shape (structured_arrow X to_Profinite) D]

def extend_to_rke : extend G ⟶ Ran.loc to_Profinite G :=
  (Ran.equiv to_Profinite G (extend G)).symm (extend_extends G).hom

def extend_equiv_rke : extend G ≅ Ran.loc to_Profinite G :=
nat_iso.of_components (λ S, limits_iso G S)
(begin
  intros S T f,
  dsimp only [limits_iso, iso.trans_hom],
  have : (limits_iso1 G S).hom ≫ (limits_iso2 G S).hom ≫ (limits_iso3 G S).hom ≫
    (limits_iso4 G S).hom = (limits_iso1 G S).hom ≫ ((limits_iso2 G S) ≪≫
    (limits_iso3 G S) ≪≫ (limits_iso4 G S)).hom :=
    by simp only [iso.cancel_iso_hom_right_assoc,
      iso.cancel_iso_hom_right, category.assoc, iso.trans_hom, iso.cancel_iso_hom_left],
  rw this,
  clear this,
  rw limits_234,
  have : (extend G).map f ≫ (limits_iso1 G T).hom ≫ (limits_iso2 G T).hom ≫ (limits_iso3 G T).hom ≫
    (limits_iso4 G T).hom = (extend G).map f ≫ (limits_iso1 G T).hom ≫ ((limits_iso2 G T) ≪≫
    (limits_iso3 G T) ≪≫ (limits_iso4 G T)).hom := by simp only [category.assoc, iso.trans_hom],
  rw this,
  clear this,
  rw limits_234,
  dsimp [limits_iso1],
  dsimp [functor.initial.limit_iso],
  simp only [← category.assoc, limit.lift_pre, limit.lift_map],
  simp only [← lim_map_eq_lim_map, category.assoc],
  rw limit.map_pre,
  simp only [← category.assoc, limit.pre_pre],
  ext,
  simp only [whisker_right_app,
    whisker_left_app,
    cone.whisker_π,
    nat_trans.comp_app,
    change_cone_π_app,
    cones.postcompose_obj_π,
    limit.cone_π,
    limit.lift_π,
    category.assoc,
    lim_map_eq_lim_map],
  change (Ran.diagram to_Profinite G T) with (structured_arrow.map f ⋙
    Ran.diagram to_Profinite G S),
  simp only [whisker_right_app, whisker_left_app, lim_map_π],
  change ((structured_arrow.map f :
    structured_arrow T to_Profinite ⥤ structured_arrow S to_Profinite) ⋙ sa_dq_functor S ⋙
    S.fintype_diagram ⋙ G) with (structured_arrow.map f ⋙ sa_dq_functor S) ⋙
    (S.fintype_diagram ⋙ G),
  simp only [category_theory.limits.limit.pre_π_assoc, ← functor.map_comp],
  congr' 2,
  ext,
  dsimp [functors_extend_rke_nat_trans],
  dsimp [hom_to_dq_to_right],
  dsimp [proj_bot_inv],
  congr' 1,
  induction x,
  refl,
  refl,
end)
