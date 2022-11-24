import topology.category.Profinite.as_limit
import topology.category.Top.basic
import category_theory.limits.has_limits
import solid.colim_hom_injective

open category_theory
open category_theory.limits
open Profinite

noncomputable theory

universe u

lemma to_Top_iso_limit (S : Profinite.{u}) : to_Top.obj S = limit (S.diagram ⋙ to_Top) :=
begin
  sorry,
end

instance proj_epi {S : Profinite.{u}} (i : discrete_quotient S) :
  epi ((limit.cone (S.diagram ⋙ to_Top)).π.app i) :=
begin
  have : preserves_limit S.diagram to_Top := by apply_instance,
  let c := this.preserves S.as_limit,
  have h : (limit.cone (S.diagram ⋙ to_Top)) ≅ (to_Top.map_cone S.as_limit_cone) :=
   is_limit.unique_up_to_iso (limit.is_limit _) c,
  -- have hX : (limit.cone (S.diagram ⋙ to_Top)).X ≅ (to_Top.map_cone S.as_limit_cone).X,
  -- { exact ⟨h.hom, h.inv⟩, },
  have h₁ : ((limit.cone (S.diagram ⋙ to_Top)).π.app i) =
    h.hom.hom ≫ ((to_Top.map_cone S.as_limit_cone).π.app i) :=
    (cone_morphism.w h.hom i).symm,
  rw h₁,
  haveI h₂ : is_iso h.hom.hom,
  { fconstructor,
    use h.inv.hom,
    split,
    { have hom_comp : (h.hom.hom ≫ h.inv.hom) = (h.hom ≫ h.inv).hom := by refl,
      have id_comp : 𝟙 (limit.cone (S.diagram ⋙ to_Top)).X =
        cone_morphism.hom (𝟙 (limit.cone (S.diagram ⋙ to_Top))) := by refl,
      rw hom_comp,
      rw id_comp,
      rw ← cone_morphism.ext_iff _ _,
      exact h.hom_inv_id' },
    { have hom_comp : (h.inv.hom ≫ h.hom.hom) = (h.inv ≫ h.hom).hom := by refl,
      have id_comp : 𝟙 (to_Top.map_cone S.as_limit_cone).X =
        cone_morphism.hom (𝟙 (to_Top.map_cone S.as_limit_cone)) := by refl,
      rw hom_comp,
      rw id_comp,
      rw ← cone_morphism.ext_iff _ _,
      exact h.inv_hom_id' } },
  have h₃ := is_iso.epi_of_iso h.hom.hom,
  apply epi_comp h.hom.hom _,
  simp only [Profinite.to_Top_map, category_theory.functor.map_cone_π_app],
  refine (Top.epi_iff_surjective (S.as_limit_cone.π.app i)).mpr _,
  exact discrete_quotient.proj_surjective i,
end

def map_as_discrete_quotient {α β : Type u} {f : α → β} [topological_space α] [topological_space β]
  [compact_space α] [t2_space α] [totally_disconnected_space α] [discrete_topology β]
  (cont : continuous f) : discrete_quotient α := discrete_quotient.comap ⊥ cont

lemma discreteness_condition_necessary {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] :
  is_iso (can_map_from_colim_of_homs_to_hom_from_limit X (S.diagram ⋙ Profinite.to_Top)) :=
begin
  refine (is_iso_iff_bijective (can_map_from_colim_of_homs_to_hom_from_limit X (S.diagram ⋙ Profinite.to_Top))).mpr _,
  split, { exact can_is_injective _ _ (λ i, proj_epi i), },
  intros f,
  rw ← to_Top_iso_limit S at f,
  cases f,
  cases f_1,
  let a := colimit.ι (((S.diagram ⋙ to_Top).op ⋙ yoneda.obj X ⋙ ulift_functor))
    (opposite.op (map_as_discrete_quotient f_1_continuous_to_fun)),
  sorry,
end
