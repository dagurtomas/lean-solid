import topology.category.Profinite.as_limit
import topology.category.Top.basic
import category_theory.limits.has_limits
import solid.colim_hom_injective

open category_theory
open category_theory.limits
open Profinite

noncomputable theory

universe u

lemma iso_limit₁ (S : Profinite.{u}) : (limit.cone S.diagram).X = limit S.diagram := by simp

def iso_limit₂ (S : Profinite.{u}) : S ≅ (Profinite.limit_cone S.diagram).X :=
  (iso_as_limit_cone_lift S)

def iso_limit_cones (S : Profinite.{u}) : Profinite.limit_cone S.diagram ≅ limit.cone S.diagram :=
  is_limit.unique_up_to_iso (Profinite.limit_cone_is_limit S.diagram) (limit.is_limit S.diagram)

def iso_limit₃ (S : Profinite.{u}) : (Profinite.limit_cone S.diagram).X ≅ (limit.cone S.diagram).X :=
  iso_X_of_iso_cones (iso_limit_cones S)

def iso_limit (S : Profinite.{u}) : S ≅ limit S.diagram :=
  as_iso ((iso_limit₂ S).hom ≫ (iso_limit₃ S).hom)

def to_Top_map_cone_iso_limit_cone (S : Profinite.{u}) :
  (limit.cone (S.diagram ⋙ to_Top)) ≅ (to_Top.map_cone S.as_limit_cone) :=
begin
  have : preserves_limit S.diagram to_Top := by apply_instance,
  let c := this.preserves S.as_limit,
  exact is_limit.unique_up_to_iso (limit.is_limit _) c,
end

instance to_Top_map_cone_iso_limit_cone_hom_iso (S : Profinite.{u}) :
  is_iso (to_Top_map_cone_iso_limit_cone S).hom.hom :=
begin
  let h := to_Top_map_cone_iso_limit_cone S,
  fconstructor,
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
      exact h.inv_hom_id' },
end

def to_Top_iso_limit (S : Profinite.{u}) : to_Top.obj S ≅ limit (S.diagram ⋙ to_Top) :=
  (as_iso (to_Top_map_cone_iso_limit_cone S).hom.hom).symm
  -- iso_X_of_iso_cones (to_Top_map_cone_iso_limit_cone S)

def to_Top_iso_limit' (S : Profinite.{u}) : to_Top.obj (limit S.diagram) ≅ limit (S.diagram ⋙ to_Top) :=
  preserves_limit_iso to_Top S.diagram

instance proj_epi {S : Profinite.{u}} (i : discrete_quotient S) :
  epi ((limit.cone (S.diagram ⋙ to_Top)).π.app i) :=
begin
  let h := to_Top_map_cone_iso_limit_cone S,
  have h₁ : ((limit.cone (S.diagram ⋙ to_Top)).π.app i) =
    h.hom.hom ≫ ((to_Top.map_cone S.as_limit_cone).π.app i) :=
    (cone_morphism.w h.hom i).symm,
  rw h₁,
  have h₃ := is_iso.epi_of_iso h.hom.hom,
  apply epi_comp h.hom.hom _,
  simp only [Profinite.to_Top_map, category_theory.functor.map_cone_π_app],
  refine (Top.epi_iff_surjective (S.as_limit_cone.π.app i)).mpr _,
  exact discrete_quotient.proj_surjective i,
end

def map_as_discrete_quotient {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X]
  (g : to_Top.obj S ⟶ X) : discrete_quotient S := discrete_quotient.comap ⊥ g.continuous_to_fun

def map_as_discrete_quotient' {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X]
  (g : to_Top.obj (limit S.diagram) ⟶ X) : discrete_quotient S :=
  discrete_quotient.comap ⊥ (to_Top.map (iso_limit S).hom ≫ g).continuous_to_fun

def proj_g {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] (g : to_Top.obj S ⟶ X) :
  S ⟶ (S.diagram.obj (map_as_discrete_quotient g)) :=
  ⟨(map_as_discrete_quotient g).proj, discrete_quotient.proj_continuous _⟩

def proj_g' {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X]
  (g : to_Top.obj (limit S.diagram) ⟶ X) :
  limit S.diagram ⟶ (S.diagram.obj (map_as_discrete_quotient' g)) :=
limit.π S.diagram (opposite.unop (opposite.op (map_as_discrete_quotient' g)))

def incl_im {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] (g : to_Top.obj S ⟶ X) :
  (S.diagram ⋙ to_Top).obj (map_as_discrete_quotient g) ⟶ X := sorry

def incl_im' {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X]
  (g : to_Top.obj (limit S.diagram) ⟶ X) :
  (S.diagram ⋙ to_Top).obj (map_as_discrete_quotient' g) ⟶ X := sorry

lemma g_factorisation {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X]
  (g : to_Top.obj S ⟶ X) : g = to_Top.map (proj_g g) ≫ (incl_im g) := sorry

lemma g_factorisation' {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X]
  (g : to_Top.obj (limit S.diagram) ⟶ X) :
  g = (proj_g' g) ≫ (incl_im' g) := sorry

lemma discreteness_condition_necessary {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] :
  is_iso (can_map_from_colim_of_homs_to_hom_from_limit X (S.diagram ⋙ Profinite.to_Top)) :=
begin
  refine (is_iso_iff_bijective (can_map_from_colim_of_homs_to_hom_from_limit X
    (S.diagram ⋙ to_Top))).mpr _,
  split, { exact can_is_injective _ _ (λ i, proj_epi i), },
  intros f,
  let g := (to_Top_iso_limit' S).hom ≫ f.down,
  let a := colimit.ι ((S.diagram ⋙ to_Top).op ⋙ yoneda.obj X ⋙ ulift_functor)
    (opposite.op (map_as_discrete_quotient' g)) ⟨(incl_im' g)⟩,
  use a,
  rw ← ulift.down_inj,
  rw ← can_eq_left_comp_with_proj _ _ _,
  simp only [],
  rw ← iso.cancel_iso_hom_left (to_Top_iso_limit' S) _ _,
  change (to_Top_iso_limit' S).hom ≫ f.down with g,
  have : to_Top_iso_limit' S = preserves_limit_iso to_Top S.diagram := by refl,
  rw this,
  simp only [← category.assoc'],
  rw preserves_limits_iso_hom_π to_Top S.diagram _,
  simp only [Profinite.to_Top_map],
  exact (g_factorisation' g).symm,
end
