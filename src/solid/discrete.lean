import topology.category.Profinite.as_limit
import topology.category.Profinite.cofiltered_limit
import topology.category.Top.basic
import category_theory.limits.has_limits
import solid.colim_hom_injective

open category_theory
open category_theory.limits
open Profinite

noncomputable theory

universe u

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

def to_Top_iso_limit (S : Profinite.{u}) :
  to_Top.obj (limit S.diagram) ≅ limit (S.diagram ⋙ to_Top) :=
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

def loc_const_of_general {α β : Type u} [topological_space α] [topological_space β]
  [discrete_topology β] {f : α → β} (cont : continuous f) :
  locally_constant α β := ⟨f, (is_locally_constant.iff_continuous f).mpr cont⟩

def loc_const_of_Top_hom {X Y : Top.{u}} [discrete_topology Y] (f : X ⟶ Y) :
  locally_constant X Y := loc_const_of_general f.continuous_to_fun

def Top_hom_of_loc_const {X Y : Top.{u}} (f : locally_constant X Y) :
  X ⟶ Y := ⟨f.to_fun, f.continuous⟩

lemma Top_hom_loc_const_eq_id {X Y : Top.{u}} [discrete_topology Y] (f : X ⟶ Y) :
  Top_hom_of_loc_const (loc_const_of_Top_hom f) = f :=
begin
  unfold Top_hom_of_loc_const,
  unfold loc_const_of_Top_hom,
  unfold loc_const_of_general,
  simp only [continuous_map.to_fun_eq_coe],
  ext,
  norm_num,
end

lemma loc_const_Top_hom_eq_id {X Y : Top.{u}} [discrete_topology Y] (f : locally_constant X Y) :
  loc_const_of_Top_hom (Top_hom_of_loc_const f) = f :=
begin
  unfold loc_const_of_Top_hom,
  unfold loc_const_of_general,
  unfold Top_hom_of_loc_const,
  simp only [continuous_map.to_fun_eq_coe],
  ext,
  norm_num,
end

lemma discreteness_condition_necessary {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] :
  is_iso (can_map_from_colim_of_homs_to_hom_from_limit X (S.diagram ⋙ to_Top)) :=
begin
  refine (is_iso_iff_bijective (can_map_from_colim_of_homs_to_hom_from_limit X
    (S.diagram ⋙ to_Top))).mpr _,
  split, { exact can_is_injective _ _ (λ i, proj_epi i), },
  intros f,
  let g := (to_Top_iso_limit S).hom ≫ f.down,
  obtain ⟨j, g', hg⟩ :=
    exists_locally_constant _ (limit.is_limit _) (loc_const_of_Top_hom g),
  let a := colimit.ι ((S.diagram ⋙ to_Top).op ⋙ yoneda.obj X ⋙ ulift_functor) (opposite.op j)
    ⟨(Top_hom_of_loc_const g')⟩,
  use a,
  rw ← ulift.down_inj,
  rw ← can_eq_left_comp_with_proj' _ _ _,
  rw ← iso.cancel_iso_hom_left (to_Top_iso_limit S) _ _,
  change (to_Top_iso_limit S).hom ≫ f.down with g,
  have : to_Top_iso_limit S = preserves_limit_iso to_Top S.diagram := by refl,
  rw this,
  simp only [← category.assoc'],
  rw preserves_limits_iso_hom_π to_Top S.diagram _,
  simp only [Profinite.to_Top_map],
  apply_fun Top_hom_of_loc_const at hg,
  rw Top_hom_loc_const_eq_id at hg,
  rw hg,
  simp only [category_theory.limits.limit.cone_π],
  have hf : continuous (limit.π S.diagram j) := continuous_map.continuous _,
  unfold locally_constant.comap,
  split_ifs, { refl },
  exfalso,
  exact h hf,
end
