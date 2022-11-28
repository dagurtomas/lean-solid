import category_theory.limits.has_limits
import category_theory.limits.is_limit
import category_theory.limits.types
import category_theory.yoneda

universes u v

noncomputable theory

open category_theory
open category_theory.limits

variables {C : Type u}  [category.{v} C]
variables {I : Type v} [small_category I] -- [is_cofiltered I]
variables (X Y : C)
variables (S : I ⥤ C) [has_limit S]

def hom_as_cone_map : S.op ⋙ yoneda.obj Y ⋙ ulift_functor ⟶
  (category_theory.functor.const Iᵒᵖ).obj
  (ulift_functor.obj ((yoneda.obj Y).obj (opposite.op (limit S)))) :=
{ app := λ i, ulift_functor.map (as_hom (λ a, ((limit.cone S).π.app i.unop) ≫ a)),
  naturality' := begin
    intros i j ji,
    ext f,
    tidy,
    have h₁ : as_hom (category_struct.comp (limit.π S j.unop)) (S.map ji.unop ≫ f) =
      (limit.π S j.unop) ≫ (S.map ji.unop ≫ f) := by refl,
    have h₂ : as_hom (category_struct.comp (limit.π S j.unop ≫ S.map ji.unop)) f =
      (limit.π S j.unop ≫ S.map ji.unop) ≫ f := by refl,
    suffices h : (limit.π S j.unop) ≫ (S.map ji.unop) = (limit.π S i.unop),
    { rw ← h,
      rw h₁,
      rw h₂,
      simp only [category_theory.limits.limit.w,
        category_theory.limits.limit.w_assoc,
        eq_self_iff_true] },
    { simp only [category_theory.limits.limit.w, eq_self_iff_true] },
  end, }

def hom_as_cone : cocone (S.op ⋙ yoneda.obj Y ⋙ ulift_functor) :=
{ X := ulift_functor.obj ((yoneda.obj Y).obj (opposite.op (limit S))),
  ι := hom_as_cone_map Y S, }

def can_map_from_colim_of_homs_to_hom_from_limit :
  colimit (S.op ⋙ yoneda.obj Y ⋙ ulift_functor) ⟶ ulift_functor.obj
  ((yoneda.obj Y).obj (opposite.op (limit S))) :=
  colimit.desc (S.op ⋙ yoneda.obj Y ⋙ ulift_functor) (hom_as_cone Y S)

lemma can_eq_left_comp_with_proj {i : Iᵒᵖ}
  (x : (S.op ⋙ yoneda.obj Y ⋙ ulift_functor).obj i) :
  (limit.π S i.unop) ≫ x.down  =
  (can_map_from_colim_of_homs_to_hom_from_limit Y S
    (colimit.ι (S.op ⋙ yoneda.obj Y ⋙ ulift_functor) i x)).down :=
begin
  unfold can_map_from_colim_of_homs_to_hom_from_limit,
  cases x,
  simp only [category_theory.limits.types.colimit.ι_desc_apply],
  refl,
end

theorem can_is_injective (hI : ∀ i : I, epi ((limit.cone S).π.app i)) [is_cofiltered I] :
  function.injective (can_map_from_colim_of_homs_to_hom_from_limit Y S) :=
begin
  intros a b hab,
  obtain ⟨i, a', ha⟩ := types.jointly_surjective' a,
  obtain ⟨j, b', hb⟩ := types.jointly_surjective' b,
  rw ← ha,
  rw ← hb,
  have hIopfiltered : is_filtered Iᵒᵖ := category_theory.is_filtered_op_of_is_cofiltered I,
  obtain ⟨k, ki, kj, t⟩ := hIopfiltered.to_is_filtered_or_empty.cocone_objs i j,
  rw types.filtered_colimit.colimit_eq_iff,
  use k,
  use ki,
  use kj,
  let pi := limit.π S i.unop,
  let pj := limit.π S j.unop,
  let pk := limit.π S k.unop,
  have hk : epi pk := hI k.unop,
  have hcani := can_eq_left_comp_with_proj _ _ a',
  have hcanj := can_eq_left_comp_with_proj _ _ b',
  have hik : pi = pk ≫ (S.map ki.unop) := by tidy,
  have hjk : pj = pk ≫ (S.map kj.unop) := by tidy,
  have hpij : pi ≫ a'.down = pj ≫ b'.down,
  { rw hcani,
    rw hcanj,
    rw ha,
    rw hb,
    exact congr_arg ulift.down hab },
  rw hik at hpij,
  rw hjk at hpij,
  simp only [quiver.hom.unop_op,
    category_theory.ulift_functor_map,
    category_theory.functor.comp_map,
    ulift.up_inj,
    category_theory.functor.op_map,
    category_theory.yoneda_obj_map],
  simp only [category.assoc'] at hpij,
  exact hk.left_cancellation _ _ hpij,
end

instance is_iso_X_of_iso_cones {F : I ⥤ C} {c c' : cone F} (h : c ≅ c') : is_iso h.hom.hom :=
begin
  fconstructor,
  use h.inv.hom,
  split,
  { have hom_comp : (h.hom.hom ≫ h.inv.hom) = (h.hom ≫ h.inv).hom := by refl,
    have id_comp : 𝟙 c.X =
      cone_morphism.hom (𝟙 c) := by refl,
    rw hom_comp,
    rw id_comp,
    rw ← cone_morphism.ext_iff _ _,
    exact h.hom_inv_id' },
  { have hom_comp : (h.inv.hom ≫ h.hom.hom) = (h.inv ≫ h.hom).hom := by refl,
    have id_comp : 𝟙 c'.X =
      cone_morphism.hom (𝟙 c') := by refl,
    rw hom_comp,
    rw id_comp,
    rw ← cone_morphism.ext_iff _ _,
    exact h.inv_hom_id' },
end

def iso_X_of_iso_cones {F : I ⥤ C} {c c' : cone F} (f : c ≅ c') : c.X ≅ c'.X :=
  as_iso f.hom.hom
