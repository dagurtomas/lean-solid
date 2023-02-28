import topology.category.Profinite.as_limit
import solid.new_final
import category_theory.functor.flat

/- solid.new_final is just category_theory.functor.final copied from a newer version of mathlib,
   which allows large categories. -/

noncomputable theory

universe u

open category_theory
open Profinite
open discrete_quotient
open Fintype

/-- Finite types are given the discrete topology. -/
def Fintype_bot_topology (A : Fintype) : topological_space A := ⊥

local attribute [instance] Fintype_bot_topology

local attribute [instance]
lemma Fintype_discrete_topology (A : Fintype) : discrete_topology ↥A := ⟨rfl⟩

variable {S : Profinite.{u}}

lemma rel_proj (Si : discrete_quotient S) (x y : S) :
  Si.rel x y ↔ Si.proj x = Si.proj y := ⟨λ h, quotient.sound' h, λ h, quotient.exact' h⟩

def dq_to_hom (Si : discrete_quotient S) :
  S ⟶ to_Profinite.obj (S.fintype_diagram.obj Si) := ⟨Si.proj, Si.proj_continuous⟩

def hom_to_dq {X : Fintype}
  (f : S ⟶ to_Profinite.obj X) : discrete_quotient S :=
comap ⊥ f.continuous

lemma sa_to_dq_le {f g : structured_arrow S to_Profinite} (φ : f ⟶ g) :
  hom_to_dq f.hom ≤ hom_to_dq g.hom :=
begin
  have : g.hom = f.hom ≫ to_Profinite.map φ.right :=
    by simp only [structured_arrow.w],
  rw this,
  have h : hom_to_dq (f.hom ≫ to_Profinite.map φ.right) =
    comap (⊥ : discrete_quotient (to_Profinite.obj g.right))
    (continuous.comp (to_Profinite.map φ.right).continuous f.hom.continuous) :=
    by refl,
  rw comap_comp at h,
  rw h,
  unfold hom_to_dq,
  exact comap_mono _ bot_le,
end

lemma htdq_comp_dqth_eq_id (Si : discrete_quotient S) :
  Si = hom_to_dq (dq_to_hom Si) :=
begin
  ext x y,
  rw rel_proj Si x y,
  refl,
end

lemma hom_eq_dq {Si Sj : discrete_quotient S} (f g : Si ⟶ Sj) : f = g :=
  (eq_iff_true_of_subsingleton f g).mpr (by triv)

lemma dq_map_injective (f : structured_arrow S to_Profinite) :
  function.injective (map (le_refl (comap ⊥ f.hom.continuous))) :=
begin
  intros a b h,
  obtain ⟨x, hxa⟩ := proj_surjective _ a,
  obtain ⟨y, hyb⟩ := proj_surjective _ b,
  rw [← hxa, ← hyb],
  rw ← rel_proj _ x y,
  have : (comap ⊥ f.hom.continuous).rel x y =
    (⊥ : discrete_quotient f.right).rel (f.hom x) (f.hom y) := by refl,
  rw this,
  have h' : (⊥ : discrete_quotient f.right).rel (f.hom x) (f.hom y) = ((f.hom x) = (f.hom y)) :=
    by refl,
  rw h',
  rw [← hxa, ← hyb] at h,
  rwa map_proj_apply at h,
  rw map_proj_apply at h,
  exact proj_bot_injective h,
end

lemma dq_map_surj_of_fhom_surj (f : structured_arrow S to_Profinite)
  (hf : function.surjective f.hom) :
  function.surjective (map (le_refl (comap ⊥ f.hom.continuous))) :=
begin
  intros a,
  obtain ⟨x, hxa⟩ := proj_surjective _ a,
  obtain ⟨y, hyx⟩ := hf x,
  rw ← hxa,
  dsimp at *,
  use (comap ⊥ f.hom.continuous).proj y,
  simp only [discrete_quotient.map_proj_apply],
  rw ← hyx,
end

def proj_bot_inv (f : structured_arrow S to_Profinite) :=
(function.surj_inv (proj_bot_bijective.2 : function.surjective
  (⊥ : discrete_quotient f.right).proj))

def hom_to_dq_to_right (f : structured_arrow S to_Profinite) :
  hom_to_dq f.hom → f.right :=
(proj_bot_inv f) ∘ map (le_refl (comap ⊥ f.hom.continuous))

instance nonempty_dq (Si : discrete_quotient S) [nonempty S] : nonempty Si :=
  by use Si.proj _inst_1.some

instance nonempty_hom_to_dq (f : structured_arrow S to_Profinite) [nonempty S] :
  nonempty (hom_to_dq f.hom) := @nonempty_dq S _ _inst_1

def right_to_hom_to_dq (f : structured_arrow S to_Profinite) [nonempty S] :
  f.right → hom_to_dq f.hom := function.inv_fun (hom_to_dq_to_right f)

lemma inj_hom_to_dq_to_right (f : structured_arrow S to_Profinite) :
  function.injective (hom_to_dq_to_right f) :=
function.injective.comp (function.injective_surj_inv _) (dq_map_injective f)

lemma right_hom_left_inv_apply {f : structured_arrow S to_Profinite} [nonempty S] :
  ∀ x, (right_to_hom_to_dq f) (hom_to_dq_to_right f x) = x :=
begin
  intro x,
  unfold right_to_hom_to_dq,
  exact function.left_inverse_inv_fun (inj_hom_to_dq_to_right _) x
end

lemma surj_hom_to_dq_to_right_of_fhom_surj (f : structured_arrow S to_Profinite)
  (hf : function.surjective f.hom) :
  function.surjective (hom_to_dq_to_right f) :=
function.surjective.comp (function.left_inverse.surjective (function.left_inverse_surj_inv
  proj_bot_bijective)) (dq_map_surj_of_fhom_surj f hf)

def fintype_map_of_sa_to_dq_le {f g : structured_arrow S to_Profinite}
  (h : hom_to_dq f.hom ≤ hom_to_dq g.hom) [nonempty S] : f.right → g.right :=
(hom_to_dq_to_right g) ∘ (of_le h) ∘ (right_to_hom_to_dq f)

lemma fhom_eq_proj (f : structured_arrow S to_Profinite) :
  (hom_to_dq_to_right f) ∘ (hom_to_dq f.hom).proj = f.hom :=
begin
  unfold hom_to_dq_to_right,
  rw function.comp.assoc,
  rw map_proj,
  ext,
  dsimp,
  exact function.left_inverse_surj_inv proj_bot_bijective _,
end

lemma fhom_eq_proj_apply (f : structured_arrow S to_Profinite) :
  ∀ x, hom_to_dq_to_right f ((hom_to_dq f.hom).proj x) = f.hom x :=
begin
  intros x,
  change (hom_to_dq_to_right f ((hom_to_dq f.hom).proj x)) with
    ((hom_to_dq_to_right f) ∘ (hom_to_dq f.hom).proj) x,
  rw fhom_eq_proj,
end

lemma inv_comps_apply (f : structured_arrow S to_Profinite)
  (x : hom_to_dq f.hom) [nonempty S] :
  right_to_hom_to_dq f (hom_to_dq_to_right f x) = x :=
begin
  change right_to_hom_to_dq f (hom_to_dq_to_right f x) with
    ((right_to_hom_to_dq f) ∘ (hom_to_dq_to_right f)) x,
  unfold right_to_hom_to_dq,
  rw function.inv_fun_comp (inj_hom_to_dq_to_right f),
  simp only [id.def],
end

lemma w_lemma {f g : structured_arrow S to_Profinite}
  (h : hom_to_dq f.hom ≤ hom_to_dq g.hom) [nonempty S] :
  f.hom ≫ to_Profinite.map (fintype_map_of_sa_to_dq_le h) = g.hom :=
begin
  ext,
  dsimp,
  rw ← fhom_eq_proj f,
  rw ← fhom_eq_proj g,
  dsimp [fintype_map_of_sa_to_dq_le],
  rw inv_comps_apply f _,
  simp only [discrete_quotient.of_le_proj_apply],
end

def hom_of_sa_to_dq_le {f g : structured_arrow S to_Profinite}
  (h : hom_to_dq f.hom ≤ hom_to_dq g.hom) [nonempty S] : f ⟶ g :=
structured_arrow.hom_mk (fintype_map_of_sa_to_dq_le h) (w_lemma h)

variable (S)

def dq_sa_functor :
  discrete_quotient S ⥤ structured_arrow S to_Profinite :=
{ obj := λ Si, structured_arrow.mk (dq_to_hom Si),
  map := λ Si Sj g,
    structured_arrow.hom_mk' (structured_arrow.mk (dq_to_hom Si)) (S.fintype_diagram.map g), }

def sa_dq_functor :
  structured_arrow S to_Profinite ⥤ discrete_quotient S :=
{ obj := λ f, hom_to_dq f.hom,
  map := λ f g φ, hom_of_le $ sa_to_dq_le φ, }

def unit_iso_dq_sa :
  𝟭 (discrete_quotient S) ≅ (dq_sa_functor S) ⋙ (sa_dq_functor S) :=
{ hom := { app := λ Si, eq_to_hom (htdq_comp_dqth_eq_id Si), },
  inv := { app := λ Si, eq_to_hom (htdq_comp_dqth_eq_id Si).symm, }, }

instance : faithful (dq_sa_functor S) :=
  faithful.of_comp_iso (unit_iso_dq_sa S).symm

instance es_sadq : ess_surj (sa_dq_functor S) :=
begin
  constructor,
  intros Y,
  use (dq_sa_functor S).obj Y,
  use (unit_iso_dq_sa S).inv.app Y,
  exact (unit_iso_dq_sa S).hom.app Y,
end

instance (Si : discrete_quotient S) :
  inhabited (costructured_arrow (sa_dq_functor S) Si) :=
{ default := costructured_arrow.mk ((unit_iso_dq_sa S).inv.app Si) }

instance [nonempty S] : full (sa_dq_functor S) :=
functor.full_of_surjective (sa_dq_functor S) $ λ f g, begin
  intros p,
  use hom_of_sa_to_dq_le (le_of_hom p),
  exact hom_eq_dq _ _,
end

lemma le_self_sa (f : structured_arrow S to_Profinite) :
  hom_to_dq ((dq_sa_functor S).obj ((sa_dq_functor S).obj f)).hom ≤ hom_to_dq f.hom :=
begin
  dsimp [sa_dq_functor, dq_sa_functor],
  rw ← htdq_comp_dqth_eq_id _,
  exact le_refl _,
end

def counit_sa_dq [nonempty S] : sa_dq_functor S ⋙ dq_sa_functor S ⟶ 𝟭 _ :=
{ app := λ f, hom_of_sa_to_dq_le (le_self_sa S f),
  naturality' :=
  begin
    intros f g p,
    let f' := (dq_sa_functor S).obj ((sa_dq_functor S).obj f),
    let g' := (dq_sa_functor S).obj ((sa_dq_functor S).obj g),
    let p' : f' ⟶ g' := (dq_sa_functor S).map ((sa_dq_functor S).map p),
    ext,
    have hf : function.surjective f'.hom := (discrete_quotient.proj_surjective _),
    have hg : function.surjective g'.hom := (discrete_quotient.proj_surjective _),
    obtain ⟨w, hw⟩ := surj_hom_to_dq_to_right_of_fhom_surj _ hf x,
    obtain ⟨x', hx'⟩ := hf x,
    obtain ⟨w', hw'⟩ := discrete_quotient.proj_surjective _ w,
    dsimp,
    change (dq_sa_functor S).map ((sa_dq_functor S).map p) with p',
    change (dq_sa_functor S).obj ((sa_dq_functor S).obj g) with g',
    change (dq_sa_functor S).obj ((sa_dq_functor S).obj f) with f',
    dsimp [hom_of_sa_to_dq_le],
    dsimp [fintype_map_of_sa_to_dq_le],
    rw ← hw,
    rw right_hom_left_inv_apply w,
    rw ← hw',
    simp only [discrete_quotient.of_le_proj_apply],
    rw fhom_eq_proj_apply f w',
    rw fhom_eq_proj_apply f' w',
    cases p,
    dsimp [auto_param_eq] at p_w',
    simp only [category_theory.category.id_comp] at p_w',
    simp only [Fintype.to_Profinite_map_apply, Profinite.coe_comp, function.comp_app],
    have : p'.right (f'.hom w') = g'.hom w',
    { have h := p'.w',
      dsimp [auto_param_eq] at h,
      simp only [category_theory.category.id_comp] at h,
      rw h,
      refl },
    rw this,
    rw ← fhom_eq_proj_apply g' w',
    rw right_hom_left_inv_apply ((hom_to_dq g'.hom).proj w'),
    simp only [discrete_quotient.of_le_proj_apply],
    rw fhom_eq_proj_apply g w',
    rw p_w',
    refl,
  end, }

lemma at_most_one_map_from_dq {Si : discrete_quotient S} {f : structured_arrow S to_Profinite}
  (p q : (dq_sa_functor S).obj Si ⟶ f) : p = q :=
begin
  ext,
  have hf : function.surjective ((dq_sa_functor S).obj Si).hom :=
      (discrete_quotient.proj_surjective _),
  obtain ⟨x', hx⟩ := hf x,
  rw ← hx,
  have hp : p.right (((dq_sa_functor S).obj Si).hom x') = f.hom x',
  { cases p,
    dsimp at *,
    simp only [category_theory.category.id_comp] at p_w',
    rw p_w',
    refl, },
  have hq : q.right (((dq_sa_functor S).obj Si).hom x') = f.hom x',
  { cases q,
    dsimp at *,
    simp only [category_theory.category.id_comp] at q_w',
    rw q_w',
    refl, },
  rw [hp, hq],
end

lemma at_most_one_map_from_dq_apply {Si : discrete_quotient S} {f : structured_arrow S to_Profinite}
  {p q : (dq_sa_functor S).obj Si ⟶ f} : ∀ x, p.right x = q.right x :=
begin
  intro x,
  rw at_most_one_map_from_dq S p q,
end

lemma htdq_comp_dqth_eq_id_functors (Si : discrete_quotient S) :
  Si = (sa_dq_functor S).obj ((dq_sa_functor S).obj Si) :=
begin
  dsimp [sa_dq_functor, dq_sa_functor],
  exact htdq_comp_dqth_eq_id _,
end

def dq_sa_adjunction [nonempty S] : dq_sa_functor S ⊣ sa_dq_functor S :=
adjunction.mk_of_unit_counit
{ unit := (unit_iso_dq_sa S).hom,
  counit := counit_sa_dq S,
  left_triangle' :=
  begin
    ext,
    exact at_most_one_map_from_dq_apply _ _,
  end,
  right_triangle' := by refl,
}

instance sa_dq_initial [nonempty S] : (sa_dq_functor S).initial :=
{ out := λ Si, zigzag_is_connected (λ f g,
  begin
    let h := functor.ess_image.get_iso ((es_sadq S).mem_ess_image Si),
    let sc := costructured_arrow.mk h.hom,
    let fc := costructured_arrow.hom_mk ((full.preimage (f.hom ≫ h.inv)) : f.left ⟶ sc.left)
      (by simp only [category_theory.category.comp_id,
        category_theory.iso.inv_hom_id,
        category_theory.costructured_arrow.mk_hom_eq_self,
        category_theory.category.assoc,
        category_theory.full.witness]),
    let gc := costructured_arrow.hom_mk ((full.preimage (g.hom ≫ h.inv)) : g.left ⟶ sc.left)
      (by simp only [category_theory.category.comp_id,
        category_theory.iso.inv_hom_id,
        category_theory.costructured_arrow.mk_hom_eq_self,
        category_theory.category.assoc,
        category_theory.full.witness]),
    have hf : zag f sc := by { left, use fc, },
    have hg : zag sc g := by { right, use gc, },
    unfold zigzag,
    rw relation.refl_trans_gen.cases_tail_iff zag f g,
    right,
    use sc,
    refine ⟨_, hg⟩,
    rw relation.refl_trans_gen.cases_tail_iff zag f sc,
    right,
    use f,
    exact ⟨(by tauto), hf⟩,
  end)  }

instance dq_sa_initial [nonempty S] : (dq_sa_functor S).initial :=
  functor.initial_of_adjunction (dq_sa_adjunction S)
