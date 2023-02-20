import topology.category.Profinite.as_limit
import category_theory.limits.kan_extension
import solid.new_final
import category_theory.equivalence
import category_theory.functor.flat
import condensed.basic

/- solid.new_final is just the newer version of category_theory.functor.final which allows
   large categories. -/

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
comap ⊥ f.continuous

lemma sa_to_dq_le {S : Profinite.{u}} {f g : structured_arrow S to_Profinite} (φ : f ⟶ g) :
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

lemma hom_eq_dq {S : Profinite.{u}} {Si Sj : discrete_quotient S} (f g : Si ⟶ Sj) : f = g :=
  (eq_iff_true_of_subsingleton f g).mpr (by triv)

instance {S : Profinite.{u}} (Si : discrete_quotient S) :
  inhabited (costructured_arrow (sa_dq_functor S) Si) :=
{ default := costructured_arrow.mk ((unit_iso_dq_sa S).inv.app Si) }

lemma dq_map_injective {S : Profinite.{u}} (f : structured_arrow S to_Profinite) :
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

def proj_bot_inv {S : Profinite.{u}} (f : structured_arrow S to_Profinite) :=
(function.surj_inv (proj_bot_bijective.2 : function.surjective
  (⊥ : discrete_quotient f.right).proj))

def hom_to_dq_to_right {S : Profinite.{u}} (f : structured_arrow S to_Profinite) :
  hom_to_dq f.hom → f.right :=
(proj_bot_inv f) ∘ map (le_refl (comap ⊥ f.hom.continuous))

instance nonempty_dq {S : Profinite.{u}} (Si : discrete_quotient S) [nonempty S] : nonempty Si :=
  by use Si.proj _inst_1.some

instance nonempty_hom_to_dq {S : Profinite.{u}} (f : structured_arrow S to_Profinite) [nonempty S] :
  nonempty (hom_to_dq f.hom) := @nonempty_dq S _ _inst_1

def right_to_hom_to_dq {S : Profinite.{u}} (f : structured_arrow S to_Profinite) [nonempty S] :
  f.right → hom_to_dq f.hom := function.inv_fun (hom_to_dq_to_right f)

lemma bot_proj_inv_injective {S : Profinite.{u}} (f : structured_arrow S to_Profinite)
  [nonempty S] : function.injective (proj_bot_inv f) :=
function.injective_surj_inv _

lemma inj_hom_to_dq_to_right {S : Profinite.{u}} (f : structured_arrow S to_Profinite) :
  function.injective (hom_to_dq_to_right f) :=
function.injective.comp (function.injective_surj_inv _) (dq_map_injective f)

def fintype_map_of_sa_to_dq_le {S : Profinite.{u}} {f g : structured_arrow S to_Profinite}
  (h : hom_to_dq f.hom ≤ hom_to_dq g.hom) [nonempty S] : f.right → g.right :=
(hom_to_dq_to_right g) ∘ (of_le h) ∘ (right_to_hom_to_dq f)

lemma fhom_eq_proj {S : Profinite.{u}} (f : structured_arrow S to_Profinite) :
  (hom_to_dq_to_right f) ∘ (hom_to_dq f.hom).proj = f.hom :=
begin
  unfold hom_to_dq_to_right,
  rw function.comp.assoc,
  rw map_proj,
  ext,
  dsimp,
  exact function.left_inverse_surj_inv proj_bot_bijective _,
end

lemma inv_comps_apply {S : Profinite.{u}} (f : structured_arrow S to_Profinite)
  (x : hom_to_dq f.hom) [nonempty S] :
  right_to_hom_to_dq f (hom_to_dq_to_right f x) = x :=
begin
  change right_to_hom_to_dq f (hom_to_dq_to_right f x) with
    ((right_to_hom_to_dq f) ∘ (hom_to_dq_to_right f)) x,
  unfold right_to_hom_to_dq,
  rw function.inv_fun_comp (inj_hom_to_dq_to_right f),
  simp only [id.def],
end

lemma w_lemma {S : Profinite.{u}} {f g : structured_arrow S to_Profinite}
  (h : hom_to_dq f.hom ≤ hom_to_dq g.hom) [nonempty S] :
  f.hom ≫ to_Profinite.map (fintype_map_of_sa_to_dq_le h) = g.hom :=
begin
  ext,
  dsimp,
  rw ← fhom_eq_proj f,
  rw ← fhom_eq_proj g,
  dsimp [fintype_map_of_sa_to_dq_le],
  -- rw function.inv_fun_comp,
  rw inv_comps_apply f _,
  simp only [discrete_quotient.of_le_proj_apply],
end

def hom_of_sa_to_dq_le {S : Profinite.{u}} {f g : structured_arrow S to_Profinite}
  (h : hom_to_dq f.hom ≤ hom_to_dq g.hom) [nonempty S] : f ⟶ g :=
structured_arrow.hom_mk (fintype_map_of_sa_to_dq_le h) (w_lemma h)

instance (S : Profinite.{u}) [nonempty S] : full (sa_dq_functor S) :=
functor.full_of_surjective (sa_dq_functor S) $ λ f g, begin
  intros p,
  use hom_of_sa_to_dq_le (le_of_hom p),
  exact hom_eq_dq _ _,
end

instance sa_dq_initial (S : Profinite.{u}) [nonempty S] : (sa_dq_functor S).initial :=
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
