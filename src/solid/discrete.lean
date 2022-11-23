import topology.category.Profinite.as_limit
import topology.category.Top.basic
import category_theory.limits.has_limits
import solid.colim_hom_injective

open category_theory
open category_theory.limits
open Profinite

noncomputable theory

universe u

lemma to_im_cont {X Y : Top.{u}} (f : X ⟶ Y) : continuous (set.range_factorization f) :=
  continuous.subtype_mk (continuous_map.continuous f) (λ x, set.mem_range_self x)

def im {X Y : Top.{u}} (f: X ⟶ Y) : Top.{u} := ⟨(set.range f), subtype.topological_space⟩

instance im_discrete {X Y : Top.{u}} (f : X ⟶ Y) [discrete_topology Y] : discrete_topology (im f) :=
  subtype.discrete_topology

def to_im {X Y : Top.{u}} (f : X ⟶ Y) : X ⟶ im f := ⟨set.range_factorization f, to_im_cont f⟩

lemma to_im_surj {X Y : Top.{u}} (f : X ⟶ Y) : function.surjective (to_im f) := by tidy

lemma to_Top_iso_limit (S : Profinite.{u}) : to_Top.obj S ≅ limit (S.diagram ⋙ to_Top) :=
begin
  sorry,
end

def im_as_discrete_quotient {S : Profinite.{u}} {X : Top.{u}} (g : (to_Top.obj S) ⟶ X) [discrete_topology X] : discrete_quotient S :=
begin
  let f := to_im g,

  have hdisc : discrete_topology (im g),
  apply_instance,

  -- Defining the equivalence relation of the image
  fconstructor,
  intros s1 s2,

  exact f s1 = f s2,
  split,
  tauto,
  split,
  tauto,
  intros x y z,
  dsimp,
  intros h j,
  rw h,
  exact j,

  -- Clopen fibres
  intros x,
  have h : {s2 : S | f x = f s2} = f ⁻¹' {f x},
  ext,
  split,
  intros hx1,
  have hx1' : f x = f x_1,
  exact hx1,
  exact mem_id_rel.mpr (eq.symm hx1),

  intros hx1,
  have hx1' : f x = f x_1,
  exact mem_id_rel.mp (eq.symm hx1),
  exact hx1',

  rw h,

  have hfc : continuous f,
  exact continuous_map.continuous f,

  refine (quotient_map.is_clopen_preimage _).mpr _,

  -- Show that f is a quotient map
  fconstructor,
  exact to_im_surj g,

  ext,
  split,

  -- -->
  intros hx1,
  unfold topological_space.coinduced,
  have hx1' : is_open (f ⁻¹' x_1),
  exact continuous_def.mp hfc x_1 hx1,
  exact hx1',

  -- <--
  intros hx1,
  exact is_open_discrete x_1,

  split,
  exact is_open_discrete _,
  exact is_closed_discrete _,
end

lemma im_eq_quotient_by_kernel {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
↥(im_as_discrete_quotient f) = quotient (setoid.ker (to_im f)) :=
begin
  refl,
end

def incl_im {X Y : Top.{u}} (f : X ⟶ Y) : (im f) ⟶ Y :=
begin
  let i : set.range f → Y := λ y, y,
  -- intros y,
  -- exact y,
  have hi : continuous i := continuous_induced_dom,
  exact ⟨i, hi⟩,
end

lemma factor_f {X Y : Top.{u}} (f : X ⟶ Y) : f = (to_im f) ≫ (incl_im f) :=
begin
  ext,
  refl,
end

lemma im_finite {X : CompHaus.{u}} {Y : Top.{u}}
  [discrete_topology Y] (f : (CompHaus.to_Top X) ⟶ Y) : fintype (im f) :=
begin
  have X_comp : is_compact (set.univ : set X) := compact_univ,
  have im_comp : is_compact (set.range f),
  refine is_compact_range _,
  exact continuous_map.continuous f,
  rw is_compact_iff_finite at im_comp,
  exact set.finite.fintype im_comp,
end

def im_as_fintype {X : CompHaus.{u}} {Y : Top.{u}}
  [discrete_topology Y] (f : (CompHaus.to_Top X) ⟶ Y) : Fintype.{u} :=
begin
  exact ⟨(im f), (im_finite f)⟩,
end

def im_as_eq_rel {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
  setoid (to_Top.obj S) :=
begin
  exact ⟨(im_as_discrete_quotient f).rel, (im_as_discrete_quotient f).equiv⟩,
end

def im_as_quotient {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
  [discrete_topology X] : Type u := quotient (im_as_eq_rel f)

def map_to_im_as_quotient' {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
   [discrete_topology X] : (to_Top.obj S) → Top.discrete.obj (im_as_quotient f) := quotient.mk'

lemma cont_map_to_im_as_quotient' {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
   [discrete_topology X] : continuous (map_to_im_as_quotient' f) := (im_as_discrete_quotient f).proj_continuous

def map_to_im_as_quotient {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
   [discrete_topology X] : (to_Top.obj S) ⟶ Top.discrete.obj (im_as_quotient f) := ⟨(map_to_im_as_quotient' f), (cont_map_to_im_as_quotient' f)⟩

lemma im_eq_quotient {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
↥(im_as_discrete_quotient f) = quotient (im_as_eq_rel f) :=
begin
  refl,
end

def incl_im' {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
  Top.discrete.obj (Fintype.incl.obj (S.fintype_diagram.obj (im_as_discrete_quotient f))) ⟶ X :=
begin
  have heq1 : (im_as_discrete_quotient f).rel = (im_as_eq_rel f).rel := by refl,
  have h : ∀ a b : (to_Top.obj S), (im_as_discrete_quotient f).rel a b → f a = f b,
  intros a b,
  intros h',
  rw factor_f f,
  have h2 : (to_im f) a = (to_im f) b,
  exact h',
  have h3 : (to_im f ≫ incl_im f) a = (incl_im f) ((to_im f) a),
  refl,
  rw h3,
  rw h2,
  refl,
  let setmap : quotient (im_as_eq_rel f) → X := quot.lift f h,
  -- let setmap := incl_im_sets f,
  -- rw _inst_3 at setmap,
  rw ← (im_eq_quotient f) at setmap,
  have setmap2 : Top.discrete.obj (Fintype.incl.obj (S.fintype_diagram.obj (im_as_discrete_quotient f)))
    → (im_as_discrete_quotient f) := λ x, x,
  let g := setmap ∘ setmap2,
  have hg : continuous g,
  { exact continuous_bot,
  },
  exact ⟨g, hg⟩,
end


lemma discreteness_condition_necessary {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] :
  is_iso (can_map_from_colim_of_homs_to_hom_from_limit X (S.diagram ⋙ Profinite.to_Top)) :=
begin
  refine (is_iso_iff_bijective (can_map_from_colim_of_homs_to_hom_from_limit X (S.diagram ⋙ Profinite.to_Top))).mpr _,
  split,
  { refine can_is_injective _ _ _,
    intros i,
    rw Top.epi_iff_surjective _,
    refine quotient_map.surjective _,
    sorry, },
  { intros f,
    let a := colimit.ι ((S.diagram ⋙ Profinite.to_Top).op ⋙ yoneda.obj X ⋙ ulift_functor) (opposite.op (im_as_discrete_quotient ((to_Top_iso_limit S).hom ≫ f.down))),
    fconstructor,
    { exact a.app (ulift_functor.map (incl_im ((to_Top_iso_limit S).hom ≫ f.down))) },
    { ext,
      unfold can,
      tidy } },
end

-- lemma discreteness_condition_sufficient (S : Profinite.{u}) (X : CondensedSet.{u})
