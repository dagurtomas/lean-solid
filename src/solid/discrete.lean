import condensed.ab
import topology.category.Profinite.as_limit
import topology.category.Top.basic
import category_theory.limits.has_limits


open category_theory
open Profinite
-- open classical
open Condensed

noncomputable theory

-- set_option pp.universes true

universe u

variables (S T : Profinite.{u}) -- [inhabited (discrete_quotient S)]
variables (X : Top.{u}) -- [discrete X]
variables (i j : discrete_quotient S)
variables (Y : Fintype.{u})

def Cont_out (Y : Top.{u}) : Top.{u} ⥤ Type u :=
{
  obj := λ X, (Y ⟶ X),
  map := λ X₁ X₂ f, (λ g, g ≫ f),
  map_id' := by { intros, ext, refl, },
  map_comp' := by { intros, ext, refl, },
}

def Cont_in (X : Top.{u}) : Top.{u}ᵒᵖ ⥤ Type u :=
{
  obj := λ Y, (Y.unop ⟶ X),
  map := λ X₁ X₂ f, (λ g, f.unop ≫ g),
  map_id' := by { intros, ext, refl, },
  map_comp' := by { intros, ext, refl, },
}

def fin_incl : Fintype.{u} ⥤ Type u :=
{
  obj := λ X, X,
  map := λ X₁ X₂ f, f,
  map_id' := by { intros, refl, },
  map_comp' := by { intros, refl, },
}

def Colim_diagram (X : Top.{u}) : (discrete_quotient S)ᵒᵖ ⥤ Type u :=
  S.fintype_diagram.op ⋙ fin_incl.op ⋙ Top.discrete.op ⋙ (Cont_in X)

instance S_colim_exists : limits.has_colimit (Colim_diagram S X) :=
begin
  apply_instance,
end

def CSX_as_cone_map (S : Profinite.{u}) (X : Top.{u}) : (Colim_diagram S X) ⟶ (category_theory.functor.const (discrete_quotient S)ᵒᵖ).obj ((to_Top.obj S) ⟶ X) :=
{app :=
    begin
      intros i,
      refine as_hom _,
      dsimp,
      intros a,
      exact (S.as_limit_cone.π.app i.unop) ≫ a,
    end,
  naturality' :=
    begin
      intros i j f,
      tidy,
    end,
}

def CSX_as_cone (S : Profinite.{u}) (Y : Top.{u}) : limits.cocone (Colim_diagram S Y) :=
{
  X := ((to_Top.obj S) ⟶ Y),
  ι := CSX_as_cone_map S Y,
}

def can (S : Profinite.{u}) (X : Top.{u}) : ((limits.colimit (Colim_diagram S X)) ⟶ ((to_Top.obj S) ⟶ X)) :=
begin
  exact limits.colimit.desc (Colim_diagram S X) (CSX_as_cone S X),
end

lemma to_im_cont {X Y : Top.{u}} (f : X ⟶ Y) : continuous (set.range_factorization f) :=
begin
  have hfc : continuous f,
  exact continuous_map.continuous f,
  have h : ∀ (x : X), f x ∈ set.range f,
  intros x,
  exact set.mem_range_self x,
  exact continuous.subtype_mk hfc h,
end

def im {X Y : Top.{u}} (f: X ⟶ Y) : Top.{u} :=
begin
  have imf_top : topological_space (set.range f),
  apply_instance,
  exact ⟨(set.range f), imf_top⟩,
end

instance im_discrete {X Y : Top.{u}} (f : X ⟶ Y) [discrete_topology Y] : discrete_topology (im f) :=
begin
  exact subtype.discrete_topology,
end

def to_im {X Y : Top.{u}} (f : X ⟶ Y) : X ⟶ im f :=
begin
  refine ⟨set.range_factorization f, _⟩,
  norm_num,
  exact to_im_cont f,
end

lemma to_im_surj {X Y : Top.{u}} (f : X ⟶ Y) : function.surjective (to_im f) :=
begin
  tidy,
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

-- def incl_im {X Y : Top.{u}} (f : X ⟶ Y) : (im f) ⟶ Y :=
-- begin
--   exact as_hom (set.inclusion (set.range f) ⊆ set.univ)
-- end

lemma discreteness_condition_necessary (S : Profinite.{u}) (X : Top.{u}) [discrete X] : is_iso (can S X) :=
begin
  refine (is_iso_iff_bijective (can S X)).mpr _,
  split,
  unfold function.injective,
  intros a b,
  sorry,
  unfold function.surjective,
  intros f,
  sorry,
end

-- lemma discreteness_condition_sufficient (S : Profinite.{u}) (X : CondensedSet.{u})
