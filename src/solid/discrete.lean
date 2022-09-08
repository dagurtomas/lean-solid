import condensed.ab
import topology.category.Profinite.as_limit
import topology.category.Top.basic
import category_theory.limits.has_limits


open category_theory
open Profinite
-- open classical
open Condensed

noncomputable theory

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

-- def ftoim (X Y : Top.{u}) (f : X ⟶ Y) : X → set.range f :=
--   set.range_factorization f

variables (Z : Top.{u})

variables (f : X ⟶ Z)

#check set.range_factorization f
#check continuous (set.range_factorization f)

#check {x // x ∈ (set.range f)}

#check set.range f
variables U : set (set.range f)
#check U

def incl (X : Type u) (Y : set X) : {y // y ∈ Y} → X :=
  begin
    intros y,
    exact y,
  end

lemma incl_inj (X : Type u) (Y : set X) : function.injective (incl X Y) :=
begin
  unfold function.injective,
  intros a b,
  intros h,
  ext1,
  exact h,
end

def set_trans (X : Type u) (Y : set X) (Z : set Y) : set X :=
  begin
    let Z' := incl Y Z,
    let Y' := incl X Y,
    let f : ↥Y → {y // y ∈ Y} :=
    begin
      intros y,
      exact y,
    end,
    let Z'' := Y' ∘ f ∘ Z',
    exact set.range Z'',
  end

lemma incl_set_trans_comp (X : Type u) (Y : set X) (Z : set Y) : Z = (set_trans X Y Z) ∘ (incl X Y) :=
  begin
    ext,
    split,
    intros hx,
    norm_num,
    fconstructor,
    have hx' : x ∈ Z,
    exact hx,
    exact ⟨x, hx'⟩,
    refl,

    intros hx,
    norm_num at hx,
    cases hx,
    have hx' : x = (incl Y Z) hx_w,
    apply_fun (incl X Y),
    exact hx_h.symm,
    exact incl_inj X Y,
    rw hx',
    cases hx_w,
    exact hx_w_property,
  end

#check f
#check (incl _ _) ∘ (set.range_factorization f)

lemma ftoim_cont : ∀ (X Y : Top.{u}), ∀ (f : X ⟶ Y), continuous (set.range_factorization f) :=
begin
  intros X Y f,
  fconstructor,
  intros U,
  intros hU,
  let U' := set_trans Y (set.range f) U,

  have hfc : continuous f,
  exact continuous_map.continuous f,

  have hU''' : U' = set_trans Y (set.range f) U,
  refl,

  have hU'' : U = (incl _ _) ⁻¹' U',
  ext,
  split,

  intros hx1,
  have hx1hU' : (incl _ _) x ∈ U',

  rw hU''',
  have hsix1 : ((set_trans Y (set.range f) U) ∘ (incl Y (set.range f))) x,
  have hcomp : (set_trans Y (set.range f) U) ∘ (incl Y (set.range f)) = U,
  exact (incl_set_trans_comp _ _ _).symm,
  rw hcomp,
  exact hx1,
  exact hsix1,
  exact hx1hU',

  intros hx1,
  have hx1hU' : (incl _ _) x ∈ U',
  exact hx1,
  have hx1hstU' : ((set_trans Y (set.range f) U) ∘ (incl _ _)) x,
  exact hx1hU',
  rw ← (incl_set_trans_comp Y (set.range f) U) at hx1hstU',
  exact hx1hstU',

  have h : (incl Y (set.range f)) ∘ (set.range_factorization f) = f,
  refl,

  have hU' : (f ⁻¹' (U')) = set.range_factorization f ⁻¹' U,

  ext,

  split,
  intros hx,

  have hfx : f x ∈ U',
  exact hx,
  suffices hsfx : ((set.range_factorization f) x) ∈ U,
  exact hsfx,

  have hfx' : ((incl _ _) ∘ (set.range_factorization f)) x ∈ U',
  exact hfx,

  rw hU'',
  exact hfx',

  intros hx,

  have hfx : (set.range_factorization f) x ∈ U,
  exact hx,
  rw hU'' at hfx,

  have hfsx : ((incl _ _) ∘ (set.range_factorization f)) x ∈ U',
  exact hfx,
  rw h at hfsx,
  exact hfsx,
  sorry,
end

variables W : set X
variables R : set (set.range f)

#check (set.range_factorization f) ⁻¹' R
#check set.range_factorization f ⁻¹' R


#check W
#check {x // x ∈ W}

#check coe W

lemma discreteness_condition_necessary (S : Profinite.{u}) (X : Top.{u}) [discrete X] : is_iso (can S X) :=
begin
  refine (is_iso_iff_bijective (can S X)).mpr _,
  split,
  unfold function.injective,
  intros a b,
  unfold function.surjective,
  intros f,
  let fc := f.continuous,
  let imf := set.range f, -- f '' set.univ,
  have X_top : topological_space X,
  apply_instance,
  let ftoim : (to_Top.obj S) ⟶ (Top.discrete.obj imf) :=
  {
    to_fun := set.range_factorization f,
    continuous_to_fun :=
    begin
      fconstructor,
      intros s,
      intros hs,
      have h2 : X_top.is_open imf,
      rw (set.Union_of_singleton_coe imf).symm,
      have X_top_discrete : discrete_topology X,
      sorry,
      apply is_open_sUnion,
      intros t,
      intros ht,
      cases ht,
      have htt : t = {ht_w},
      apply_assumption,
      rw htt,
      have imf_top_discrete : discrete_topology imf,
      sorry,
      sorry,
      sorry,
      -- exact singletons_open_iff_discrete.mpr imf_top_discrete ht_w,
    end,
  },
  sorry,
  -- exact λ x, f x,
  -- have im_subspace : topological_space imf,
  -- apply_instance,

  -- have h : discrete imf,
  -- refine {as := _},
  -- have S_inhabited : inhabited (to_Top.obj S),
  -- swap,
  -- exact f default,

  -- sorry,
end

-- lemma discreteness_condition_sufficient (S : Profinite.{u}) (X : CondensedSet.{u})
