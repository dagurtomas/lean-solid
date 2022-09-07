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
