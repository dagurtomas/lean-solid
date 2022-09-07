import condensed.ab
import topology.category.Profinite.as_limit
import topology.category.Top.basic
import topology.order
import group_theory.free_abelian_group
import category_theory.limits.has_limits
import category_theory.limits.kan_extension
import category_theory.category.ulift
import category_theory.structured_arrow


-- set_option pp.implicit true
set_option pp.universes true
-- set_option pp.all true

open category_theory
open Profinite
-- open classical
open Condensed

noncomputable theory


universe u
variables (S T : Profinite.{u})

def FinFree : Fintype.{u} ⥤ Ab.{u} :=
{
  obj := λ X, ⟨free_abelian_group X⟩,
  map := λ X₁ X₂ f, free_abelian_group.map f,
  map_id' := by { intros, ext, refl, },
  map_comp' := by { intros, ext, refl, }
}

def FinCondensed : Fintype.{u} ⥤ CondensedSet.{u} :=
{
  obj := λ X, (Top.discrete.obj X).to_Condensed,
  map := λ X₁ X₂ f, Top_to_Condensed.map (Top.discrete.map f),
  map_id' := by { intros, ext, refl, },
  map_comp' := by { intros, ext, refl, },
}

def FinCondensed' : Fintype.{u} ⥤ CondensedSet.{u} :=
  Fintype.to_Profinite ⋙ Profinite.to_Top ⋙ Top_to_Condensed

-- TODO: FinCondensed and FinCondensed' should be equivalent.

def FinFreeCondensed : Fintype.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  FinCondensed' ⋙ CondensedSet_to_Condensed_Ab.{u}

def ProfFreeCondensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} :=
  Profinite.to_Top ⋙ Top_to_Condensed ⋙ CondensedSet_to_Condensed_Ab.{u}

instance Condensed_Ab_has_limits_of_shape : ∀ (X : Profinite.{u}),
  limits.has_limits_of_shape
    (ulift_hom.{u+1} (ulift.{(u+1) (u+1)} (structured_arrow X Fintype.to_Profinite.{u}))) (Condensed.{u} Ab.{u+1}) :=
    begin
      intros X,
      have h : limits.has_limits (Condensed.{u} Ab.{u+1}),
      apply_instance,
      have h2 : category.{u (u+1)} (structured_arrow X Fintype.to_Profinite.{u}),
      apply_instance,
      apply_instance,
    end

instance Condensed_Ab_has_limits_of_shape2 : ∀ (X : Profinite.{u}),
  limits.has_limits_of_shape
    (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u})) (Condensed.{u} Ab.{u+1}) :=
    begin
      intros X,
      have h : limits.has_limits (Condensed.{u} Ab.{u+1}),
      apply_instance,
      have h2 : category.{u (u+1)} (structured_arrow X Fintype.to_Profinite.{u}),
      apply_instance,
      apply_instance,
    end

instance : category.{(u+1)} ((ulift_hom.{u+1} (structured_arrow S Fintype.to_Profinite.{u}))) :=
{ hom := λ A B, ulift.{u+1} $ A.obj_down ⟶ B.obj_down,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩}

instance Condensed_Ab_has_limits_of_shape3 : ∀ (X : Profinite.{u}),
  limits.has_limits_of_shape
    ((structured_arrow X Fintype.to_Profinite.{u})) (Condensed.{u} Ab.{u+1}) :=
    begin
      introsI X,
      haveI h : (structured_arrow X Fintype.to_Profinite.{u}) ≌ (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u})),
      exact ulift_hom.equiv,
      haveI h2 : (ulift_hom.{u+1} (structured_arrow X Fintype.to_Profinite.{u})) ≌ (structured_arrow X Fintype.to_Profinite.{u}),
      exact ulift_hom.equiv.symm,
      apply limits.has_limits_of_shape_of_equivalence h2,
      apply_instance,
    end

def Zsolid_functor_Ran : (Fintype.{u} ⥤ Condensed.{u} Ab.{u+1}) ⥤ (Profinite.{u} ⥤ Condensed.{u} Ab.{u+1}) :=
  (Ran Fintype.to_Profinite)

def Zsolid_functor : Profinite.{u} ⥤ Condensed.{u} Ab.{u+1} := Ran.loc Fintype.to_Profinite FinFreeCondensed

def α : (((whiskering_left Fintype Profinite (Condensed.{u} Ab.{u+1})).obj Fintype.to_Profinite).obj ProfFreeCondensed ⟶
       FinFreeCondensed) :=
       {app :=
          begin
            intros X,
            dsimp only [whiskering_left],
            exact eq_to_hom rfl,
          end,
        naturality' :=
          begin
            intros X Y f,
            tidy,
          end,
        }

-- α is just the identity natural transformation from FinFreeCondensed to itself

def Solidification_profinite : ProfFreeCondensed ⟶ Zsolid_functor :=
  (Ran.equiv Fintype.to_Profinite FinFreeCondensed ProfFreeCondensed).symm α

def Hom_into_CondAb (A : Condensed.{u} Ab.{u+1}) : (Condensed.{u} Ab.{u+1})ᵒᵖ ⥤ Type (u+1) :=
  {
    obj := λ X, (X.unop ⟶ A),
    map := λ X₁ X₂ f, λ g, f.unop ≫ g,
    map_id' := by { intros, ext, refl, },
    map_comp' := by { intros, ext, refl, },
  }

def is_solid (A : Condensed.{u} Ab.{u+1}) : Prop :=
  ∀ X : Profinite.{u}, is_iso ((Hom_into_CondAb A).map (Solidification_profinite.app X).op)
