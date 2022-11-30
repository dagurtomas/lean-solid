import condensed.top_comparison
import solid.discrete

open category_theory
open category_theory.adjunction

universe u

def Type_to_Condensed : Type (u+1) ⥤ CondensedSet.{u+1} := Top.discrete ⋙ Top_to_Condensed

def Condensed_to_Type : CondensedSet.{u} ⥤ Type (u+1) :=
{
  obj := λ X, X.val.obj (opposite.op point),
  map := λ X₁ X₂ f, f.val.app (opposite.op point)
}

def Condensed_u_down : CondensedSet.{u+1} ⥤ CondensedSet.{u} :=
{
  obj := λ X, {
    val := sorry,
    cond := sorry,
  },
  map := sorry,
}


def Condensed_Type_adjunction : Type_to_Condensed ⋙ Condensed_u_down ⊣ Condensed_to_Type := sorry
