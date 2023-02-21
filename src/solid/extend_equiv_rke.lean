import for_mathlib.Profinite.extend
import solid.dq_sa_comparison

noncomputable theory

open Profinite
open category_theory
open category_theory.limits

universes v u u'

variables {C : Type u} [category.{v} C] (F : Fintype.{v} ⥤ C)
variables {D : Type u'} [category.{v} D]
variables [∀ (X : Profinite), has_limit (X.fintype_diagram ⋙ F)]
variables [∀ (X : Profinite), has_limit (Ran.diagram Fintype.to_Profinite F X)]

def extend_equiv_rke : extend F ≅ Ran.loc Fintype.to_Profinite F := sorry

/- Should follow from `sa_dq_initial` -/
