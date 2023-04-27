import solid.discrete_condensed
import solid.loc_const_underlying_adjunction

noncomputable theory

open category_theory
open category_theory.adjunction

def Type_to_Condensed_iso : Type_to_Condensed ≅ loc_const_Condensed_functor :=
  left_adjoint_uniq Condensed_Type_adjunction loc_const_adjunction
