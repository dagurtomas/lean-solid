import solid.discrete_condensed
import challenge_notations

open_locale liquid_tensor_experiment nnreal zero_object
open liquid_tensor_experiment

def R_to_discrete (M : Ab) : ∀ i ≥ 0,
  Ext i (Condensed.of_top_ab ℝ) (Ab_to_Condensed.obj M) ≅ 0 :=
sorry
