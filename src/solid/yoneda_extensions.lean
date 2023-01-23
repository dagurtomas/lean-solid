import category_theory.limits.kan_extension
import category_theory.limits.preserves.basic

noncomputable theory

open category_theory

universes v v₁ v₂ u₁ u₂

variables {S : Type u₁} {L : Type u₂} -- {D : Type u₃}
variables [category.{v₁} S] [category.{v₂} L] -- [category.{v₃} D]
variables (ι : S ⥤ L)

#check Lan.diagram ι ι

lemma cocontinuous_commutes (G : L ⥤ L)
  [∀ X, limits.preserves_colimits_of_shape (costructured_arrow ι X) G]
  [∀ X, limits.has_colimits_of_shape (costructured_arrow ι X) L] :
  (Lan ι).obj (ι ⋙ G) = ((Lan ι).obj ι) ⋙ G :=
begin
  unfold Lan,
  dsimp,
  unfold Lan.loc,
  apply category_theory.functor.ext,
  swap,
  { intros X,
    dsimp,
    -- have h : limits.preserves_colimits_of_shape (costructured_arrow ι X) G := by apply_instance,
    have h : limits.preserves_colimit (Lan.diagram ι ι X) G := by apply_instance,
    --let c := (limits.colimit (Lan.diagram ι ι X)).cone
    sorry, },
  sorry,
end
