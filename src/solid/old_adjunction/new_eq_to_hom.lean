import category_theory.eq_to_hom

universes v₁ v₂ v₃ u₁ u₂ u₃
-- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
open opposite

variables {C : Type u₁} [category.{v₁} C]

lemma comp_eq_to_hom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
  f ≫ eq_to_hom p = g ↔ f = g ≫ eq_to_hom p.symm :=
{ mp := λ h, h ▸ by simp,
  mpr := λ h, by simp [eq_whisker h (eq_to_hom p)] }

lemma eq_to_hom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
  eq_to_hom p ≫ g = f ↔ g = eq_to_hom p.symm ≫ f :=
{ mp := λ h, h ▸ by simp,
  mpr := λ h, h ▸ by simp [whisker_eq _ h] }

end category_theory
