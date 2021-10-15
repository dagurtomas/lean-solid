import condensed.proetale_site
import for_mathlib.presieve
import topology.category.Profinite.projective
import for_mathlib.Profinite.disjoint_union
import condensed.is_proetale_sheaf

/-!
# Condensed sets

Defines the category of condensed sets and condensed structures.
*Strictly speaking* these are pyknotic, but we hope that in the context of Lean's type theory they
serve the same purpose.

-/

open category_theory category_theory.limits

universes w v u

variables {C : Type u} [category.{v} C]

/-- The category of condensed sets. -/
@[derive category]
def CondensedSet : Type (u+2) := SheafOfTypes.{u+1} proetale_topology.{u}

/-- The category of condensed `A`. Applying this to `A = Type*` is *equivalent* but not the same
as `CondensedSet`. -/
@[derive category]
def Condensed (C : Type u) [category.{v} C] := Sheaf proetale_topology.{w} C

example : category.{u+1} (Condensed.{u} Ab.{u+1}) := infer_instance
example : category.{u+37} (Condensed.{u} Ring.{u+37}) := infer_instance

open opposite

noncomputable theory

variables (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
variables (P : Profinite.{w}ᵒᵖ ⥤ Type u)

-- TODO: Move this
lemma subsingleton_of_is_proetale_sheaf_of_types
  (h : P.is_proetale_sheaf_of_types) (Z : Profinite) (hZ : is_empty Z) :
  subsingleton (P.obj (op Z)) :=
begin
  specialize h pempty Z pempty.elim (λ a, a.elim) hZ.elim (λ a, a.elim) (λ a, a.elim),
  obtain ⟨t,ht1,ht2⟩ := h,
  constructor,
  intros x y,
  have : x = t, { apply ht2, exact λ a, a.elim },
  have : y = t, { apply ht2, exact λ a, a.elim },
  cc,
end

-- TODO: Move this
theorem category_theory.functor.is_proetale_sheaf_of_types_prod_of_is_proetale_sheaf_of_types
  (h : P.is_proetale_sheaf_of_types) (α : Type w) [fintype α] (X : α → Profinite.{w}) :
  function.bijective (λ (x : P.obj (op $ Profinite.sigma X)) (a : α),
    P.map (Profinite.sigma.ι _ a).op x) :=
begin
  split,
  { intros x y hh,
    dsimp at hh,
    specialize h α (Profinite.sigma X) X (Profinite.sigma.ι X)
      (Profinite.sigma.ι_jointly_surjective X)
      (λ a, P.map (Profinite.sigma.ι X a).op x) _,
    { intros a b Z g₁ g₂ hhh,
      dsimp,
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _,
      simp_rw [← P.map_comp, ← op_comp, hhh] },
    obtain ⟨t,ht1,ht2⟩ := h,
    have hx : x = t,
    { apply ht2,
      intros a,
      refl },
    have hy : y = t,
    { apply ht2,
      intros a,
      apply_fun (λ e, e a) at hh,
      exact hh.symm },
    rw [hx, ← hy] },
  { intros bb,
    dsimp,
    specialize h α (Profinite.sigma X) X (Profinite.sigma.ι X)
      (Profinite.sigma.ι_jointly_surjective X) bb _,
    { intros a b Z g₁ g₂ hhh,
      by_cases hZ : is_empty Z,
      { haveI := subsingleton_of_is_proetale_sheaf_of_types P h Z hZ, apply subsingleton.elim },
      simp at hZ,
      obtain ⟨z⟩ := hZ,
      have : a = b,
      { apply_fun (λ e, (e z).1) at hhh,
        exact hhh },
      subst this,
      have : g₁ = g₂,
      { ext1 t,
        apply_fun (Profinite.sigma.ι X a),
        swap, { exact Profinite.sigma.ι_injective X a },
        apply_fun (λ e, e t) at hhh,
        exact hhh },
      rw this },
    obtain ⟨t,ht1,ht2⟩ := h,
    use t,
    ext,
    apply ht1 }
end

-- TODO: Move this
theorem category_theory.functor.is_proetale_sheaf_of_types_projective_iff :
  P.is_proetale_sheaf_of_types_projective ↔ P.is_proetale_sheaf_of_types :=
begin
  split,
  { introsI h α _ B X f surj x compat,
    let T := Profinite.sigma X,
    let π := Profinite.sigma.desc X f,
    sorry },
  { intros h α X _,
    apply P.is_proetale_sheaf_of_types_prod_of_is_proetale_sheaf_of_types h α X }
end

lemma maps_comm {S S' : Profinite.{u}} (f : S' ⟶ S) :
  X.map f.op ≫ X.map (pullback.fst : pullback f f ⟶ S').op = X.map f.op ≫ X.map pullback.snd.op :=
by rw [←X.map_comp, ←op_comp, pullback.condition, op_comp, X.map_comp]

def natural_fork {S S' : Profinite.{u}} (f : S' ⟶ S) :
  fork (X.map pullback.fst.op) (X.map pullback.snd.op) :=
fork.of_ι (X.map (quiver.hom.op f)) (maps_comm X f)

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_terminal
  (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := sorry

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_binary_products
  (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := sorry

structure condensed_type_condition : Prop :=
(empty : nonempty X.preserves_terminal)
(bin_prod : nonempty X.preserves_binary_products)
(pullbacks : ∀ {S S' : Profinite.{u}} (f : S' ⟶ S) [epi f],
  nonempty (is_limit (natural_fork X f)))

-- (BM): I'm 90% sure this is true as stated, the forward direction is about halfway done.
lemma sheaf_condition_iff :
  presieve.is_sheaf proetale_topology X ↔ condensed_type_condition X :=
sorry

-- TODO: Double check this definition...
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T ⋙ ulift_functor.{u+1}, sorry⟩,
  map := λ T₁ T₂ f, whisker_left _ $ whisker_right (yoneda.map f) _ }

/-
-- TODO: State `sheaf_condition_iff` for presheaves taking values in `A` for `A` with appropriate
-- structure.
-- TODO: Use `sheaf_condition_iff` to define the functor of Example 1.5, it might look like this:
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T,
  begin
    rw sheaf_condition_iff, refine ⟨⟨_⟩, ⟨_⟩, _⟩,
    all_goals { sorry }
  end⟩,
  map := λ T₁ T₂ f, whisker_left Profinite.to_Top.op (yoneda.map f) }
-/

-- TODO: Use the above to prove the first part of Proposition 1.7:
lemma embed_Top_faithful : faithful embed_Top := sorry

-- TODO: Construct the left adjoint to `embed_Top` as in the second part of Proposition 1.7.
