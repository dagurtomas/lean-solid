import condensed.top_comparison
import condensed.adjunctions

noncomputable theory

universe u

open category_theory
open category_theory.adjunction
open opposite
open Profinite

def Type_to_constant_presheaf : Type (u+1) ⥤ Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
category_theory.functor.const _

def Type_to_Condensed : Type (u+1) ⥤ CondensedSet.{u} :=
Type_to_constant_presheaf ⋙ presheaf_to_CondensedSet

def presheaf_to_Type : (Profinite.{u}ᵒᵖ ⥤ Type (u+1)) ⥤ Type (u+1) :=
(evaluation _ _).obj $ op point

def Condensed_to_Type : CondensedSet.{u} ⥤ Type (u+1) :=
CondensedSet_to_presheaf ⋙ presheaf_to_Type

lemma Condensed_to_Type_eq_Condensed_evaluation_at_point :
  Condensed_to_Type = CondensedSet.evaluation point := by refl

def map_to_point (S : Profinite.{u}) : S ⟶ point := punit.elim S

def map_to_point_op (S : Profinite.{u}ᵒᵖ) : op point ⟶ S := (punit.elim S.unop).op

lemma presheaf_to_Type_comp_Type_to_constant_presheaf_eq_id (α : Type (u+1)) :
  presheaf_to_Type.obj (Type_to_constant_presheaf.obj α) = α := by refl

lemma presheaf_to_Type_map {F G : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (f : F ⟶ G) :
  presheaf_to_Type.map f = f.app (op point) := by refl

lemma Fmap_of_point {F : Profinite.{u}ᵒᵖ ⥤ Type (u+1)} (x : F.obj (op point)) :
  F.map (punit.elim point).op x = x :=
begin
  have : punit.elim point.{u} = 𝟙 point.{u} := by {ext1, exact dec_trivial},
  have h : (punit.elim point).op = 𝟙 (op point) := by {rw this, refl},
  rw h,
  have h₁ : F.map (𝟙 (op point.{u})) = 𝟙 (F.obj (op point)) :=
    category_theory.functor.map_id F _,
  rw h₁,
  refl,
end

def can_map_from_presheaf_to_sheaf (X : Type (u+1)) :
  Type_to_constant_presheaf.obj X ⟶ CondensedSet_to_presheaf.obj (Type_to_Condensed.obj X) :=
grothendieck_topology.to_sheafify proetale_topology (Type_to_constant_presheaf.obj X)

def presheaf_Type_counit : presheaf_to_Type.{u} ⋙ Type_to_constant_presheaf.{u} ⟶
  𝟭 (Profinite.{u}ᵒᵖ ⥤ Type (u+1)) :=
{ app := λ F,
    { app := λ S, F.map (punit.elim S.unop).op,
      naturality' :=
      begin
        intros S T f,
        dsimp,
        simp only [← category_theory.functor.map_comp],
        exact rfl,
      end, } }

def presheaf_Type_adjunction : Type_to_constant_presheaf.{u} ⊣ presheaf_to_Type.{u} :=
mk_of_unit_counit
{ unit := (category_theory.functor.const_comp_evaluation_obj _ point).hom,
  counit := presheaf_Type_counit,
  left_triangle' := by refl,
  right_triangle' :=
  begin
    ext1, dsimp at *, ext1 F, dsimp at *, simp at *, ext1, dsimp at *,
    rw presheaf_to_Type_map _,
    unfold presheaf_Type_counit,
    dsimp,
    exact Fmap_of_point x,
  end,
}

def Condensed_Type_adjunction : Type_to_Condensed.{u} ⊣ Condensed_to_Type.{u} :=
comp presheaf_Type_adjunction CondensedSet_presheaf_adjunction

instance : is_iso presheaf_Type_adjunction.unit :=
is_iso.of_iso (category_theory.functor.const_comp_evaluation_obj _ point)

-- lemma sheafification_eq_presheaf_on_point (X : Type (u+1)) :
--   (Type_to_Condensed.obj X).val.obj (op point) = X :=
-- begin
--   sorry,
--   -- unfold Type_to_Condensed,
--   -- unfold Type_to_constant_presheaf,
--   -- unfold presheaf_to_CondensedSet,
--   -- dsimp,
--   -- unfold proetale_topology,
--   -- unfold proetale_pretopology,
--   -- dsimp,
-- end

-- instance unit_iso : is_iso Condensed_Type_adjunction.{u}.unit :=
-- begin
--   unfold Condensed_Type_adjunction,
--   unfold comp,
--   dsimp,
--   unfold presheaf_Type_adjunction,
--   unfold CondensedSet_presheaf_adjunction,
--   dsimp,
--   unfold sheafification_adjunction,
--   dsimp,
--   sorry,
-- end

-- instance : full Type_to_Condensed := L_full_of_unit_is_iso Condensed_Type_adjunction
-- instance : faithful Type_to_Condensed := L_faithful_of_unit_is_iso Condensed_Type_adjunction
