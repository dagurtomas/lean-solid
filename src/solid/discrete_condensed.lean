import condensed.top_comparison
import condensed.adjunctions

noncomputable theory

universe u

open category_theory
open category_theory.adjunction
open opposite
open Profinite

/- TODO: Unify this for condensed objects in a general category to avoid all this repetition... -/

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
      end, },
  naturality' :=
  begin
    intros S T f,
    ext1,
    ext1,
    dsimp,
    simp only [category_theory.nat_trans.naturality],
    refl,
  end, }
-- was way too slow before but still worked without explicit naturality proof

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
is_iso.of_iso (category_theory.functor.const_comp_evaluation_obj _ point) .

def Ab_to_constant_presheaf : Ab.{u+1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u+1} :=
category_theory.functor.const _

def Ab_to_Condensed : Ab.{u+1} ⥤ Condensed.{u} Ab.{u+1} :=
Ab_to_constant_presheaf ⋙ presheaf_to_Condensed_Ab

def presheaf_to_Ab : (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) ⥤ Ab.{u+1} :=
(evaluation _ _).obj $ op point

def Condensed_to_Ab : Condensed.{u} Ab.{u+1} ⥤ Ab.{u+1} :=
Condensed_Ab_to_presheaf ⋙ presheaf_to_Ab

lemma Condensed_to_Ab_eq_Condensed_evaluation_at_point :
  Condensed_to_Ab = Condensed.evaluation Ab.{u+1} point := by refl

lemma presheaf_to_Ab_comp_Ab_to_constant_presheaf_eq_id (α : Ab.{u+1}) :
  presheaf_to_Ab.obj (Ab_to_constant_presheaf.obj α) = α := by refl

lemma presheaf_to_Ab_map {F G : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}} (f : F ⟶ G) :
  presheaf_to_Ab.map f = f.app (op point) := by refl

lemma Fmap_of_point_Ab {F : Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}} (x : F.obj (op point)) :
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

def can_map_from_presheaf_to_sheaf_Ab (X : Ab.{u+1}) :
  Ab_to_constant_presheaf.obj X ⟶ Condensed_Ab_to_presheaf.obj (Ab_to_Condensed.obj X) :=
grothendieck_topology.to_sheafify proetale_topology (Ab_to_constant_presheaf.obj X)

def presheaf_Ab_counit : presheaf_to_Ab.{u} ⋙ Ab_to_constant_presheaf.{u} ⟶
  𝟭 (Profinite.{u}ᵒᵖ ⥤ Ab.{u+1}) :=
{ app := λ F,
    { app := λ S, F.map (punit.elim S.unop).op,
      naturality' :=
      begin
        intros S T f,
        dsimp,
        simp only [← category_theory.functor.map_comp],
        dsimp [Ab_to_constant_presheaf],
        simp only [category.id_comp],
        congr,
      end, },
  naturality' :=
  begin
    intros S T f,
    ext1,
    ext1,
    dsimp,
    simp only [nat_trans.naturality],
    refl,
  end, }

def presheaf_Ab_adjunction : Ab_to_constant_presheaf.{u} ⊣ presheaf_to_Ab.{u} :=
mk_of_unit_counit
{ unit := (category_theory.functor.const_comp_evaluation_obj _ point).hom,
  counit := presheaf_Ab_counit,
  left_triangle' := by refl,
  right_triangle' :=
  begin
    ext1, dsimp at *, ext1 F, dsimp at *, simp at *, ext1,
    rw presheaf_to_Ab_map _,
    unfold presheaf_Ab_counit,
    dsimp,
    exact Fmap_of_point_Ab x,
  end,
}

def Condensed_Ab_adjunction : Ab_to_Condensed.{u} ⊣ Condensed_to_Ab.{u} :=
comp presheaf_Ab_adjunction Condensed_Ab_presheaf_adjunction

instance Ab_unit_is_iso : is_iso presheaf_Ab_adjunction.unit :=
is_iso.of_iso (category_theory.functor.const_comp_evaluation_obj _ point) .

variables (A : Type (u+1)) [ring A]
variables [∀ (X : Profinite.{u}), limits.preserves_colimits_of_shape
  (proetale_topology.cover X)ᵒᵖ (forget (Module.{u+1} A))]

def Mod_to_constant_presheaf : (Module.{u+1} A) ⥤ Profinite.{u}ᵒᵖ ⥤ (Module.{u+1} A) :=
category_theory.functor.const _

def presheaf_to_Condensed_Mod : (Profinite.{u}ᵒᵖ ⥤ Module.{u+1} A) ⥤
  Condensed.{u} (Module.{u+1} A) :=
presheaf_to_Sheaf _ _

def Mod_to_Condensed : (Module.{u+1} A) ⥤ Condensed.{u} (Module.{u+1} A) :=
Mod_to_constant_presheaf A ⋙ presheaf_to_Condensed_Mod A

def presheaf_to_Mod : (Profinite.{u}ᵒᵖ ⥤ (Module.{u+1} A)) ⥤ (Module.{u+1} A) :=
(evaluation _ _).obj $ op point

def Condensed_Mod_to_presheaf : Condensed.{u} (Module.{u+1} A) ⥤
  (Profinite.{u}ᵒᵖ ⥤ Module.{u+1} A) :=
Sheaf_to_presheaf _ _

def Condensed_Mod_presheaf_adjunction : presheaf_to_Condensed_Mod A ⊣ Condensed_Mod_to_presheaf A :=
sheafification_adjunction _ _

def Condensed_to_Mod : Condensed.{u} (Module.{u+1} A) ⥤ (Module.{u+1} A) :=
Condensed_Mod_to_presheaf A ⋙ presheaf_to_Mod A

lemma Condensed_to_Mod_eq_Condensed_evaluation_at_point :
  Condensed_to_Mod A = Condensed.evaluation (Module.{u+1} A) point := by refl

lemma presheaf_to_Mod_comp_Mod_to_constant_presheaf_eq_id (α : (Module.{u+1} A)) :
  (presheaf_to_Mod A).obj ((Mod_to_constant_presheaf A).obj α) = α := by refl

lemma presheaf_to_Mod_map {F G : Profinite.{u}ᵒᵖ ⥤ (Module.{u+1} A)} (f : F ⟶ G) :
  (presheaf_to_Mod A).map f = f.app (op point) := by refl

lemma Fmap_of_point_Mod {F : Profinite.{u}ᵒᵖ ⥤ (Module.{u+1} A)} (x : F.obj (op point)) :
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

def can_map_from_presheaf_to_sheaf_Mod (X : (Module.{u+1} A)) :
  (Mod_to_constant_presheaf A).obj X ⟶ (Condensed_Mod_to_presheaf A).obj
  ((Mod_to_Condensed A).obj X) :=
grothendieck_topology.to_sheafify proetale_topology ((Mod_to_constant_presheaf A).obj X)

def presheaf_Mod_counit : presheaf_to_Mod.{u} A ⋙ Mod_to_constant_presheaf.{u} A ⟶
  𝟭 (Profinite.{u}ᵒᵖ ⥤ (Module.{u+1} A)) :=
{ app := λ F,
    { app := λ S, F.map (punit.elim S.unop).op,
      naturality' :=
      begin
        intros S T f,
        dsimp,
        simp only [← category_theory.functor.map_comp],
        dsimp [Mod_to_constant_presheaf],
        simp only [category.id_comp],
        congr,
      end, },
  naturality' :=
  begin
    intros S T f,
    ext1,
    ext1,
    dsimp,
    simp only [nat_trans.naturality],
    refl,
  end, }

def presheaf_Mod_adjunction : Mod_to_constant_presheaf.{u} A ⊣ presheaf_to_Mod.{u} A :=
mk_of_unit_counit
{ unit := (category_theory.functor.const_comp_evaluation_obj _ point).hom,
  counit := presheaf_Mod_counit A,
  left_triangle' := by refl,
  right_triangle' :=
  begin
    ext1, dsimp at *, ext1 F, dsimp at *, simp at *, ext1,
    rw presheaf_to_Mod_map _,
    unfold presheaf_Mod_counit,
    dsimp,
    exact Fmap_of_point_Mod A x,
  end,
}

def Condensed_Mod_adjunction : Mod_to_Condensed.{u} A ⊣ Condensed_to_Mod.{u} A :=
comp (presheaf_Mod_adjunction A) (Condensed_Mod_presheaf_adjunction A)

instance Mod_unit_is_iso : is_iso (presheaf_Mod_adjunction A).unit :=
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
