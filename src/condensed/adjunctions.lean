import condensed.ab
import for_mathlib.SheafOfTypes_sheafification
import for_mathlib.sheafify_forget
import for_mathlib.whisker_adjunction
import algebra.category.Group.adjunctions

open category_theory

namespace Condensed

noncomputable theory

section Type_to_presheaf

def Type_to_presheaf : CondensedSet ⥤ Profiniteᵒᵖ ⥤ Type* :=
SheafOfTypes_to_presheaf _

def presheaf_to_Type : (Profiniteᵒᵖ ⥤ Type*) ⥤ CondensedSet :=
presheaf_to_SheafOfTypes _

def Type_to_presheaf_adjunction : presheaf_to_Type ⊣ Type_to_presheaf :=
sheafification_adjunction_types _

def to_presheaf_to_Type (S : Profiniteᵒᵖ ⥤ Type*) :
  S ⟶ Type_to_presheaf.obj (presheaf_to_Type.obj S) :=
Type_to_presheaf_adjunction.unit.app S

def from_Type_to_presheaf (S : CondensedSet) :
  presheaf_to_Type.obj (Type_to_presheaf.obj S) ⟶ S :=
Type_to_presheaf_adjunction.counit.app S

instance is_iso_from_Type_to_presheaf (S : CondensedSet) :
  is_iso (from_Type_to_presheaf S) :=
category_theory.is_iso_sheafification_types_adjunction_counit_app _ _

-- TODO: Generalize to arbitrary reflective adjunctions.
lemma Type_to_presheaf_map_from_Type_to_presheaf (S : CondensedSet) :
  Type_to_presheaf.map (inv (from_Type_to_presheaf S)) = to_presheaf_to_Type _ :=
begin
  dsimp only [to_presheaf_to_Type],
  have := Type_to_presheaf_adjunction.right_triangle,
  apply_fun (λ e, e.app S) at this,
  dsimp at this,
  erw [functor.map_inv, ← category.id_comp (inv _), is_iso.comp_inv_eq, this],
end

instance is_iso_to_presheaf_to_Type (S : CondensedSet) :
  is_iso (to_presheaf_to_Type (Type_to_presheaf.obj S)) :=
by { rw ← Type_to_presheaf_map_from_Type_to_presheaf, apply_instance }

def Type_presheaf_lift {S : Profiniteᵒᵖ ⥤ Type*} {T : CondensedSet}
  (η : S ⟶ Type_to_presheaf.obj T) : presheaf_to_Type.obj S ⟶ T :=
(Type_to_presheaf_adjunction.hom_equiv _ _).symm η

@[simp]
lemma to_presheaf_to_Type_Type_presheaf_lift {S : Profiniteᵒᵖ ⥤ Type*}
  {T : CondensedSet} (η : S ⟶ Type_to_presheaf.obj T) :
  to_presheaf_to_Type S ≫ Type_to_presheaf.map (Type_presheaf_lift η) = η :=
begin
  dsimp only [to_presheaf_to_Type, Type_presheaf_lift],
  rw Type_to_presheaf_adjunction.hom_equiv_counit,
  simp only [adjunction.unit_naturality_assoc, adjunction.right_triangle_components,
    category.comp_id, functor.map_comp],
end

lemma Type_presheaf_lift_unique {S : Profiniteᵒᵖ ⥤ Type*}
  {T : CondensedSet} (η : S ⟶ Type_to_presheaf.obj T)
  (g : presheaf_to_Type.obj S ⟶ T) (h : to_presheaf_to_Type S ≫ Type_to_presheaf.map g = η) :
  g = Type_presheaf_lift η :=
begin
  apply_fun (Type_to_presheaf_adjunction.hom_equiv _ _),
  simp only [Type_to_presheaf_adjunction.hom_equiv_unit],
  erw [h, to_presheaf_to_Type_Type_presheaf_lift],
end

lemma Type_presheaf_hom_ext {S : Profiniteᵒᵖ ⥤ Type*}
  {T : CondensedSet} (f g : presheaf_to_Type.obj S ⟶ T)
  (h : to_presheaf_to_Type S ≫ Type_to_presheaf.map f =
    to_presheaf_to_Type S ≫ Type_to_presheaf.map g) : f = g :=
by rw [Type_presheaf_lift_unique _ f rfl, Type_presheaf_lift_unique _ g rfl, h]

lemma to_presheaf_to_Type_map {S T : Profiniteᵒᵖ ⥤ Type*} (η : S ⟶ T) :
  to_presheaf_to_Type S ≫ Type_to_presheaf.map (presheaf_to_Type.map η) =
  η ≫ to_presheaf_to_Type T :=
begin
  dsimp only [to_presheaf_to_Type],
  simp,
end

lemma map_Type_presheaf_lift {S T : Profiniteᵒᵖ ⥤ Type*} {W : CondensedSet} (η : S ⟶ T)
  (γ : T ⟶ Type_to_presheaf.obj W) :
  presheaf_to_Type.map η ≫ Type_presheaf_lift γ = Type_presheaf_lift (η ≫ γ) :=
begin
  apply Type_presheaf_lift_unique,
  rw [functor.map_comp, ← category.assoc, to_presheaf_to_Type_map,
    category.assoc, to_presheaf_to_Type_Type_presheaf_lift],
end

lemma from_Type_to_presheaf_inv_lift {S T : CondensedSet} (η : S ⟶ T) :
  inv (from_Type_to_presheaf S) ≫ Type_presheaf_lift (Type_to_presheaf.map η) = η :=
begin
  rw is_iso.inv_comp_eq,
  dsimp [Type_presheaf_lift, from_Type_to_presheaf],
  simp,
end

end Type_to_presheaf

section Ab_to_presheaf

def Ab_to_presheaf : Condensed Ab ⥤ Profiniteᵒᵖ ⥤ Ab :=
Sheaf_to_presheaf _ _

def presheaf_to_Ab : (Profiniteᵒᵖ ⥤ Ab) ⥤ Condensed Ab :=
presheaf_to_Sheaf _ _

def Ab_to_presheaf_adjunction : presheaf_to_Ab ⊣ Ab_to_presheaf :=
sheafification_adjunction _ _

def to_presheaf_to_Ab (S : Profiniteᵒᵖ ⥤ Ab) : S ⟶ Ab_to_presheaf.obj (presheaf_to_Ab.obj S) :=
Ab_to_presheaf_adjunction.unit.app _

def from_Ab_to_presheaf (S : Condensed Ab) : presheaf_to_Ab.obj (Ab_to_presheaf.obj S) ⟶ S :=
Ab_to_presheaf_adjunction.counit.app _

instance is_iso_from_Ab_to_presheaf (S : Condensed Ab) : is_iso (from_Ab_to_presheaf S) :=
category_theory.is_iso_sheafification_adjunction_counit _

lemma Ab_to_presheaf_map_from_Ab_to_presheaf (S : Condensed Ab) :
  Ab_to_presheaf.map (inv (from_Ab_to_presheaf S)) = to_presheaf_to_Ab _ :=
begin
  dsimp only [to_presheaf_to_Ab],
  have := Ab_to_presheaf_adjunction.right_triangle,
  apply_fun (λ e, e.app S) at this,
  dsimp at this,
  erw [functor.map_inv, ← category.id_comp (inv _), is_iso.comp_inv_eq, this],
end

instance is_iso_to_presheaf_to_Ab (S : Condensed Ab) :
  is_iso (to_presheaf_to_Ab (Ab_to_presheaf.obj S)) :=
by { rw ← Ab_to_presheaf_map_from_Ab_to_presheaf, apply_instance }

def Ab_presheaf_lift {S : Profiniteᵒᵖ ⥤ Ab} {T : Condensed Ab}
  (η : S ⟶ Ab_to_presheaf.obj T) : presheaf_to_Ab.obj S ⟶ T :=
(Ab_to_presheaf_adjunction.hom_equiv _ _).symm η

@[simp]
lemma to_presheaf_to_Ab_Ab_presheaf_lift {S : Profiniteᵒᵖ ⥤ Ab}
  {T : Condensed Ab} (η : S ⟶ Ab_to_presheaf.obj T) :
  to_presheaf_to_Ab S ≫ Ab_to_presheaf.map (Ab_presheaf_lift η) = η :=
begin
  dsimp only [to_presheaf_to_Ab, Ab_presheaf_lift],
  rw Ab_to_presheaf_adjunction.hom_equiv_counit,
  simp only [adjunction.unit_naturality_assoc, adjunction.right_triangle_components,
    category.comp_id, functor.map_comp],
end

lemma Ab_presheaf_lift_unique {S : Profiniteᵒᵖ ⥤ Ab}
  {T : Condensed Ab} (η : S ⟶ Ab_to_presheaf.obj T)
  (g : presheaf_to_Ab.obj S ⟶ T) (h : to_presheaf_to_Ab S ≫ Ab_to_presheaf.map g = η) :
  g = Ab_presheaf_lift η :=
begin
  apply_fun (Ab_to_presheaf_adjunction.hom_equiv _ _),
  simp only [Ab_to_presheaf_adjunction.hom_equiv_unit],
  erw [h, to_presheaf_to_Ab_Ab_presheaf_lift],
end

lemma Ab_presheaf_hom_ext {S : Profiniteᵒᵖ ⥤ Ab}
  {T : Condensed Ab} (f g : presheaf_to_Ab.obj S ⟶ T)
  (h : to_presheaf_to_Ab S ≫ Ab_to_presheaf.map f =
    to_presheaf_to_Ab S ≫ Ab_to_presheaf.map g) : f = g :=
by rw [Ab_presheaf_lift_unique _ f rfl, Ab_presheaf_lift_unique _ g rfl, h]

lemma to_presheaf_to_Ab_map {S T : Profiniteᵒᵖ ⥤ Ab} (η : S ⟶ T) :
  to_presheaf_to_Ab S ≫ Ab_to_presheaf.map (presheaf_to_Ab.map η) =
  η ≫ to_presheaf_to_Ab T :=
begin
  dsimp [to_presheaf_to_Ab],
  simp,
end

lemma to_presheaf_to_Ab_map_lift {S : Profiniteᵒᵖ ⥤ Ab} {T : Condensed Ab}
  (η : S ⟶ Ab_to_presheaf.obj T) :
  to_presheaf_to_Ab S ≫ Ab_to_presheaf.map (Ab_presheaf_lift η) = η :=
begin
  dsimp [to_presheaf_to_Ab, Ab_presheaf_lift],
  simp,
end

end Ab_to_presheaf

section Ab_presheaf

def Ab_presheaf_to_presheaf : (Profiniteᵒᵖ ⥤ Ab) ⥤ Profiniteᵒᵖ ⥤ Type* :=
(whiskering_right _ _ _).obj $ forget Ab

def presheaf_to_Ab_presheaf : (Profiniteᵒᵖ ⥤ Type*) ⥤ Profiniteᵒᵖ ⥤ Ab :=
(whiskering_right _ _ _).obj $ AddCommGroup.free

def Ab_presheaf_to_presheaf_adjunction : presheaf_to_Ab_presheaf ⊣ Ab_presheaf_to_presheaf :=
AddCommGroup.adj.whiskering_right _

def to_presheaf_to_Ab_presheaf (S : Profiniteᵒᵖ ⥤ Type*) :
  S ⟶ Ab_presheaf_to_presheaf.obj (presheaf_to_Ab_presheaf.obj S) :=
Ab_presheaf_to_presheaf_adjunction.unit.app _

def from_Ab_presheaf_to_presheaf (S : Profiniteᵒᵖ ⥤ Ab) :
  presheaf_to_Ab_presheaf.obj (Ab_presheaf_to_presheaf.obj S) ⟶ S :=
Ab_presheaf_to_presheaf_adjunction.counit.app _

def Ab_presheaf_presheaf_lift {S : Profiniteᵒᵖ ⥤ Type*} {T : Profiniteᵒᵖ ⥤ Ab}
  (η : S ⟶ Ab_presheaf_to_presheaf.obj T) : presheaf_to_Ab_presheaf.obj S ⟶ T :=
(Ab_presheaf_to_presheaf_adjunction.hom_equiv _ _).symm η

@[simp]
lemma to_presheaf_to_Ab_presheaf_Ab_presheaf_presheaf_lift
  {S : Profiniteᵒᵖ ⥤ Type*} {T : Profiniteᵒᵖ ⥤ Ab}
  (η : S ⟶ Ab_presheaf_to_presheaf.obj T) :
  to_presheaf_to_Ab_presheaf S ≫ Ab_presheaf_to_presheaf.map (Ab_presheaf_presheaf_lift η) = η :=
begin
  dsimp only [to_presheaf_to_Ab_presheaf, Ab_presheaf_presheaf_lift],
  rw Ab_presheaf_to_presheaf_adjunction.hom_equiv_counit,
  simp only [adjunction.unit_naturality_assoc, adjunction.right_triangle_components,
  category.comp_id, functor.map_comp],
end

lemma Ab_presheaf_presheaf_lift_unique {S : Profiniteᵒᵖ ⥤ Type*} {T : Profiniteᵒᵖ ⥤ Ab}
  (η : S ⟶ Ab_presheaf_to_presheaf.obj T) (g : presheaf_to_Ab_presheaf.obj S ⟶ T)
  (h : to_presheaf_to_Ab_presheaf S ≫ Ab_presheaf_to_presheaf.map g = η) :
  g = Ab_presheaf_presheaf_lift η :=
begin
  apply_fun (Ab_presheaf_to_presheaf_adjunction.hom_equiv _ _),
  simp only [Ab_presheaf_to_presheaf_adjunction.hom_equiv_unit],
  erw [h, to_presheaf_to_Ab_presheaf_Ab_presheaf_presheaf_lift],
end

lemma Ab_presheaf_presheaf_hom_ext {S : Profiniteᵒᵖ ⥤ Type*} {T : Profiniteᵒᵖ ⥤ Ab}
  (f g : presheaf_to_Ab_presheaf.obj S ⟶ T)
  (h : to_presheaf_to_Ab_presheaf S ≫ Ab_presheaf_to_presheaf.map f =
    to_presheaf_to_Ab_presheaf S ≫ Ab_presheaf_to_presheaf.map g) : f = g :=
by rw [Ab_presheaf_presheaf_lift_unique _ f rfl, Ab_presheaf_presheaf_lift_unique _ g rfl, h]

lemma to_presheaf_to_Ab_presheaf_map {S T : Profiniteᵒᵖ ⥤ Type*} (η : S ⟶ T) :
  to_presheaf_to_Ab_presheaf S ≫ (Ab_presheaf_to_presheaf.map (presheaf_to_Ab_presheaf.map η)) =
  η ≫ to_presheaf_to_Ab_presheaf T :=
begin
  dsimp [to_presheaf_to_Ab_presheaf],
  simp,
end

end Ab_presheaf

section Ab_to_Type

def Ab_to_Type : Condensed Ab ⥤ CondensedSet :=
{ obj := λ S, ⟨Ab_to_presheaf.obj S ⋙ forget _, begin
    rw [← is_sheaf_iff_is_sheaf_of_type, ← presheaf.is_sheaf_iff_is_sheaf_forget],
    exact S.2
  end⟩,
  map := λ A B f, whisker_right (Ab_to_presheaf.map f) _,
  map_id' := λ A, whisker_right_id _,
  map_comp' := λ A B C f g, whisker_right_comp _ _ _ }

/-
def Ab_to_Type' : Condensed Ab ⥤ CondensedSet :=
Ab_to_presheaf ⋙ Ab_presheaf_to_presheaf ⋙ presheaf_to_Type

def Ab_to_Type_iso : Ab_to_Type ≅ Ab_to_Type' := sorry
-/

def Type_to_Ab : CondensedSet ⥤ Condensed Ab :=
Type_to_presheaf ⋙ presheaf_to_Ab_presheaf ⋙ presheaf_to_Ab

def Ab_Type_lift {S : CondensedSet} {T : Condensed Ab} (η : S ⟶ Ab_to_Type.obj T) :
  Type_to_Ab.obj S ⟶ T :=
Ab_presheaf_lift $ Ab_presheaf_presheaf_lift $ Type_to_presheaf.map η

def presheaf_to_Type_forget_iso (S : Profiniteᵒᵖ ⥤ Ab) :
   presheaf_to_Type.obj (S ⋙ forget _) ≅ Ab_to_Type.obj (presheaf_to_Ab.obj S) :=
{ hom := (sheafify_forget proetale_topology S).hom,
  inv := (sheafify_forget proetale_topology S).inv,
  hom_inv_id' := (sheafify_forget proetale_topology S).hom_inv_id,
  inv_hom_id' := (sheafify_forget proetale_topology S).inv_hom_id, }

lemma presheaf_to_Type_forget_iso_hom' (S : Profiniteᵒᵖ ⥤ Ab) :
  (presheaf_to_Type_forget_iso S).hom = proetale_topology.sheafify_lift
    (whisker_right (to_presheaf_to_Ab _) _)
begin
  erw ← presheaf.is_sheaf_iff_is_sheaf_forget,
  exact (presheaf_to_Ab.obj S).2
end := sheafify_forget_hom _ _

lemma presheaf_to_Type_forget_iso_hom (S : Profiniteᵒᵖ ⥤ Ab) :
  (presheaf_to_Type_forget_iso S).hom =
  Type_presheaf_lift (whisker_right (to_presheaf_to_Ab _) _) :=
presheaf_to_Type_forget_iso_hom' _

def to_Type_to_Ab (S : CondensedSet) : S ⟶ Ab_to_Type.obj (Type_to_Ab.obj S) :=
inv (from_Type_to_presheaf S) ≫ presheaf_to_Type.map (to_presheaf_to_Ab_presheaf _) ≫
(presheaf_to_Type_forget_iso _).hom

lemma to_Type_to_Ab_Ab_Type_lift {S : CondensedSet} {T : Condensed Ab} (η : S ⟶ Ab_to_Type.obj T) :
  to_Type_to_Ab S ≫ (Ab_to_Type.map (Ab_Type_lift η)) = η :=
begin
  dsimp only [to_Type_to_Ab],
  rw [category.assoc, presheaf_to_Type_forget_iso_hom],
  rw map_Type_presheaf_lift,
  erw [← category.assoc, from_Type_to_presheaf_inv_lift],
  dsimp [Ab_Type_lift, Ab_to_Type],
  apply_fun (λ e, Type_to_presheaf.map e),
  swap, { exact function.injective_id },
  ext : 2,
  dsimp,
  erw nat_trans.comp_app,
  erw nat_trans.comp_app,
  dsimp only [whisker_right_app],
  rw [category.assoc, ← (forget Ab).map_comp, ← nat_trans.comp_app, to_presheaf_to_Ab_map_lift],
  rw [← whisker_right_app, ← nat_trans.comp_app],
  congr' 1,
  erw to_presheaf_to_Ab_presheaf_Ab_presheaf_presheaf_lift,
end

lemma Ab_Type_lift_unique {S : CondensedSet} {T : Condensed Ab} (η : S ⟶ Ab_to_Type.obj T)
  (g : Type_to_Ab.obj S ⟶ T) (h : to_Type_to_Ab S ≫ (Ab_to_Type.map g) = η) :
  g = Ab_Type_lift η := sorry

lemma Ab_Type_hom_ext {S : CondensedSet} {T : Condensed Ab}
  (f g : Type_to_Ab.obj S ⟶ T)
  (h : to_Type_to_Ab S ≫ (Ab_to_Type.map f) = to_Type_to_Ab S ≫ (Ab_to_Type.map g)) :
  f = g :=
by rw [Ab_Type_lift_unique _ f rfl, Ab_Type_lift_unique _ g rfl, h]

/-
def Ab_to_Type : Condensed Ab ⥤ CondensedSet :=
{ obj := λ S, ⟨Ab_to_presheaf.obj S ⋙ forget _, begin
    rw [← is_sheaf_iff_is_sheaf_of_type, ← presheaf.is_sheaf_iff_is_sheaf_forget],
    exact S.2
  end⟩,
  map := λ A B f, whisker_right (Ab_to_presheaf.map f) _,
  map_id' := λ A, whisker_right_id _,
  map_comp' := λ A B C f g, whisker_right_comp _ _ _ }

def Type_to_Ab : CondensedSet ⥤ Condensed Ab :=
{ obj := λ S, presheaf_to_Ab.obj $ Type_to_presheaf.obj S ⋙ AddCommGroup.free,
  map := λ S T f, presheaf_to_Ab.map $ whisker_right (Type_to_presheaf.map f) _,
  map_id' := λ S, by erw [Type_to_presheaf.map_id, whisker_right_id, presheaf_to_Ab.map_id],
  map_comp' := λ S T W f g,
    by rw [Type_to_presheaf.map_comp, whisker_right_comp, presheaf_to_Ab.map_comp] }

def presheaf_to_Type_forget_iso (S : Profiniteᵒᵖ ⥤ Ab) :
   presheaf_to_Type.obj (S ⋙ forget _) ≅ Ab_to_Type.obj (presheaf_to_Ab.obj S) :=
{ hom := (sheafify_forget proetale_topology S).hom,
  inv := (sheafify_forget proetale_topology S).inv,
  hom_inv_id' := (sheafify_forget proetale_topology S).hom_inv_id,
  inv_hom_id' := (sheafify_forget proetale_topology S).inv_hom_id, }

lemma presheaf_to_Type_forget_iso_hom' (S : Profiniteᵒᵖ ⥤ Ab) :
  (presheaf_to_Type_forget_iso S).hom = proetale_topology.sheafify_lift
    (whisker_right (to_presheaf_to_Ab _) _)
begin
  erw ← presheaf.is_sheaf_iff_is_sheaf_forget,
  exact (presheaf_to_Ab.obj S).2
end := sheafify_forget_hom _ _

lemma presheaf_to_Type_forget_iso_hom (S : Profiniteᵒᵖ ⥤ Ab) :
  (presheaf_to_Type_forget_iso S).hom =
  Type_presheaf_lift (whisker_right (to_presheaf_to_Ab _) _) :=
presheaf_to_Type_forget_iso_hom' _

def Ab_Type_lift {S : CondensedSet} {T : Condensed Ab} (η : S ⟶ Ab_to_Type.obj T) :
  Type_to_Ab.obj S ⟶ T :=
proetale_topology.sheafify_lift (Ab_presheaf_presheaf_lift (Type_to_presheaf.map η)) T.2

def to_Type_to_Ab (S : CondensedSet) : S ⟶ Ab_to_Type.obj (Type_to_Ab.obj S) :=
inv (from_Type_to_presheaf S) ≫ presheaf_to_Type.map (to_presheaf_to_Ab_presheaf _) ≫
(presheaf_to_Type_forget_iso _).hom

lemma to_Type_to_Ab_Ab_Type_lift {S : CondensedSet} {T : Condensed Ab} (η : S ⟶ Ab_to_Type.obj T) :
  to_Type_to_Ab S ≫ (Ab_to_Type.map (Ab_Type_lift η)) = η :=
begin
  dsimp only [to_Type_to_Ab],
  rw [category.assoc, presheaf_to_Type_forget_iso_hom],
  rw map_Type_presheaf_lift,
  erw [← category.assoc, from_Type_to_presheaf_inv_lift],
  dsimp [Ab_Type_lift],


  apply Type_presheaf_hom_ext,
  erw ← category.assoc,

  --erw to_presheaf_to_Type_map,
end

def Ab_to_Type_adjunction : Type_to_Ab ⊣ Ab_to_Type :=
sorry

-/
end Ab_to_Type

end Condensed
