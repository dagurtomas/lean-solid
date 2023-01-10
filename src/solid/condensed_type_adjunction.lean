import condensed.top_comparison
import solid.discrete
import category_theory.adjunction.basic
import solid.top_comparison_ulift
import solid.Profinite_fibres

open category_theory
open category_theory.adjunction
open Profinite
open opposite

noncomputable theory

universes u v

def evaluate_at_point_equiv_of_condensed (Y : CondensedSet.{u}) :
  Y.val.obj (opposite.op point) ≃ Condensed_to_Type.obj Y := by refl

def evaluate_at_point_equiv_of_type (X : Type (u+1)) :
  (Type_to_Condensed.obj X).val.obj (opposite.op point) ≃ X :=
{ to_fun := λ f, f.down.to_fun ⟨punit.star⟩,
  inv_fun := λ x, ⟨⟨λ f, x⟩⟩,
  left_inv := by tidy,
  right_inv := by tidy, } .

def Condensed_Type_hom_equiv : core_hom_equiv Type_to_Condensed Condensed_to_Type :=
{ hom_equiv := λ X T,
  { to_fun := λ f, (evaluate_at_point_equiv_of_type X).inv_fun ≫ (f.val.app $ opposite.op point) ≫
      (evaluate_at_point_equiv_of_condensed T).to_fun,
    inv_fun := sorry,
    left_inv := sorry,
    right_inv := sorry, },
  hom_equiv_naturality_left_symm' := sorry,
  hom_equiv_naturality_right' := sorry, }

-- lemma comp_lemma {X : CondensedSet.{u}} {S T : Profinite.{u}} (g : T ⟶ S)
--   (f : (Type_to_Condensed.obj (Condensed_to_Type.obj X)).val.obj (op S)) :
--   (Type_to_Condensed.obj (Condensed_to_Type.obj X)).val.map g.op f =
--   (Profinite_ulift.map g) ≫ f.down :=
-- begin
--   unfold can_map_from_colim_of_homs_to_hom_from_limit,
--   cases x,
--   simp only [category_theory.limits.types.colimit.ι_desc_apply],
--   refl,
-- end

-- lemma can_eq_left_comp_with_proj {i : Iᵒᵖ}
--   (x : (S.op ⋙ yoneda.obj Y ⋙ ulift_functor).obj i) :
--   (limit.π S i.unop) ≫ x.down  =
--   (can_map_from_colim_of_homs_to_hom_from_limit Y S
--     (colimit.ι (S.op ⋙ yoneda.obj Y ⋙ ulift_functor) i x)).down :=
-- begin
--   unfold can_map_from_colim_of_homs_to_hom_from_limit,
--   cases x,
--   simp only [category_theory.limits.types.colimit.ι_desc_apply],
--   refl,
-- end

--set_option pp.universes true

-- variables {X : CondensedSet.{u}} {S T : Profinite.{u}ᵒᵖ} (g : S ⟶ T)
-- #check Type_to_Condensed.obj (Condensed_to_Type.obj X)
-- #check Condensed_to_Type.obj X
-- #check Profinite_ulift.op.obj S ⟶ Profinite_ulift.op.obj T
-- #check Profinite_ulift.op.map g
-- #check Top.discrete.obj (Condensed_to_Type.obj X)
-- #check (to_Top.op.obj (Profinite_ulift.op.obj S)).unop

-- lemma ulift_up_eq_id (X : Type (u+1)) : (ulift.up.{u+1 u+1} : X → ulift X) = λ x, ⟨x⟩ :=
-- begin
--   sorry,
-- end

-- lemma ulift_eq_id (X : Type (u+1)) : ulift.{u+1 u+1} X = X :=
-- begin
--   have : (ulift.{u+1 u+1} X) = ulift.up :: (down : X),
-- end

-- variables (α : Type u)
-- #check α
-- #check ulift.{u u} α

@[simp]
lemma condensed_type_x2_as_hom (X : CondensedSet.{u}) (S : Profinite.{u}ᵒᵖ) :
  (Type_to_Condensed.obj (Condensed_to_Type.obj X)).val.obj S =
  ulift_functor.{u+1 u+1}.obj (((to_Top.op.obj (Profinite_ulift.op.obj S)).unop) ⟶
  (Top.discrete.obj (Condensed_to_Type.obj X))) :=
by refl

@[simp]
lemma condensed_type_x2_as_hom_map {X : CondensedSet.{u}} {S T : Profinite.{u}ᵒᵖ} (g : S ⟶ T) :
  (Type_to_Condensed.obj (Condensed_to_Type.obj X)).val.map g =
  (ulift_functor.map (as_hom (λ f, (to_Top.op.map (Profinite_ulift.op.map g)).unop ≫ f))) :=
by refl

-- why the "ulift_functor.{u+1 u+1}"??? It shouldn't do anything?

-- eq_to_hom (condensed_type_x2_as_hom X S) ≫
--  ≫ (eq_to_hom (condensed_type_x2_as_hom X S).symm)

def map_for_counit {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) : X.val.obj S :=
begin
  let f' := f.down,
  let g := parts_of_map_as_Profinite f.down,
  have h := parts_of_map_cover_Profinite f.down,
  apply_fun op at h,
  simp at h,
  change (parts_of_map_as_Profinite f.down) with g at h,
  rw h,
  let i := (λ (t : X.val.obj (op (Profinite.sigma g))),
    ((λ a, X.val.map (Profinite.sigma.ι g a).op t) :
    Π (a : (set_range_as_type_u f.down)), X.val.obj (op (g a)))),
  have : function.bijective i := product_condition_general_finite X g,
  let e := equiv.of_bijective i this,
  equiv_rw e,
  intros a,
  let pmap : g a → point := (equiv.arrow_punit_equiv_punit (g a)).inv_fun punit.star,
  have hp : continuous pmap := continuous_const,
  let p : g a ⟶ point := ⟨pmap, hp⟩,
  apply X.val.map p.op,
  let x := ((set_range_as_type_u_equiv f.down).inv_fun ∘ ulift.down.{u 0}) a,
  let x' : Top.discrete.obj (Condensed_to_Type.obj X) := x,
  exact x',
end

def for_counit₁ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  set_range_as_type_u f.down → Profinite.{u} :=
  parts_of_map_as_Profinite f.down

lemma for_counit₂ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  S = op (sigma (for_counit₁ f)) :=
begin
  have h := parts_of_map_cover_Profinite f.down,
  apply_fun op at h,
  simp only [opposite.op_unop] at h,
  exact h,
end

def for_counit₂b {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  X.val.obj (op (sigma (for_counit₁ f))) → X.val.obj S := X.val.map (eq_to_hom (for_counit₂ f).symm)

def for_counit₃ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  X.val.obj (op (sigma (for_counit₁ f))) ≃
  Π (a : set_range_as_type_u f.down), X.val.obj (op ((for_counit₁ f) a)) :=
  equiv.of_bijective _ (product_condition_general_finite X (for_counit₁ f))

def for_counit₄ {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ}
  (f : ((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) :
  Π (a : set_range_as_type_u f.down), (for_counit₁ f) a ⟶ point :=
  λ a, ⟨(equiv.arrow_punit_equiv_punit ((for_counit₁ f) a)).inv_fun punit.star, continuous_const⟩

def map_for_counit' {X : CondensedSet.{u}} {S : Profinite.{u}ᵒᵖ} :
  (((Condensed_to_Type ⋙ Type_to_Condensed).obj X).val.obj S) → X.val.obj S :=
λ f, (for_counit₂b f) ((for_counit₃ f).inv_fun (λ a, X.val.map (for_counit₄ f a).op
    ((coe (((set_range_as_type_u_equiv f.down).inv_fun ∘ ulift.down.{u 0}) a)) :
    Top.discrete.obj (Condensed_to_Type.obj X))))

def Condensed_Type_adjunction : Type_to_Condensed.{u} ⊣ Condensed_to_Type.{u} :=
  mk_of_unit_counit
  { unit := { app := λ X, (λ x, ⟨⟨λ f, x⟩⟩), },
    counit := { app := λ X, { val := { app:= λ S, (as_hom map_for_counit'),
      naturality' := begin
        intros S T g,
        dsimp,
        simp only [condensed_type_x2_as_hom_map],
        ext f,
        simp only [Profinite.to_Top_map,
          quiver.hom.unop_op,
          category_theory.ulift_functor_map,
          category_theory.types_comp_apply,
          category_theory.functor.op_map],
        cases f,
        dsimp at *,

        -- unfold map_for_counit',
        -- unfold for_counit₂b,
        -- unfold for_counit₃,
        -- unfold for_counit₄,
        -- dsimp,
        sorry,
      end, },}, }, }
  -- mk_of_hom_equiv Condensed_Type_hom_equiv

instance glob_sec_preserves_limits :
  limits.preserves_limits (CondensedSet.evaluation point) := by apply_instance

instance : limits.preserves_limits Condensed_to_Type := glob_sec_preserves_limits

def is_discrete (X: CondensedSet.{u}) : Prop :=
  ∃ (Y : Type (u+1)) (h : (Type_to_Condensed.obj Y) ⟶ X), is_iso h

def is_discrete_stronger (X : CondensedSet.{u}) : Prop :=
  is_iso ((counit Condensed_Type_adjunction).app X)
