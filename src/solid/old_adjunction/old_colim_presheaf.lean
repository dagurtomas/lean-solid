import solid.colim_hom_injective
import topology.category.Profinite.as_limit
import category_theory.limits.kan_extension
--import category_theory.natural_isomorphism

noncomputable theory

universes v u

open category_theory
open category_theory.limits
open Profinite
open opposite

def functor_for_colim_presheaf (S : Profinite.{u}) (X : Type (u+1)) :
  (discrete_quotient S)ᵒᵖ ⥤ Type (u+1) :=
S.fintype_diagram.op ⋙ (Fintype.incl ⋙ ulift_functor.{u+1}).op ⋙ (yoneda.obj X)

set_option pp.universes true

instance has_colimits_of_shape_discrete_quotient (S : Profinite.{u}) :
  has_colimits_of_shape.{u u u+1 u+2} (discrete_quotient S)ᵒᵖ
  (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u+1} (Type (u+1)) := by apply_instance,
  haveI : has_colimits_of_size.{u u} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (discrete_quotient S)ᵒᵖ,
end



def colim_presheaf_cocone (S : Profinite.{u}) (X : Type (u+1)) :
  colimit_cocone $ functor_for_colim_presheaf S X :=
get_colimit_cocone _

def discrete_quotient_functor {S T : Profinite.{u}} (f : T ⟶ S) :
  discrete_quotient S ⥤ discrete_quotient T :=
{ obj := λ Si, Si.comap f.continuous_to_fun,
  map := λ Si Sj φ, ⟨⟨discrete_quotient.comap_mono _ φ.le⟩⟩ }

-- lemma comap_category_id {S : Profinite.{u}} (Si : discrete_quotient S) :
--   Si.comap ((𝟙 S).continuous_to_fun)

-- lemma discrete_quotient_functor_id (S : Profinite.{u}) :
--   discrete_quotient_functor (𝟙 S) ≅ 𝟭 (discrete_quotient S) :=
-- { hom := { app := λ Si, 𝟙 Si, },
--   inv := { app := λ Si, 𝟙 Si, } }

lemma discrete_quotient_functor_id (S : Profinite.{u}) :
  discrete_quotient_functor (𝟙 S) = 𝟭 (discrete_quotient S) :=
begin
  apply category_theory.functor.ext,
  { intros Si Sj φ, refl },
  { intros Si, ext, tauto },
end

theorem discrete_quotient_functor_id_op (S : Profinite.{u}) :
  (discrete_quotient_functor (𝟙 S)).op = 𝟭 (discrete_quotient S)ᵒᵖ :=
begin
  rw discrete_quotient_functor_id S,
  refl,
end

lemma discrete_quotient_functor_comp {S T U : Profinite.{u}} (f : T ⟶ S) (g : U ⟶ T) :
  discrete_quotient_functor (g ≫ f) =
  (discrete_quotient_functor f) ⋙ (discrete_quotient_functor g) :=
begin
  apply category_theory.functor.ext,
  { intros Si Sj φ, exact rfl, },
  { intros Si, ext, tauto },
end

def discrete_quotient_to_Cat_functor : Profinite.{u}ᵒᵖ ⥤ Cat :=
{ obj := λ S, Cat.of (discrete_quotient S.unop),
  map := λ S T f, discrete_quotient_functor f.unop,
  map_id' :=
  begin
    intros S,
    exact discrete_quotient_functor_id S.unop,
  end,
  map_comp' :=
  begin
    intros S T U f g,
    exact discrete_quotient_functor_comp _ _,
  end, }

def Cat_to_functor_Cat : Catᵒᵖ ⥤ Cat :=
{ obj := λ C, Cat.of (C.unopᵒᵖ ⥤ Type (u+1)),
  map := λ C D F,
  { obj := λ G, (functor.op (F.unop)) ⋙ G,
    map := λ G H f, whisker_left (functor.op F.unop) f, },
  map_id' :=
  begin
    intros C,
    dsimp,
    apply category_theory.functor.ext,
    { intros F G f,
      simp only [category_theory.Cat.id_map],
      ext1,
      dsimp,
      ext1,
      dsimp,
      simp only [category_theory.category.comp_id,
        category_theory.eq_to_hom_refl,
        category_theory.eq_to_hom_app],
      refl, },
    intros F,
    dsimp,
    have : functor.op (𝟙 C.unop) = 𝟭 C.unopᵒᵖ := by refl,
    rw this,
    rw category_theory.functor.id_comp,
    refl,
  end,
  map_comp' := by obviously, }

def discrete_quotient_op_to_type_to_Cat_functor : Profinite.{u} ⥤ Cat :=
functor.right_op discrete_quotient_to_Cat_functor ⋙ Cat_to_functor_Cat

-- lemma value_of_Cat_functor (S : Profinite.{u}) :
--   discrete_quotient_op_to_type_to_Cat_functor.obj S =

def nat_map_of_general_functor {S T : Profinite.{u}} (f : T ⟶ S)
  (F : (discrete_quotient T)ᵒᵖ ⥤ Type (u+1)) :
  (discrete_quotient_functor f).op ⋙ F ⟶ F := sorry

def nat_map_for_colim_1 {S T : Profinite.{u}} (f : T ⟶ S) (X : Type (u+1)) :
  (discrete_quotient_functor f).op ⋙ (functor_for_colim_presheaf T X) ⟶
  (functor_for_colim_presheaf S X) :=
begin
  type_check (discrete_quotient_op_to_type_to_Cat_functor.map f).obj (functor_for_colim_presheaf T X),
  sorry,
end

def nat_map_for_colim' {S T : Profinite.{u}} (f : T ⟶ S) (X : Type (u+1)) :
  (discrete_quotient_op_to_type_to_Cat_functor.map f).obj (functor_for_colim_presheaf T X) ⟶
  functor_for_colim_presheaf S X := sorry

theorem functor_id_comp  {S : Profinite.{u}} (F : (discrete_quotient S)ᵒᵖ ⥤ Type (u+1)) :
  𝟭 (discrete_quotient S)ᵒᵖ ⋙ F = F := category_theory.functor.id_comp F

lemma colimit_pre_id (S : Profinite.{u}) (X : Type (u+1)) :
  colimit.pre (functor_for_colim_presheaf S X) (discrete_quotient_functor (𝟙 S)).op =
  𝟙 (colimit (functor_for_colim_presheaf S X)) :=
begin
  ext,
  simp only [category_theory.types_comp_apply,
    category_theory.limits.colimit.ι_pre,
    category_theory.types_id_apply],
  have h₂ : colimit.ι ((discrete_quotient_functor (𝟙 S)).op ⋙ functor_for_colim_presheaf S X) j x
    = colimit.ι (𝟭 (discrete_quotient S)ᵒᵖ ⋙ functor_for_colim_presheaf S X) j x,
  { dsimp at *, fsplit, },
  rw h₂,
  rw functor.congr_obj (discrete_quotient_functor_id_op.{u} S) _,
  refl,
  -- have h₁ : colimit.ι (functor_for_colim_presheaf S X)
  --   ((discrete_quotient_functor (𝟙 S)).op.obj j) x = colimit.ι (functor_for_colim_presheaf S X)
  --   ((𝟭 (discrete_quotient S)ᵒᵖ).obj j) x,
  -- { have : (discrete_quotient_functor (𝟙 S)).obj (opposite.unop j) = opposite.unop j := by
  --   { rw discrete_quotient_functor_id,
  --     simp only [category_theory.functor.id_obj, opposite.unop_inj_iff, eq_self_iff_true], },
  --   have h : opposite.op ((discrete_quotient_functor (𝟙 S)).obj (opposite.unop j))
  --     = j := by { rw this, simp only [opposite.op_unop, eq_self_iff_true], },
  --   -- type of x is the problem, rw it with eq_to_hom
  --   let x' := (whisker_right (eq_to_hom (discrete_quotient_functor_id_op.{u} S))
  --     (functor_for_colim_presheaf S X)).app j x,
  --   have hx : x = x' := by refl, },
  -- have := discrete_quotient_functor_id S,
  -- -- rw ← nat_iso.naturality_2 (eq_to_iso (functor_id_comp (functor_for_colim_presheaf S X))),
  -- sorry,
  -- rw functor_id_comp (functor_for_colim_presheaf S X),
  --rw category_theory.functor.id_comp (functor_for_colim_presheaf S X),
  -- have : j.op.unop = j := by simp only [eq_self_iff_true, opposite.unop_op],
  -- rw this,
  --{ sorry, },

  -- change' (discrete_quotient_functor (𝟙 S)).op with 𝟭 (discrete_quotient S)ᵒᵖ,
  -- injections_and_clear,
  -- dsimp,
  -- let h := h_1 j,
  --rw h,
  -- rw this,
  -- { rw discrete_quotient_functor_id_op S,
  --   refl, },
  -- dsimp at *,
  -- rw discrete_quotient_functor_id_op S,
  -- rw this,
  -- simp_rw [discrete_quotient_functor_id_op S],
end

lemma le_comap_of_comap {S T : Profinite.{u}} (f : T ⟶ S) (Si : discrete_quotient S) :
  discrete_quotient.le_comap f.continuous_to_fun (Si.comap f.continuous_to_fun) Si :=
λ x y z, by { assumption }

def nat_map_fintype_diagrams {S T : Profinite.{u}} (f : T ⟶ S) :
  (discrete_quotient_functor f) ⋙ T.fintype_diagram ⟶ S.fintype_diagram :=
{ app := λ Si, discrete_quotient.map (le_comap_of_comap f Si), }

lemma nat_map_fintype_diagrams_id (S : Profinite.{u}) :
  nat_map_fintype_diagrams (𝟙 S) = 𝟙 S.fintype_diagram :=
begin
  ext,
  induction x_1,
  { exact rfl, },
  exact rfl,
end

def nat_map_functors_for_colim {S T : Profinite.{u}} (X : Type (u+1)) (f : T ⟶ S) :
  (functor_for_colim_presheaf S X) ⟶
  (discrete_quotient_functor f).op ⋙ (functor_for_colim_presheaf T X) :=
whisker_right (nat_trans.op (whisker_right (nat_map_fintype_diagrams.{u} f)
  (Fintype.incl ⋙ ulift_functor.{u+1}))) (yoneda.obj X)

def nat_map_functors_for_colim' {S T : Profinite.{u}} (X : Type (u+1)) (f : T ⟶ S) :
  (functor_for_colim_presheaf S X) ⟶
  (discrete_quotient_functor f).op ⋙ (functor_for_colim_presheaf T X) :=
whisker_right (nat_trans.op (nat_map_fintype_diagrams.{u} f))
  ((Fintype.incl ⋙ ulift_functor.{u+1}).op ⋙ (yoneda.obj X))

lemma nat_map_functors_for_colim_id (S : Profinite.{u}) (X : Type (u+1)) :
  nat_map_functors_for_colim X (𝟙 S) = 𝟙 (functor_for_colim_presheaf S X) :=
begin
  unfold nat_map_functors_for_colim,
  rw nat_map_fintype_diagrams_id S,
  ext,
  cases j,
  induction j,
  { dsimp, exact rfl, },
  exact dec_trivial,
end

def cocones_functor_precompose (X : Type (u+1)) {S T : Profinite.{u}} (f : T ⟶ S) :
  cocone ((discrete_quotient_functor f).op ⋙ (functor_for_colim_presheaf T X)) ⥤
  cocone (functor_for_colim_presheaf S X) :=
cocones.precompose (nat_map_functors_for_colim X f)

def cocones_functor_whiskering (X : Type (u+1)) {S T : Profinite.{u}} (f : T ⟶ S) :
  cocone (functor_for_colim_presheaf T X) ⥤
  cocone ((discrete_quotient_functor f).op ⋙ (functor_for_colim_presheaf T X)) :=
cocones.whiskering _

def cocones_functor (X : Type (u+1)) {S T : Profinite.{u}} (f : T ⟶ S) :
  cocone (functor_for_colim_presheaf T X) ⥤ cocone (functor_for_colim_presheaf S X) :=
cocones_functor_whiskering X f ⋙ cocones_functor_precompose X f

def colim_copresheaf_Cat (X : Type (u+1)) : Profinite.{u} ⥤ Cat :=
{ obj := λ S, Cat.of (cocone (functor_for_colim_presheaf S X)),
  map := λ T S f, cocones_functor X f,
  map_id' :=
  begin
    intros S,
    unfold cocones_functor,
    unfold cocones_functor_whiskering,
    unfold cocones_functor_precompose,
    rw nat_map_functors_for_colim_id S X,
    apply category_theory.functor.ext,
    { intros c d f,
      dsimp,
      simp only [category_theory.functor.comp_map, category_theory.Cat.id_map],
      dsimp at *,
      ext,
      dsimp at x,
      dsimp,
      dsimp only [eq_to_hom],
      simp only [eq_mpr_eq_cast],
      dsimp at *,
      sorry, },
    sorry,
    -- rw discrete_quotient_functor_id_op S
  end,
  map_comp' :=
  begin
    intros T S U f g,
    unfold cocones_functor,
    unfold cocones_functor_whiskering,
    unfold cocones_functor_precompose,
    sorry,
  end, }

def colim_presheaf (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
{
  obj := λ S, colimit (functor_for_colim_presheaf S.unop X),
  map := λ S T f, (colim.map (nat_map_functors_for_colim' X f.unop)) ≫
    (colimit.pre ((functor_for_colim_presheaf T.unop X)) (discrete_quotient_functor f.unop).op),
  map_id' :=
  begin
    intros S,
    have : (𝟙 S).unop = 𝟙 S.unop := by simp only [eq_self_iff_true, category_theory.unop_id],
    rw this,
    unfold nat_map_functors_for_colim',
    rw nat_map_fintype_diagrams_id,
    ext,
    -- simp only [category_theory.nat_trans.op_app,
    --   quiver.hom.unop_op,
    --   category_theory.whisker_right_app,
    --   category_theory.types_comp_apply,
    --   category_theory.functor.comp_map,
    --   category_theory.limits.colimit.ι_map_assoc,
    --   category_theory.functor.op_map,
    --   category_theory.types_id_apply,
    --   category_theory.yoneda_obj_map],
    -- have h :
  end,
  map_comp' := sorry,
}

variable (F : Π (S : Profinite.{u}), (discrete_quotient S)ᵒᵖ ⥤ Type (u+1))
variable (G : Fintype.{u}ᵒᵖ ⥤ Type (u+1))

def H (S : Profinite.{u}) : (discrete_quotient S)ᵒᵖ ⥤ Type (u+1) := S.fintype_diagram.op ⋙ G

def nat_map_for_colim {S T : Profinite.{u}} (f : T ⟶ S) :
  H G S ⟶ (discrete_quotient_functor f).op ⋙ H G T :=
whisker_right (nat_trans.op (nat_map_fintype_diagrams.{u} f)) G

def colim_presheaf' : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
{ obj := λ S, colim.obj (H G S.unop),
  map := λ S T f, colim.map (nat_map_for_colim G f.unop) ≫
    (colimit.pre (H G T.unop) (discrete_quotient_functor f.unop).op),
  map_id' :=
  begin
    intros S,
    have : (𝟙 S).unop = 𝟙 S.unop := by simp only [eq_self_iff_true, category_theory.unop_id],
    rw this,
    unfold nat_map_for_colim,
    rw nat_map_fintype_diagrams_id,
    have h₁ : whisker_right (nat_trans.op (𝟙 (unop S).fintype_diagram)) G =
      𝟙 ((unop S).fintype_diagram.op ⋙ G) := by
      simp only [eq_self_iff_true,
      category_theory.nat_trans.op_id,
      category_theory.whisker_right_id'],
    rw h₁,
    have h₂ : colim.map (𝟙 ((unop S).fintype_diagram.op ⋙ G)) = 𝟙 (colim.obj _) := by
      simp only [eq_self_iff_true, category_theory.functor.map_id],
    rw h₂,
    change (unop S).fintype_diagram.op ⋙ G with H G (unop S),
    simp only [category_theory.category.id_comp],
    let φ := whisker_right (eq_to_hom (discrete_quotient_functor_id_op.{u} S.unop)) (H G S.unop),
    let f := colim.map φ,
    have h₃ : colimit.pre _ _ = f := by sorry,
    rw h₃,
    sorry,
  end,
  map_comp' :=
  begin
    intros S T U f g,
    unfold nat_map_for_colim,
    sorry,
  end, }

variables (C : Type u) [category.{v} C]
#check has_colimits_of_size.{v}
variables (S : Profinite.{u}) (X : Type (u+1))
#check Fintype.incl.{u+1}
#check (S.fintype_diagram ⋙ Fintype.incl.{u}).op
#check discrete_quotient S

variables {T : Profinite.{u}} (f : T ⟶ S)
variables (Si : discrete_quotient S)
variables (α : Type*) (x : α) (rel : α → α → Prop)
#check set_of (rel x)
#check ((discrete_quotient_functor f).map (𝟙 Si)).le
#check (Fintype.of Si).α
#check (Si.comap f.continuous_to_fun).proj
#check Si.proj
#check (Si.comap f.continuous_to_fun : discrete_quotient T)
#check ↥Si
#check S.to_CompHaus.to_Top.α
#check (f.to_fun : T.to_CompHaus.to_Top.α → S.to_CompHaus.to_Top.α)
#check discrete_quotient.map (discrete_quotient.le_comap_id (Si.comap f.continuous_to_fun))
#check nat_map_functors_for_colim X (𝟙 S)

-- def discrete_quotient_functor' {S T : Profinite.{u}} (f : T ⟶ S) :
--   discrete_quotient T ⥤ discrete_quotient S :=
-- {
--   obj := λ Ti, discrete_quotient.map Ti f.continuous_to_fun,
-- }

-- lemma comap_as_subtype {S T : Profinite.{u}} (f : T ⟶ S) (Si : discrete_quotient S) :
--   Si.comap f.continuous_to_fun = {x : Si // }

#exit

instance (S : Profinite.{u}) : category.{u+1} (discrete_quotient S)ᵒᵖ :=
{ hom := λ A B, ulift.{u+1 u} $ A ⟶ B,
  id := λ A, ⟨𝟙 _⟩,
  comp := λ A B C f g, ⟨f.down ≫ g.down⟩}

def ulift_equiv_discrete_quotient (S : Profinite.{u}) :
   ulift_hom.{u+1} (ulift.{u+1} (discrete_quotient S)ᵒᵖ) ≌ (discrete_quotient S)ᵒᵖ :=
(ulift_hom_ulift_category.equiv (discrete_quotient S)ᵒᵖ).symm


-- def map_for_functor_projection {S : Profinite.{u}} {Si Sj : discrete_quotient S} (f : Si ⟶ Sj)
--   (X : Type (u+1)) : (Si → X) → X := sorry

-- lemma surj_transition_map {S : Profinite.{u}} {Si Sj : discrete_quotient S} (f : Si ⟶ Sj) :
--   function.surjective (discrete_quotient.of_le f.1.1) :=
-- begin
--   have : function.surjective (discrete_quotient.of_le f.1.1 ∘ Si.proj),
--   { simp only [discrete_quotient.of_le_proj],
--     exact discrete_quotient.proj_surjective _, },
--   exact function.surjective.of_comp this,
-- end

-- def map_for_functor {S : Profinite.{u}} {Si Sj : discrete_quotient S} (f : Si ⟶ Sj)
--   (X : Type (u+1)) : (Si → X) → (Sj → X) :=
