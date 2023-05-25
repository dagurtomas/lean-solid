import discrete.discrete_loc_const

noncomputable theory

universe u

open category_theory
open Profinite
open opposite

lemma Profinite_is_iso_iff_bijective {S T : Profinite.{u}} (f : S ⟶ T) :
  is_iso f ↔ function.bijective f :=
  ⟨by {introsI hf, exact concrete_category.bijective_of_is_iso f },
    λ hf, Profinite.is_iso_of_bijective f hf⟩

instance fintype_set_range_of_compact_to_discrete {X Y : Type*} {f : X → Y}
  [topological_space X] [topological_space Y] [discrete_topology Y] [compact_space X]
  (hf : continuous f) : fintype (set.range f) :=
set.finite.fintype (is_compact_iff_finite.mp (is_compact_range hf))

instance fintype_set_range_of_loc_const_compact_to_discrete {X : Type*} {Y : Type*}
  [topological_space X] [compact_space X] (f : locally_constant X Y) : fintype (set.range f) :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := {eq_bot := rfl},
  have hf : continuous f := locally_constant.continuous f,
  exact fintype_set_range_of_compact_to_discrete hf,
end

def finset_range_of_loc_const {X : Type*} {Y : Type*}  [topological_space X]
  [compact_space X] (f : locally_constant X Y) : finset Y :=
@set.to_finset Y (set.range f) (fintype_set_range_of_loc_const_compact_to_discrete f)

instance {X Y : Type*} (f : X → Y) (A : finset X) : fintype (f '' A) := fintype.of_finite (f '' A)

def parts_of_loc_const {X : Type*} {Y : Type*} [topological_space X]
  [compact_space X] (f : locally_constant X Y) : finset (set X) :=
set.to_finset ((λ i, f ⁻¹' {i}) '' (finset_range_of_loc_const f))

instance {X : Type*} {Y : Type*} [topological_space X] [compact_space X]
  (f : locally_constant X Y) : fintype (parts_of_loc_const f) :=
fintype.of_finset (parts_of_loc_const f) (λ x, iff.rfl)

instance part_compact {S : Profinite.{u}} {X : Type (u+1)} {f : locally_constant S X}
  (T : parts_of_loc_const f) : compact_space T :=
begin
  cases T,
  dsimp,
  rw ← is_compact_iff_compact_space,
  dsimp [parts_of_loc_const] at T_property,
  simp only [set.mem_image, set.mem_to_finset] at T_property,
  obtain ⟨x, h⟩ := T_property,
  rw ← h.2,
  exact is_closed.is_compact (is_locally_constant.is_closed_fiber f.is_locally_constant x),
end

def index_map {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X) :
  parts_of_loc_const f → Profinite.{u} :=
λ T, Profinite.of T

def part_to_Profinite_map {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (T : parts_of_loc_const f) : index_map f T ⟶ S :=
⟨((λ t, t) : T → S), by continuity⟩

def Profinite_of_to_part_map {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (T : parts_of_loc_const f) : Profinite.of T ⟶ index_map f T := 𝟙 _

def part_to_Profinite_of_map {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (T : parts_of_loc_const f) : index_map f T ⟶ Profinite.of T := 𝟙 _

def Profinite_hom_sigma_of_parts {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X) :
  Profinite.sigma (index_map f) ⟶ S :=
Profinite.sigma.desc (index_map f) (λ T, ⟨((λ t, t) : T → S), by continuity⟩)

instance is_iso_Profinite_hom_sigma_of_parts {S : Profinite.{u}} {X : Type (u+1)}
  (f : locally_constant S X) :  is_iso (Profinite_hom_sigma_of_parts f) :=
begin
  rw Profinite_is_iso_iff_bijective _,
  split,
  { intros a b h,
    obtain ⟨ia, xa, ha⟩ := sigma.ι_jointly_surjective (index_map f) a,
    obtain ⟨ib, xb, hb⟩ := sigma.ι_jointly_surjective (index_map f) b,
    rw ← ha,
    rw ← hb,
    dsimp [sigma.ι],
    rw ← ha at h,
    rw ← hb at h,
    dsimp [Profinite_hom_sigma_of_parts] at h,
    simp only [← category_theory.comp_apply, sigma.ι_desc] at h,
    ext,
    { dsimp [parts_of_loc_const] at ia,
      cases ia,
      simp only [set.mem_image, set.mem_to_finset] at ia_property,
      obtain ⟨ia', ha'⟩ := ia_property,
      dsimp [parts_of_loc_const] at ib,
      cases ib,
      simp only [set.mem_image, set.mem_to_finset] at ib_property,
      obtain ⟨ib', hb'⟩ := ib_property,
      dsimp [index_map] at *,
      cases xa,
      cases xb,
      dsimp at h,
      have := pairwise_disjoint_fiber f,
      have h1 := this ia' ib',
      rw ← not_imp_not at h1,
      simp at h1,
      suffices : ia' = ib',
      { rw ← ha'.2,
        rw ← hb'.2,
        rw this },
      apply h1,
      rw ← ha'.2 at xa_property,
      rw ← hb'.2 at xb_property,
      rw h at xa_property,
      rw set.not_disjoint_iff,
      use xb_val,
      exact ⟨xa_property, xb_property⟩ },
    exact h },
  { apply sigma.desc_surjective,
    intros s,
    use f ⁻¹' ({f s}),
    dsimp [parts_of_loc_const, finset_range_of_loc_const],
    simp only [set.mem_image, set.mem_to_finset, exists_exists_eq_and,
      set.coe_to_finset, exists_apply_eq_apply],
    use f s,
    exact ⟨set.mem_range_self s, by refl⟩,
    dsimp [index_map],
    use s,
    simp only [set.mem_preimage, set.mem_singleton],
    refl },
end .

def Profinite_iso_sigma_of_parts {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X) :
  Profinite.sigma (index_map f) ≅ S :=
as_iso (Profinite_hom_sigma_of_parts f)

lemma product_condition_general_finite {α : Type u} (X : CondensedSet.{u}) [fintype α]
  (S : α → Profinite.{u}) : function.bijective (λ (t : X.val.obj (op $ Profinite.sigma S)),
  ((λ a, X.val.map (Profinite.sigma.ι S a).op t) : Π (a : α), X.val.obj $ op $ S a)) :=
begin
  -- basically done in condensed.is_proetale_sheaf:
  have : X.val.is_proetale_sheaf_of_types,
  { rw (functor.is_proetale_sheaf_of_types_tfae X.val).out 1 0,
    rw ← is_sheaf_iff_is_sheaf_of_type,
    exact X.cond },
  exact (functor.finite_product_condition_of_is_proetale_sheaf_of_types X.val this)
    (Fintype.of α) S
end

def Y_of_coproduct_equiv_product {α : Type u} (X : CondensedSet.{u}) [fintype α]
  (S : α → Profinite.{u}) : X.val.obj (op $ Profinite.sigma S) ≃ Π (a : α), X.val.obj $ op $ S a :=
equiv.of_bijective (λ (t : X.val.obj (op $ Profinite.sigma S)),
  ((λ a, X.val.map (Profinite.sigma.ι S a).op t) : Π (a : α), X.val.obj $ op $ S a))
  (product_condition_general_finite X S)

instance fiber_compact {S : Profinite.{u}} {X : Type (u+1)} {f : locally_constant S X}
  (x : X) : compact_space (f ⁻¹' {x}) :=
begin
  rw ← is_compact_iff_compact_space,
  exact is_closed.is_compact (is_locally_constant.is_closed_fiber f.is_locally_constant x),
end

lemma part_property_as_existential {S : Profinite.{u}} {X : Type (u+1)}
  {f : locally_constant S X}
  (T : parts_of_loc_const f) : ∃ (x : X),
  x ∈ finset_range_of_loc_const f ∧ f ⁻¹' {x} = T.val :=
begin
  dsimp [parts_of_loc_const] at T,
  cases T,
  simp only [set.mem_image, set.mem_to_finset] at T_property,
  exact T_property,
end

def value_of_part {S : Profinite.{u}} {X : Type (u+1)}
  {f : locally_constant S X}
  (T : parts_of_loc_const f) : X :=
(part_property_as_existential T).some

lemma value_of_part_satisfies_prop {S : Profinite.{u}} {X : Type (u+1)}
  {f : locally_constant S X}
  (T : parts_of_loc_const f) : value_of_part T ∈ finset_range_of_loc_const f ∧
  f ⁻¹' {value_of_part T} = T.val :=
Exists.some_spec (part_property_as_existential T)

lemma value_of_part_as_existential {S : Profinite.{u}} {X : Type (u+1)}
  {f : locally_constant S X}
  (T : parts_of_loc_const f) : (∃ (s : S), f s = value_of_part T) ∧ f ⁻¹' {value_of_part T} = T :=
begin
  have := value_of_part_satisfies_prop T,
  dsimp [finset_range_of_loc_const] at this,
  simp only [set.mem_range, set.mem_to_finset] at this,
  exact this,
end

def counit_loc_const_app_coordinate {S : Profinite.{u}} {Y : CondensedSet.{u}}
  (f : locally_constant S (Y.val.obj (op point))) (T : parts_of_loc_const f) :
  Y.val.obj (op (Profinite.of T)) :=
Y.val.map (punit.elim _).op (value_of_part T)

def counit_loc_const_app_app (S : Profinite.{u}) (Y : CondensedSet.{u}) :
  locally_constant S (Y.val.obj (op point)) → Y.val.obj (op S) :=
λ f, Y.val.map (Profinite_iso_sigma_of_parts f).inv.op
  ((Y_of_coproduct_equiv_product Y (index_map f)).inv_fun
  (counit_loc_const_app_coordinate f))

def part_of_comap {S T : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (g : T ⟶ S) (W : parts_of_loc_const (f.comap g)) : parts_of_loc_const f :=
⟨f ⁻¹' {value_of_part W},
begin
  dsimp [parts_of_loc_const],
  simp only [set.mem_image, set.mem_to_finset],
  use value_of_part W,
  dsimp [finset_range_of_loc_const],
  simp only [set.mem_range, and_true, set.mem_to_finset, eq_self_iff_true],
  rw ← Exists.some_spec (value_of_part_as_existential W).1,
  use g ((value_of_part_as_existential W).1.some),
  simp only [← function.comp_app f g],
  exact congr_fun (locally_constant.coe_comap g f g.continuous).symm _,
end⟩

lemma value_of_part_of_comap_eq_value_of_part {S T : Profinite.{u}} {X : Type (u+1)}
  (f : locally_constant S X) (g : T ⟶ S) (W : parts_of_loc_const (f.comap g)) :
  value_of_part (part_of_comap f g W) = value_of_part W :=
begin
  let x := value_of_part (part_of_comap f g W),
  let y := value_of_part W,
  have hpW := (value_of_part_satisfies_prop (part_of_comap f g W)),
  change value_of_part (part_of_comap f g W) with x at hpW,
  change value_of_part (part_of_comap f g W) with x,
  dsimp [part_of_comap] at *,
  change value_of_part W with y at hpW,
  change value_of_part W with y,
  have := pairwise_disjoint_fiber f,
  have h1 := this x y,
  rw ← not_imp_not at h1,
  simp at h1,
  apply h1,
  rw set.not_disjoint_iff,
  dsimp [finset_range_of_loc_const] at hpW,
  simp only [set.mem_range, set.mem_to_finset] at hpW,
  obtain ⟨z, h⟩ := hpW.1,
  use z,
  change (λ a, f ⁻¹' {a}) x with f ⁻¹' {x},
  change (λ a, f ⁻¹' {a}) y with f ⁻¹' {y},
  rw ← hpW.2,
  dsimp,
  exact ⟨h, h⟩,
end

def map_from_part_to_preimage {S T : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (g : T ⟶ S) (W : parts_of_loc_const (f.comap g)) :
  W → f ⁻¹' {value_of_part W} := λ w, ⟨g w,
begin
  simp only [set.mem_preimage, set.mem_singleton_iff, ← function.comp_app f g],
  rw congr_fun (locally_constant.coe_comap g f g.continuous).symm _,
  have := (value_of_part_satisfies_prop W).2,
  dsimp [parts_of_loc_const] at W,
  dsimp [finset_range_of_loc_const] at *,
  cases w,
  rw ← this at w_property,
  simp only [set.mem_preimage, set.mem_singleton_iff] at w_property,
  exact w_property,
end⟩

def map_from_part_to_comap_part {S T : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (g : T ⟶ S) (W : parts_of_loc_const (f.comap g)) :
  W → part_of_comap f g W := map_from_part_to_preimage f g W

def Profinite_hom_part_to_comap_part {S T : Profinite.{u}} {X : Type (u+1)}
  (f : locally_constant S X) (g : T ⟶ S) (W : parts_of_loc_const (f.comap g)) :
  Profinite.of W ⟶ Profinite.of (part_of_comap f g W) :=
⟨map_from_part_to_comap_part f g W,
begin
  dsimp [map_from_part_to_comap_part, map_from_part_to_preimage],
  refine continuous.subtype_mk _ (λ (x : ↥(of ↥↑W)), map_from_part_to_preimage._proof_3 f g W x),
  refine continuous.comp g.continuous _,
  continuity,
end⟩

def Y_val_map_of_products_proj_coordinate {S T : Profinite.{u}} {Y : CondensedSet.{u}}
  (f : locally_constant S (Y.val.obj (op point))) (g : T ⟶ S)
  (W : parts_of_loc_const (f.comap g)) :
  Y.val.obj (op $ Profinite.of (part_of_comap f g W)) → Y.val.obj (op $ Profinite.of W) :=
Y.val.map (Profinite_hom_part_to_comap_part f g W).op

def Y_val_map_of_products_coordinate {S T : Profinite.{u}} {Y : CondensedSet.{u}}
  (f : locally_constant S (Y.val.obj (op point))) (g : T ⟶ S)
  (W : parts_of_loc_const (f.comap g)) :
  (Π (V : parts_of_loc_const f), Y.val.obj (op $ Profinite.of V)) → Y.val.obj (op $ Profinite.of W) :=
Y_val_map_of_products_proj_coordinate f g W ∘ (λ φ, φ (part_of_comap f g W))

def Y_val_map_of_products {S T : Profinite.{u}} {Y : CondensedSet.{u}}
  (f : locally_constant S (Y.val.obj (op point))) (g : T ⟶ S) :
  (Π (V : parts_of_loc_const f), Y.val.obj (op $ Profinite.of V)) →
  (Π (W : parts_of_loc_const (f.comap g)), Y.val.obj (op $ Profinite.of W)) :=
λ φ W, Y_val_map_of_products_coordinate f g W φ

lemma map_of_products_naturality_square {S T : Profinite.{u}} {Y : CondensedSet.{u}}
  (f : locally_constant S (Y.val.obj (op point))) (g : T ⟶ S) :
  Y_val_map_of_products f g ∘
  (Y_of_coproduct_equiv_product Y (index_map f)).to_fun ∘
  Y.val.map (Profinite_iso_sigma_of_parts f).hom.op =
  (Y_of_coproduct_equiv_product Y (index_map (f.comap g))).to_fun ∘
  Y.val.map (Profinite_iso_sigma_of_parts (f.comap g)).hom.op ∘
  Y.val.map g.op :=
begin
  dsimp [Y_val_map_of_products,
    Y_val_map_of_products_coordinate,
    Y_val_map_of_products_proj_coordinate,
    Profinite_hom_part_to_comap_part,
    map_from_part_to_comap_part,
    map_from_part_to_preimage,
    Y_of_coproduct_equiv_product,
    Profinite_iso_sigma_of_parts,
    Profinite_hom_sigma_of_parts],
  ext,
  dsimp,
  simp only [← category_theory.functor_to_types.map_comp_apply,
    ← category_theory.op_comp,
    sigma.ι_desc, sigma.ι_desc_assoc],
  refl,
end .

lemma map_of_products_naturality_square_rearrange {S T : Profinite.{u}} {Y : CondensedSet.{u}}
  (f : locally_constant S (Y.val.obj (op point))) (g : T ⟶ S) :
  Y.val.map g.op =
  Y.val.map (Profinite_iso_sigma_of_parts (f.comap g)).inv.op ∘
  (Y_of_coproduct_equiv_product Y (index_map (f.comap g))).inv_fun ∘
  Y_val_map_of_products f g ∘
  (Y_of_coproduct_equiv_product Y (index_map f)).to_fun ∘
  Y.val.map (Profinite_iso_sigma_of_parts f).hom.op :=
begin
  rw map_of_products_naturality_square f g,
  simp only [equiv.to_fun_as_coe, equiv.inv_fun_as_coe],
  dsimp,
  ext,
  dsimp,
  simp only [equiv.symm_apply_apply,
    ← category_theory.functor_to_types.map_comp_apply,
    ← category_theory.op_comp,
    iso.inv_hom_id_assoc],
end .

lemma Profinite_comp_punit_elim {S T : Profinite.{u}} (f : S ⟶ T) :
  f ≫ punit.elim T = punit.elim S := by refl

def counit_loc_const_app (Y : CondensedSet.{u}) :
  loc_const_CondensedSet (Y.val.obj (op point)) ⟶ Y :=
{ val :=
  { app := λ S, counit_loc_const_app_app S.unop Y,
    naturality' :=
    begin
      intros S T g,
      ext f,
      simp only [category_theory.types_comp],
      rw ← quiver.hom.op_unop g,
      rw map_of_products_naturality_square_rearrange f g.unop,
      dsimp [counit_loc_const_app_app],
      simp only [← category_theory.functor_to_types.map_comp_apply,
        ← category_theory.op_comp,
        iso.hom_inv_id,
        equiv.apply_symm_apply,
        category_theory.functor_to_types.map_id_apply,
        category_theory.op_id],
      congr,
      dsimp [loc_const_CondensedSet, Y_val_map_of_products, loc_const_presheaf,
        Y_val_map_of_products_coordinate, Y_val_map_of_products_proj_coordinate,
        counit_loc_const_app_coordinate, Profinite_hom_part_to_comap_part,
        map_from_part_to_comap_part, map_from_part_to_preimage],
      ext W,
      dsimp [counit_loc_const_app_coordinate],
      simp only [← category_theory.functor_to_types.map_comp_apply,
        ← category_theory.op_comp],
      rw Profinite_comp_punit_elim _,
      rw value_of_part_of_comap_eq_value_of_part f g.unop W,
    end } } .

lemma inv_op_eq_op_inv {S T : Profinite.{u}} (f : S ≅ T) : f.inv.op = f.op.inv := by refl

def loc_const_on_part {S : Profinite.{u}} {X Y : Type (u+1)} {f : locally_constant S X} {p : X → Y}
  (W : parts_of_loc_const (loc_const_map f p)) : locally_constant (Profinite.of W) X :=
{ to_fun := λ w, f w.val,
  is_locally_constant :=
  begin
    apply is_locally_constant.comp_continuous,
    exact f.is_locally_constant,
    exact continuous_subtype_val,
  end }

def part_on_part_to_sigma_of_parts {S : Profinite.{u}} {X Y : Type (u+1)}
  {f : locally_constant S X} {p : X → Y} (W : parts_of_loc_const (loc_const_map f p))
  (V : parts_of_loc_const (loc_const_on_part W)) :
  index_map (loc_const_on_part W) V ⟶
  Profinite.sigma (index_map f) :=
part_to_Profinite_map _ V ≫ Profinite_of_to_part_map _ W ≫ part_to_Profinite_map _ W ≫
(Profinite_iso_sigma_of_parts f).inv

def map_of_smaller_sigmas {S : Profinite.{u}} {X Y : Type (u+1)} {f : locally_constant S X}
  {p : X → Y} (W : parts_of_loc_const (loc_const_map f p)) :
  Profinite.sigma (index_map (loc_const_on_part W)) ⟶
  Profinite.sigma (index_map f) :=
sigma.desc (index_map (loc_const_on_part W))
  (part_on_part_to_sigma_of_parts W)

def map_for_sigmas {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X) (p : X → Y)
  (W : parts_of_loc_const (loc_const_map f p)) :
  (index_map (loc_const_map f p)) W ⟶
  Profinite.sigma (index_map f) :=
part_to_Profinite_of_map _ W ≫
  (Profinite_iso_sigma_of_parts (loc_const_on_part W)).inv ≫
  map_of_smaller_sigmas W

def map_sigmas {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X) (p : X → Y) :
  Profinite.sigma (index_map (loc_const_map f p))
  ⟶ Profinite.sigma (index_map f) :=
sigma.desc (index_map (loc_const_map f p)) (map_for_sigmas f p)

lemma incl_lemma {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X)
  (W : parts_of_loc_const f) : part_to_Profinite_map f W ≫ (Profinite_iso_sigma_of_parts f).inv =
  sigma.ι (index_map f) W :=
begin
  rw ← iso.cancel_iso_hom_right _ _ (Profinite_iso_sigma_of_parts f),
  simp only [category.comp_id, iso.inv_hom_id, category.assoc],
  dsimp [Profinite_iso_sigma_of_parts, Profinite_hom_sigma_of_parts],
  simp only [Profinite.sigma.ι_desc],
  refl,
end

lemma Profinite_hom_iso_lemma {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X) :
  ∀ x, (Profinite_hom_sigma_of_parts f) ((Profinite_iso_sigma_of_parts f).inv x) = x :=
begin
  intro x,
  simp only [← category_theory.comp_apply],
  change Profinite_hom_sigma_of_parts f with (Profinite_iso_sigma_of_parts f).hom,
  simp only [Profinite.coe_id, id.def, category_theory.iso.inv_hom_id, eq_self_iff_true],
end

lemma Profintie_hom_factorisation_aux {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X)
  (p : X → Y) (W : parts_of_loc_const (loc_const_map f p)) :
  (Profinite_iso_sigma_of_parts (loc_const_on_part W)).inv ≫
  sigma.desc (index_map (loc_const_on_part W))
  (part_on_part_to_sigma_of_parts W) ≫ Profinite_hom_sigma_of_parts f =
  sigma.ι (index_map (loc_const_map f p)) W ≫
  Profinite_hom_sigma_of_parts (loc_const_map f p) :=
begin
  let g := Profinite_hom_sigma_of_parts f,
  change Profinite_hom_sigma_of_parts f with g,
  rw ← iso.cancel_iso_hom_left (Profinite_iso_sigma_of_parts (loc_const_on_part W)) _ _,
  simp only [category_theory.iso.hom_inv_id_assoc],
  dsimp [Profinite_iso_sigma_of_parts, Profinite_hom_sigma_of_parts],
  ext b,
  obtain ⟨T, xb, hb⟩ := sigma.ι_jointly_surjective
    (index_map (loc_const_on_part W)) b,
  rw ← hb,
  simp only [← category_theory.comp_apply, sigma.ι_desc_assoc, sigma.ι_desc],
  dsimp only [part_on_part_to_sigma_of_parts, part_to_Profinite_map, Profinite_of_to_part_map],
  simp only [category_theory.category.id_comp,
    continuous_map.coe_mk,
    Profinite.coe_comp,
    function.comp_app,
    category_theory.category.assoc],
  change g with Profinite_hom_sigma_of_parts f,
  exact Profinite_hom_iso_lemma f _,
end .

lemma Profinite_hom_factorisation {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X)
  (p : X → Y) : map_sigmas f p ≫ Profinite_hom_sigma_of_parts f =
  Profinite_hom_sigma_of_parts (loc_const_map f p) :=
begin
  ext,
  dsimp [map_sigmas],
  obtain ⟨W, xa, ha⟩ := sigma.ι_jointly_surjective
    (index_map (loc_const_map f p)) a,
  rw ← ha,
  simp only [← category_theory.comp_apply, sigma.ι_desc_assoc, sigma.ι_desc],
  dsimp only [map_for_sigmas, map_of_smaller_sigmas, part_to_Profinite_of_map],
  simp only [category.id_comp, category.assoc],
  congr' 1,
  exact Profintie_hom_factorisation_aux f p W,
end .

lemma Profintie_hom_factorisation₁ {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X)
  (p : X → Y) (W : parts_of_loc_const (loc_const_map f p)) :
  (Profinite_iso_sigma_of_parts (loc_const_on_part W)).inv ≫
  sigma.desc (index_map (loc_const_on_part W))
  (part_on_part_to_sigma_of_parts W) =
  sigma.ι (index_map (loc_const_map f p)) W ≫
  map_sigmas f p :=
begin
  rw ← iso.cancel_iso_hom_right _ _ (Profinite_iso_sigma_of_parts f),
  simp only [category.assoc],
  change (Profinite_iso_sigma_of_parts f).hom with Profinite_hom_sigma_of_parts f,
  rw Profinite_hom_factorisation f p,
  exact Profintie_hom_factorisation_aux f p W,
end

instance is_iso_map_sigmas {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X)
  (p : X → Y) : is_iso (map_sigmas f p) :=
begin
  use Profinite_hom_sigma_of_parts f ≫(Profinite_iso_sigma_of_parts (loc_const_map f p)).inv,
  split,
  { simp only [← category.assoc],
    rw Profinite_hom_factorisation f p,
    change Profinite_hom_sigma_of_parts (loc_const_map f p) with
      (Profinite_iso_sigma_of_parts _).hom,
    simp only [iso.hom_inv_id] },
  change Profinite_hom_sigma_of_parts f with (Profinite_iso_sigma_of_parts f).hom,
  rw ← iso.cancel_iso_inv_left (Profinite_iso_sigma_of_parts f) _ _,
  simp only [category.comp_id,
    iso.inv_hom_id_assoc,
    category.assoc],
  rw ← iso.cancel_iso_hom_right _ _ (Profinite_iso_sigma_of_parts f),
  simp only [category_theory.iso.inv_hom_id, category_theory.category.assoc],
  rw ← iso.cancel_iso_hom_left (Profinite_iso_sigma_of_parts (loc_const_map f p)) _ _,
  simp only [category.comp_id, iso.hom_inv_id_assoc],
  exact Profinite_hom_factorisation _ _,
end

def map_sigmas_iso {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X) (p : X → Y) :
  Profinite.sigma (index_map (loc_const_map f p))
  ≅ Profinite.sigma (index_map f) :=
as_iso (map_sigmas f p)

lemma Profinite_iso_factorisation {S : Profinite.{u}} {X Y : Type (u+1)} (f : locally_constant S X)
  (p : X → Y) : (map_sigmas_iso f p) ≪≫ Profinite_iso_sigma_of_parts f =
  Profinite_iso_sigma_of_parts (loc_const_map f p) :=
begin
  ext,
  dsimp,
  simp only [← category_theory.comp_apply],
  change (Profinite_iso_sigma_of_parts f).hom with Profinite_hom_sigma_of_parts f,
  change (Profinite_iso_sigma_of_parts (loc_const_map f p)).hom with
    Profinite_hom_sigma_of_parts (loc_const_map f p),
  change (map_sigmas_iso f p).hom with map_sigmas f p,
  rw Profinite_hom_factorisation _ _,
end

lemma iso_trans_op {S T U : Profinite.{u}} (f : S ≅ T) (g : T ≅ U) : (f ≪≫ g).op = g.op ≪≫ f.op :=
begin
  ext,
  dsimp,
  refl,
end

lemma Y_val_iso_hom_injective {S T : Profinite.{u}ᵒᵖ} (f : S ≅ T)
  (Y : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : function.injective (Y.map_iso f).hom :=
begin
  refine function.bijective.injective _,
  rw function.bijective_iff_has_inverse,
  use (Y.map_iso f).inv,
  split,
  intro a,
  simp only [functor.map_iso_inv,
    functor_to_types.map_inv_map_hom_apply,
    functor.map_iso_hom],
  intro a,
  simp only [functor.map_iso_inv,
    functor_to_types.map_hom_map_inv_apply,
    functor.map_iso_hom],
end

lemma Y_val_iso_inv_injective {S T : Profinite.{u}ᵒᵖ} (f : S ≅ T)
  (Y : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : function.injective (Y.map_iso f).inv :=
begin
  refine function.bijective.injective _,
  rw function.bijective_iff_has_inverse,
  use (Y.map_iso f).hom,
  split,
  intro a,
  simp only [functor.map_iso_inv,
    functor_to_types.map_hom_map_inv_apply,
    functor.map_iso_hom],
  intro a,
  simp only [functor.map_iso_inv,
    functor_to_types.map_inv_map_hom_apply,
    functor.map_iso_hom],
end

lemma naturality_square₁ {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  (f : locally_constant S (X.val.obj (op point))) (p : X ⟶ Y) :
  p.val.app (op point) ≫ Y.val.map (punit.elim S).op =
  X.val.map (punit.elim S).op ≫ p.val.app (op S) :=
begin
  ext,
  dsimp,
  rw category_theory.functor_to_types.naturality,
end

def X_of_point_to_prod {α : Type u} (X : CondensedSet.{u}) [fintype α]
  (S : α → Profinite.{u}) : X.val.obj (op point) ⟶ Π (a : α), X.val.obj (op (S a)) :=
λ x a, X.val.map (punit.elim (S a)).op x

def prod_of_coprods_map {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  (f : locally_constant S (X.val.obj (op point))) (p : X ⟶ Y) :
  (Π (T : parts_of_loc_const (loc_const_map f (p.val.app (op point)))),
  X.val.obj (op (Profinite.sigma (index_map (loc_const_on_part T)))))
  ⟶ Π (T : parts_of_loc_const (loc_const_map f (p.val.app (op point)))),
  X.val.obj (op (index_map (loc_const_map f (p.val.app (op point))) T)) :=
λ φ T, (X.val.map ((Profinite_iso_sigma_of_parts (loc_const_on_part T))).inv.op) (φ T)

lemma prop_of_part {S : Profinite.{u}} {X : Type (u+1)} {f : locally_constant S X}
  (W : parts_of_loc_const f) : ∃ (x : X), x ∈ set.range ⇑f ∧ ⇑f ⁻¹' {x} = W.val :=
begin
  cases W,
  dsimp [parts_of_loc_const, finset_range_of_loc_const] at W_property,
  simp only [set.mem_image, set.mem_to_finset, exists_exists_eq_and, set.coe_to_finset]
    at W_property,
  dsimp,
  exact W_property,
end .

lemma values_eq_of_fibers {S : Profinite.{u}} {X : Type (u+1)} {f : S → X} {x y : X}
  (hx : x ∈ set.range f) (h : f ⁻¹' {x} = f ⁻¹' {y}) : x = y :=
begin
  obtain ⟨s, hs⟩ := hx,
  rw ← hs,
  simp only [← set.mem_singleton_iff , ← set.mem_preimage],
  rw ← h,
  exact hs,
end

lemma values_eq_of_fibers_subset {S : Profinite.{u}} {X : Type (u+1)} {f : S → X} {x y : X}
  (hx : x ∈ set.range f) (h : f ⁻¹' {x} ⊆ f ⁻¹' {y}) : x = y :=
begin
  obtain ⟨s, hs⟩ := hx,
  rw ← hs,
  simp only [← set.mem_singleton_iff , ← set.mem_preimage],
  apply h,
  exact hs,
end

def part_of_value {S : Profinite.{u}} {X : Type (u+1)} {f : locally_constant S X} (x : X)
  (hx : x ∈ set.range f) : parts_of_loc_const f :=
⟨f ⁻¹' {x}, begin
  dsimp [parts_of_loc_const, finset_range_of_loc_const],
  simp only [set.mem_image, set.mem_to_finset, exists_exists_eq_and, set.coe_to_finset],
  use x,
  exact ⟨hx, by refl⟩,
end⟩

lemma value_of_part_on_part_satisfies_prop {S : Profinite.{u}} {X Y : Type (u+1)}
  {f : locally_constant S X} {p : X → Y} {W : parts_of_loc_const (loc_const_map f p)}
  (V : parts_of_loc_const (loc_const_on_part W)) : value_of_part V ∈ set.range f :=
begin
  have := (value_of_part_satisfies_prop V).1,
  dsimp [loc_const_on_part] at this,
  dsimp [finset_range_of_loc_const] at *,
  simp only [set.mem_range, set.mem_to_finset] at *,
  obtain ⟨w, h⟩ := this,
  use w.val,
  exact h,
end

def part_of_part_on_part {S : Profinite.{u}} {X Y : Type (u+1)} {f : locally_constant S X} {p : X → Y}
  {W : parts_of_loc_const (loc_const_map f p)} (V : parts_of_loc_const (loc_const_on_part W)) :
  parts_of_loc_const f :=
part_of_value (value_of_part V) (value_of_part_on_part_satisfies_prop V)

lemma v_val_val_in_V {S : Profinite.{u}} {X Y : Type (u+1)} {f : locally_constant S X}
  {p : X → Y} {W : parts_of_loc_const (loc_const_map f p)}
  {V : parts_of_loc_const (loc_const_on_part W)} (v : Profinite.of V) :
  v.val.val ∈ (part_of_part_on_part V).val :=
begin
  have := value_of_part_satisfies_prop V,
  have h : v.val ∈ V.val := v.property,
  rw ← this.2 at h,
  exact h,
end

def part_of_part_on_part_to_part {S : Profinite.{u}} {X Y : Type (u+1)} {f : locally_constant S X}
  {p : X → Y} {W : parts_of_loc_const (loc_const_map f p)}
  (V : parts_of_loc_const (loc_const_on_part W)) :
  index_map (loc_const_on_part W) V ⟶
  index_map f (part_of_part_on_part V)  :=
{ to_fun := λ v, ⟨v.val.val, v_val_val_in_V v⟩, }

def map_pis {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  (Π (T : parts_of_loc_const f),
  X.val.obj (op (index_map f T)))
  ⟶ Π (V : parts_of_loc_const (loc_const_on_part W)),
  X.val.obj (op (index_map (loc_const_on_part W) V)) :=
λ φ V, X.val.map (part_of_part_on_part_to_part V).op (φ (part_of_part_on_part V))

lemma naturality_sigmas_pis {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W)) ∘
  X.val.map (map_of_smaller_sigmas W).op =
  map_pis W ∘ Y_of_coproduct_equiv_product X (index_map f) :=
begin
  ext,
  dsimp [Y_of_coproduct_equiv_product, map_of_smaller_sigmas, map_pis],
  simp only [← category_theory.functor_to_types.map_comp_apply, ← op_comp, sigma.ι_desc],
  -- dsimp [part_of_part_on_part_to_part],
  dsimp only [part_on_part_to_sigma_of_parts, part_to_Profinite_map, Profinite_of_to_part_map],
  simp only [category.id_comp],
  congr' 2,
  rw ← iso.cancel_iso_hom_right _ _(Profinite_iso_sigma_of_parts f),
  simp only [category.comp_id, iso.inv_hom_id, category.assoc],
  dsimp [Profinite_iso_sigma_of_parts, Profinite_hom_sigma_of_parts],
  simp only [sigma.ι_desc],
  refl,
end

lemma values_of_parts_eqs {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  {W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))}
  (V : parts_of_loc_const (loc_const_on_part W)) :
  value_of_part V = value_of_part (part_of_part_on_part V) :=
begin
  have h := value_of_part_satisfies_prop (part_of_part_on_part V),
  dsimp [part_of_part_on_part] at *,
  dsimp [part_of_value] at *,
  exact values_eq_of_fibers (value_of_part_on_part_satisfies_prop V) h.2.symm,
end

lemma values_of_parts_eqs' {S : Profinite.{u}} {X Y : Type (u+1)}
  {f : locally_constant S X} {p : X → Y}
  {W : parts_of_loc_const (loc_const_map f p)}
  (V : parts_of_loc_const (loc_const_on_part W)) :
  value_of_part V = value_of_part (part_of_part_on_part V) :=
begin
  have h := value_of_part_satisfies_prop (part_of_part_on_part V),
  dsimp [part_of_part_on_part] at *,
  dsimp [part_of_value] at *,
  exact values_eq_of_fibers (value_of_part_on_part_satisfies_prop V) h.2.symm,
end

lemma map_pis_of_coordinate {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  map_pis W (counit_loc_const_app_coordinate f) = counit_loc_const_app_coordinate
  (loc_const_on_part W) :=
begin
  dsimp [map_pis, counit_loc_const_app_coordinate],
  ext V,
  dsimp [counit_loc_const_app_coordinate],
  simp only [← category_theory.functor_to_types.map_comp_apply, ← op_comp],
  rw Profinite_comp_punit_elim _,
  congr' 1,
  exact (values_of_parts_eqs V).symm,
end .

lemma naturality_sigmas_pis_rearrange {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  map_pis W = Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W)) ∘
  X.val.map (map_of_smaller_sigmas W).op ∘ (Y_of_coproduct_equiv_product X (index_map f)).symm :=
begin
  rw ← function.comp.assoc,
  rw naturality_sigmas_pis W,
  rw function.comp.assoc,
  simp only [equiv.self_comp_symm, eq_self_iff_true, function.comp.right_id],
end

lemma naturality_sigmas_pis_rearrange_apply {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  ∀ x, map_pis W x = Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W))
  (X.val.map (map_of_smaller_sigmas W).op
  ((Y_of_coproduct_equiv_product X (index_map f)).symm x)) :=
begin
  intro x,
  rw ← function.comp_app (X.val.map (map_of_smaller_sigmas W).op)
    (Y_of_coproduct_equiv_product X (index_map f)).symm x,
  rw ← function.comp_app (Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W)))
    ((X.val.map (map_of_smaller_sigmas W).op) ∘
    (Y_of_coproduct_equiv_product X (index_map f)).symm) x,
  exact congr_fun (naturality_sigmas_pis_rearrange W) x,
end

lemma naturality_sigmas_pis_rearrange_apply₂ {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  ∀ x, (Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W))).symm (map_pis W x) =
  X.val.map (map_of_smaller_sigmas W).op
  ((Y_of_coproduct_equiv_product X (index_map f)).symm x) :=
begin
  intro x,
  apply_fun (Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W))),
  simp only [equiv.apply_symm_apply],
  exact naturality_sigmas_pis_rearrange_apply W x,
end

def prodXY_map {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  (Π (V : parts_of_loc_const (loc_const_on_part W)),
  X.val.obj (op (index_map (loc_const_on_part W) V))) ⟶
  Π (V : parts_of_loc_const (loc_const_on_part W)),
  Y.val.obj (op (index_map (loc_const_on_part W) V)) :=
λ φ V, p.val.app _ (φ V)

lemma prodXY_naturality {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) :
  prodXY_map W ∘ Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W)) =
  Y_of_coproduct_equiv_product Y (index_map (loc_const_on_part W)) ∘ p.val.app _ :=
begin
  ext,
  dsimp [Y_of_coproduct_equiv_product, prodXY_map],
  rw functor_to_types.naturality,
end

lemma prodXY_naturality_apply {S : Profinite.{u}} {X Y : CondensedSet.{u}}
  {f : locally_constant S (X.val.obj (op point))} {p : X ⟶ Y}
  (W : parts_of_loc_const (loc_const_map f (p.val.app (op point)))) : ∀ x,
  prodXY_map W (Y_of_coproduct_equiv_product X (index_map (loc_const_on_part W)) x) =
  Y_of_coproduct_equiv_product Y (index_map (loc_const_on_part W)) (p.val.app _ x) :=
begin
  intro x,
  exact congr_fun (prodXY_naturality W) x,
end

lemma value_of_part_eq_p_of_value_of_part_on_part {S : Profinite.{u}} {X Y : Type (u+1)}
  {f : locally_constant S X} {p : X → Y}
  {W : parts_of_loc_const (loc_const_map f p)}
  (V : parts_of_loc_const (loc_const_on_part W)) :
  value_of_part W = p (value_of_part V) :=
begin
  have hW := value_of_part_satisfies_prop W,
  dsimp [loc_const_map, finset_range_of_loc_const] at hW,
  have hV := value_of_part_satisfies_prop V,
  dsimp [loc_const_on_part, finset_range_of_loc_const] at hV,
  simp only [set.mem_range, set.mem_to_finset] at hV,
  obtain ⟨w, hw⟩ := hV.1,
  rw ← hw,
  cases w,
  rw ← hW.2 at w_property,
  have : (p ∘ f) w_val = value_of_part W := w_property,
  rw ← this,
  refl,
end

def counit_loc_const : CondensedSet.evaluation point ⋙ loc_const_Condensed_functor.{u} ⟶
  𝟭 CondensedSet.{u} :=
{ app := counit_loc_const_app,
  naturality' :=
  begin
    intros X Y p,
    dsimp [counit_loc_const_app, counit_loc_const_app_app],
    ext S f,
    dsimp [CondensedSet.evaluation, loc_const_Condensed_functor] at *,
    dsimp [loc_const_CondensedSet, loc_const_presheaf] at f,
    let g := (Y_of_coproduct_equiv_product X (index_map f)).symm
      (counit_loc_const_app_coordinate f),
    change (Y_of_coproduct_equiv_product X (index_map f)).symm
      (counit_loc_const_app_coordinate f) with g,
    rw category_theory.functor_to_types.naturality,
    rw inv_op_eq_op_inv (Profinite_iso_sigma_of_parts _),
    rw inv_op_eq_op_inv (Profinite_iso_sigma_of_parts f),
    simp only [← functor.map_iso_inv],
    rw ← Profinite_iso_factorisation _ _,
    apply_fun (Y.val.map_iso (Profinite_iso_sigma_of_parts f).op).hom using
      Y_val_iso_hom_injective _ _,
    rw iso_trans_op _ _,
    simp only [functor.map_iso_trans, iso.op_hom,
      functor.map_iso_inv, iso.trans_inv,
      types_comp_apply, iso.op_inv,
      functor.map_iso_hom],
    congr,
    rw inv_op_eq_op_inv (map_sigmas_iso f _),
    simp only [← functor.map_iso_inv],
    apply_fun (Y.val.map_iso (map_sigmas_iso f (p.val.app (op point))).op).hom using
      Y_val_iso_hom_injective _ _,
    simp only [category_theory.inv_hom_id_apply],
    simp only [category_theory.iso.op_hom, category_theory.functor.map_iso_hom],
    apply_fun Y_of_coproduct_equiv_product Y
      (index_map (loc_const_map f (p.val.app (op point)))),
    simp only [equiv.apply_symm_apply],
    dsimp [Y_of_coproduct_equiv_product],
    ext W,
    dsimp [map_sigmas_iso],
    simp only [← category_theory.functor_to_types.map_comp_apply, ← op_comp],
    dsimp only [map_sigmas],
    simp only [sigma.ι_desc],
    dsimp only [map_for_sigmas, map_of_smaller_sigmas, part_to_Profinite_of_map],
    simp only [category.id_comp, category.assoc],
    have : (sigma.desc (index_map (loc_const_on_part W))
      (part_on_part_to_sigma_of_parts W)) = map_of_smaller_sigmas W := by refl,
    rw this,
    clear this,
    dsimp [counit_loc_const_app_coordinate],
    rw inv_op_eq_op_inv (Profinite_iso_sigma_of_parts _),
    simp only [category_theory.functor_to_types.map_comp_apply],
    apply_fun (Y.val.map_iso (Profinite_iso_sigma_of_parts (loc_const_on_part W)).op).hom using
      Y_val_iso_hom_injective _ _,
    simp only [← functor.map_iso_inv],
    simp only [category_theory.inv_hom_id_apply],
    simp only [category_theory.iso.op_hom, category_theory.functor.map_iso_hom],
    simp only [← category_theory.functor_to_types.map_comp_apply, ← op_comp],
    rw Profinite_comp_punit_elim _,
    change g with (Y_of_coproduct_equiv_product X (index_map f)).symm
      (counit_loc_const_app_coordinate f),
    rw ← category_theory.functor_to_types.naturality,
    rw ←  naturality_sigmas_pis_rearrange_apply₂ W (counit_loc_const_app_coordinate f),
    rw map_pis_of_coordinate W,
    apply_fun Y_of_coproduct_equiv_product Y (index_map (loc_const_on_part W)),
    rw ← prodXY_naturality_apply W _,
    simp only [equiv.apply_symm_apply],
    ext V,
    dsimp [Y_of_coproduct_equiv_product],
    simp only [← category_theory.functor_to_types.map_comp_apply, ← op_comp],
    rw Profinite_comp_punit_elim _,
    dsimp [prodXY_map, counit_loc_const_app_coordinate],
    rw functor_to_types.naturality,
    congr,
    exact value_of_part_eq_p_of_value_of_part_on_part V,
  end } .

def unit_loc_const : 𝟭 (Type (u+1)) ⟶ loc_const_Condensed_functor ⋙
  CondensedSet.evaluation point :=
{ app := λ X x, { to_fun := function.const point x,
    is_locally_constant := is_locally_constant.const x }, }

def unit_loc_const_inv : loc_const_Condensed_functor ⋙ CondensedSet.evaluation point ⟶
  𝟭 (Type (u+1)) :=
{ app := λ X f, f.to_fun (punit.star), }

def unit_loc_const_iso : 𝟭 (Type (u+1)) ≅ loc_const_Condensed_functor ⋙
  CondensedSet.evaluation point :=
{ hom := unit_loc_const,
  inv := unit_loc_const_inv,
  hom_inv_id' :=
  begin
    ext X x,
    dsimp at *,
    refl,
  end,
  inv_hom_id' :=
  begin
    ext X f x,
    dsimp at *,
    have : x = punit.star := punit_eq_star x,
    rw this,
    refl,
  end } .

instance unit_loc_const_is_iso : is_iso unit_loc_const :=
is_iso.of_iso unit_loc_const_iso

lemma Profinite_inv_hom_iso_lemma {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X) :
  ∀ x, (Profinite_iso_sigma_of_parts f).inv ((Profinite_iso_sigma_of_parts f).hom x) = x :=
begin
  intro x,
  simp only [← category_theory.comp_apply],
  simp only [Profinite.coe_id, id.def, category_theory.iso.hom_inv_id, eq_self_iff_true],
end

lemma loc_const_map_unit {S : Profinite.{u}} {X : Type (u+1)} (f : locally_constant S X) (s : S)
  : ((loc_const_map f (unit_loc_const.app X)) s).to_fun (punit.star : point) = f s :=
by refl

lemma injective_comp_iso {S T : Profinite.{u}} {X : Type (u+1)} (i : T ≅ S) :
  function.injective (λ (f : S → X), f ∘ i.hom) :=
begin
  refine function.bijective.injective _,
  rw function.bijective_iff_has_inverse,
  use λ g, g ∘ i.inv,
  split,
  { intro a,
    ext,
    dsimp,
    simp only [← category_theory.comp_apply, Profinite.coe_id, id.def,
      iso.inv_hom_id], },
  intro a,
  ext,
  dsimp,
  simp only [← category_theory.comp_apply, Profinite.coe_id, id.def,
    iso.hom_inv_id],
end

lemma Profinite_iso_comp_assoc {S T : Profinite} {X : Type (u+1)} (i : S ≅ T) (f : S → X) :
  (f ∘ i.inv) ∘ i.hom = f :=
begin
  ext,
  dsimp,
  simp only [← category_theory.comp_apply, Profinite.coe_id, id.def, iso.hom_inv_id],
end

lemma left_triangle_lemma₁ {α : Type u} (X : CondensedSet.{u}) [fintype α]
  (S : α → Profinite.{u}) (a : α) : ∀ φ, X.val.map (sigma.ι S a).op
  ((Y_of_coproduct_equiv_product X S).symm φ) = φ a :=
begin
  intro φ,
  obtain ⟨x, h⟩ := equiv.surjective (Y_of_coproduct_equiv_product X S) φ,
  rw ← h,
  simp only [equiv.symm_apply_apply],
  refl,
end

lemma left_triangle_lemma₂ {S : Profinite.{u}ᵒᵖ} {X : Type (u+1)}
  {f : (loc_const_Condensed_functor.obj X).val.obj S}
  (W : (parts_of_loc_const (loc_const_map f (unit_loc_const.app X)))) :
  ∀ g x, ((loc_const_Condensed_functor.obj X).val.map
  (sigma.ι (index_map (loc_const_map f (unit_loc_const.app X))) W).op g).to_fun x =
  g.to_fun ((sigma.ι (index_map (loc_const_map f (unit_loc_const.app X))) W) x) :=
begin
  intros g x,
  dsimp [loc_const_Condensed_functor, loc_const_CondensedSet, loc_const_presheaf],
  rw locally_constant.coe_comap _ _ (sigma.ι _ _).continuous,
end

lemma left_triangle_lemma₃ {S : Profinite.{u}ᵒᵖ} {X : Type (u+1)}
  {f : (loc_const_Condensed_functor.obj X).val.obj S}
  (W : (parts_of_loc_const (loc_const_map f (unit_loc_const.app X))))
  (y : unop (op point)) (xs : W) : (value_of_part W).to_fun y = f.to_fun xs.val :=
begin
  have := value_of_part_satisfies_prop W,
  dsimp [loc_const_map] at *,
  cases xs,
  rw ← this.2 at xs_property,
  have h : ((unit_loc_const.app X) ∘ f.to_fun) xs_val = value_of_part W := xs_property,
  dsimp [unit_loc_const] at h,
  rw ← h,
  dsimp,
  refl,
end .

lemma left_triangle_lemma {S : Profinite.{u}ᵒᵖ} {X : Type (u+1)}
  (f : (loc_const_Condensed_functor.obj X).val.obj S) :
  (counit_loc_const.app (loc_const_Condensed_functor.obj X)).val.app S
  ((loc_const_Condensed_functor.map (unit_loc_const.app X)).val.app S f) = f :=
begin
    let Y := loc_const_Condensed_functor.obj X,
    change loc_const_Condensed_functor.obj X with Y,
    dsimp [loc_const_Condensed_functor], --, loc_const_CondensedSet, loc_const_presheaf],
    dsimp [counit_loc_const, counit_loc_const_app, counit_loc_const_app_app],
    dsimp [loc_const_Condensed_functor, loc_const_CondensedSet, loc_const_presheaf] at *,
    rw ← locally_constant.coe_inj,
    rw locally_constant.coe_comap _ _ (Profinite_iso_sigma_of_parts _).inv.continuous,
    apply_fun λ g, g ∘ (Profinite_iso_sigma_of_parts (loc_const_map f (unit_loc_const.app X))).hom
      using injective_comp_iso (Profinite_iso_sigma_of_parts _),
    dsimp,
    rw Profinite_iso_comp_assoc (Profinite_iso_sigma_of_parts _) _,
    ext s,
    obtain ⟨W, xs, hs⟩ := sigma.ι_jointly_surjective
      (index_map ((loc_const_map f (unit_loc_const.app X)))) s,
    rw ← hs,
    dsimp [Profinite_iso_sigma_of_parts, Profinite_hom_sigma_of_parts],
    simp only [← category_theory.comp_apply, sigma.ι_desc],
    have := left_triangle_lemma₂ W,
    dsimp at this,
    rw ← this _ xs,
    have h := left_triangle_lemma₁ Y (index_map (loc_const_map f (unit_loc_const.app X))) W,
    change loc_const_Condensed_functor.obj X with Y,
    rw h (counit_loc_const_app_coordinate (loc_const_map f (unit_loc_const.app X))),
    dsimp [counit_loc_const_app_coordinate, loc_const_map, unit_loc_const],
    dsimp [loc_const_Condensed_functor, loc_const_CondensedSet, loc_const_presheaf],
    rw locally_constant.coe_comap _ _ (punit.elim _).continuous,
    dsimp,
    have h' := left_triangle_lemma₃ W (punit.elim (of W) xs) xs,
    dsimp at h',
    exact h',
end .

def loc_const_const (S : Profinite.{u}) {X : Type (u+1)} (x : X) : locally_constant S X :=
{ to_fun := function.const S x,
  is_locally_constant := is_locally_constant.const x }

lemma loc_const_from_point_is_const {X : Type (u+1)} (f : locally_constant point X) :
  f = loc_const_const point (f punit.star) :=
begin
  ext,
  rw punit_eq_star x,
  dsimp [loc_const_const],
  refl,
end

lemma parts_of_loc_const_const {S : Profinite.{u}} [inhabited S] {X : Type (u+1)} (x : X) :
  parts_of_loc_const (loc_const_const S x) = {set.univ} :=
begin
  ext,
  dsimp [parts_of_loc_const, finset_range_of_loc_const],
  simp only [set.mem_image, set.mem_to_finset, exists_exists_eq_and,
    finset.mem_singleton, set.coe_to_finset],
  split,
  { intro h,
    obtain ⟨y, hy⟩ := h,
    obtain ⟨s, hs⟩ := hy.1,
    dsimp [loc_const_const] at hs,
    rw ← hs at hy,
    rw ← hy.2,
    refine set.eq_univ_of_subset _ rfl,
    intros z hz,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    refl },
  intro ha,
  use x,
  split,
  { use _inst_1.default,
    refl },
  rw ha,
  refine set.eq_univ_of_subset _ ha,
  intros s hs,
  simp only [set.mem_preimage, set.mem_singleton_iff],
  refl,
end

instance subsingleton_parts_of_const {S : Profinite.{u}} [inhabited S] {X : Type (u+1)} (x : X) :
  subsingleton (parts_of_loc_const (loc_const_const S x)) :=
begin
  rw subsingleton_iff,
  intros W T,
  cases W,
  cases T,
  rw parts_of_loc_const_const at W_property,
  rw parts_of_loc_const_const at T_property,
  ext,
  dsimp,
  simp only [finset.mem_singleton] at W_property,
  simp only [finset.mem_singleton] at T_property,
  rw W_property,
  rw T_property,
end

lemma set_univ_mem_parts_of_loc_const_const {S : Profinite.{u}} [inhabited S] {X : Type (u+1)}
  (x : X) : set.univ ∈ parts_of_loc_const (loc_const_const S x) :=
begin
  rw parts_of_loc_const_const,
  simp only [finset.mem_singleton],
end

def set_univ_as_parts_of_loc_const_const {S : Profinite.{u}} [inhabited S] {X : Type (u+1)}
  (x : X) : parts_of_loc_const (loc_const_const S x) :=
⟨set.univ, set_univ_mem_parts_of_loc_const_const x⟩

instance unique_parts_of_const {S : Profinite.{u}} [inhabited S] {X : Type (u+1)} (x : X) :
  unique (parts_of_loc_const (loc_const_const S x)) :=
unique_of_subsingleton (set_univ_as_parts_of_loc_const_const x)

instance : inhabited point := { default := punit.star }

instance unique_parts_of_const_point {X : Type (u+1)} (x : X) :
  unique (parts_of_loc_const (loc_const_const point x)) :=
unique_parts_of_const x

def unique_to_pi {α : Type*} [unique α] (f : α → Type*) :
  f default → (Π (a : α), f a) := λ x a,
begin
  rw unique.eq_default a,
  exact x,
end

def sigma_to_unique {α : Type*} [unique α] (f : α → Type*) :
  (Σ (a : α), f a) → f default :=
begin
  intro h,
  obtain ⟨a, ha⟩ := h,
  rw unique.default_eq a,
  exact ha,
end

lemma Profinite_eq_default {α : Type u} [fintype α] [unique α]
  (S : α → Profinite.{u}) (a : α) : S a = S default :=
begin
  rw unique.default_eq a,
end

def Profinite_to_default {α : Type u} [fintype α] [unique α]
  (S : α → Profinite.{u}) (a : α) : S a ⟶ S default :=
eq_to_hom (Profinite_eq_default S a)

def Profinite_sigma_to_default {α : Type u} [fintype α] [unique α]
  (S : α → Profinite.{u}) : Profinite.sigma S ⟶ S default :=
sigma.desc S (Profinite_to_default S)

lemma sigma_ι_bijective_unique {α : Type u} [fintype α] [unique α]
  (S : α → Profinite.{u}) : function.bijective (sigma.ι S default) :=
begin
  split,
  exact sigma.ι_injective _ _,
  intro s,
  obtain ⟨a, h⟩ := sigma.ι_jointly_surjective S s,
  have := unique.eq_default a,
  subst this,
  exact h,
end

def sigma_iso_default  {α : Type u} [fintype α] [unique α]
  (S : α → Profinite.{u}) : Profinite.sigma S ≅ S default :=
{ hom := Profinite_sigma_to_default S,
  inv := sigma.ι S default,
  hom_inv_id' :=
  begin
    dsimp [Profinite_sigma_to_default],
    ext1 s,
    dsimp,
    obtain ⟨s', h⟩ := (sigma_ι_bijective_unique S).surjective s,
    rw ← h,
    rw function.injective.eq_iff (sigma.ι_injective S default),
    simp only [← category_theory.comp_apply, sigma.ι_desc],
    refl,
  end,
  inv_hom_id' :=
  begin
    dsimp [Profinite_sigma_to_default],
    simp only [Profinite.sigma.ι_desc],
    dsimp [Profinite_to_default],
    refl,
  end
}

lemma prod_symm_map_eq_proj {X : CondensedSet.{u}} (x : X.val.obj (op point)) :
  ∀ φ, (X.val.map (sigma.ι (index_map (loc_const_const point x)) default).op)
  ((Y_of_coproduct_equiv_product X (index_map (loc_const_const point x))).symm φ) =
  φ default :=
begin
  intro φ,
  obtain ⟨y, h⟩ := (Y_of_coproduct_equiv_product X _).surjective φ,
  rw ← h,
  simp only [equiv.symm_apply_apply],
  dsimp [Y_of_coproduct_equiv_product],
  refl,
end

lemma value_of_part_default {X : CondensedSet.{u}}
  (f : locally_constant point (X.val.obj (op point))) :
  @value_of_part point _ (loc_const_const point (f punit.star)) default = f punit.star :=
begin
  have := (@value_of_part_satisfies_prop point _ (loc_const_const point (f punit.star)) default),
  dsimp [finset_range_of_loc_const] at this,
  simp only [set.mem_range, set.mem_to_finset] at this,
  obtain ⟨y, h⟩ := this.1,
  rw ← h,
  refl,
end

lemma right_triangle_lemma {X : CondensedSet.{u}}
  (f : locally_constant point (X.val.obj (op point))) :
  (counit_loc_const.app X).val.app (op point) f = f punit.star :=
begin
  dsimp [counit_loc_const, counit_loc_const_app, counit_loc_const_app_app],
  apply_fun (X.val.map_iso (Profinite_iso_sigma_of_parts f).op).hom using
    Y_val_iso_hom_injective _ _,
  dsimp,
  simp only [← functor_to_types.map_comp_apply, ← op_comp],
  simp only [category_theory.iso.hom_inv_id,
    category_theory.functor_to_types.map_id_apply,
    category_theory.op_id],
  rw loc_const_from_point_is_const f,
  apply_fun (X.val.map_iso (sigma_iso_default (index_map (loc_const_const point
    (f punit.star)))).op).inv using Y_val_iso_inv_injective _ _,
  dsimp [sigma_iso_default],
  rw prod_symm_map_eq_proj _,
  dsimp [Profinite_iso_sigma_of_parts, Profinite_hom_sigma_of_parts],
  simp only [← functor_to_types.map_comp_apply, ← op_comp, sigma.ι_desc],
  dsimp [counit_loc_const_app_coordinate, loc_const_const],
  congr,
  { ext },
  exact value_of_part_default f,
end .

def loc_const_adjunction : loc_const_Condensed_functor ⊣ CondensedSet.evaluation point :=
adjunction.mk_of_unit_counit
{ unit := unit_loc_const,
  counit := counit_loc_const,
  left_triangle' :=
  begin
    ext X S f : 6,
    dsimp at *,
    exact left_triangle_lemma f,
  end,
  right_triangle' :=
  begin
    ext X : 2,
    dsimp,
    simp only [category_theory.category.id_comp],
    have h :=  (unit_loc_const_iso.app (X.val.obj (op point))).hom_inv_id',
    dsimp at h,
    rw ← h,
    dsimp [unit_loc_const_iso],
    congr,
    ext f,
    dsimp [unit_loc_const_inv],
    dsimp [loc_const_Condensed_functor, loc_const_CondensedSet, loc_const_presheaf] at f,
    exact right_triangle_lemma f,
  end } .
