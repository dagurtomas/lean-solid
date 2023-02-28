import category_theory.limits.kan_extension
import category_theory.filtered
import condensed.basic
import solid.dq_sa_comparison
import for_mathlib.Profinite.product

noncomputable theory

universes u

open category_theory
open Profinite
open opposite
open Fintype

def fintype_profinite_equiv (X : Fintype) : X ≃ to_Profinite.obj X :=
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  left_inv := by tauto,
  right_inv := by tauto, }

def fintype_profinite_to_CompHaus_Top_equiv (X : Fintype) :
  X ≃ (to_Profinite.obj X).to_CompHaus.to_Top :=
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  left_inv := by tauto,
  right_inv := by tauto, }

def Profinite_to_CompHaus_Top_equiv (X : Profinite) :
  X ≃ X.to_CompHaus.to_Top :=
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  left_inv := by tauto,
  right_inv := by tauto, }

def fintype_profinite_prod_equiv (X Y : Fintype) :
  X × Y ≃ (to_Profinite.obj X) × (to_Profinite.obj Y) :=
{ to_fun := prod.map (fintype_profinite_equiv X).to_fun  (fintype_profinite_equiv Y).to_fun,
  inv_fun := prod.map (fintype_profinite_equiv X).inv_fun  (fintype_profinite_equiv Y).inv_fun,
  left_inv :=
  begin
    apply function.left_inverse.prod_map,
    exact (fintype_profinite_equiv X).left_inv,
    exact (fintype_profinite_equiv Y).left_inv,
  end,
  right_inv :=
  begin
    apply function.right_inverse.prod_map,
    exact (fintype_profinite_equiv X).right_inv,
    exact (fintype_profinite_equiv Y).right_inv,
  end }

def Profinite_coe_equiv (X Y : Fintype) :
  ↥(limits.prod (to_Profinite.obj X) (to_Profinite.obj Y)) ≃
  ↥(to_Profinite.obj X) × ↥(to_Profinite.obj Y) :=
(Profinite.homeo_of_iso (Profinite.prod_iso _ _)).to_equiv

open category_theory.limits

local attribute [instance] Fintype_bot_topology

local attribute [instance] Fintype_discrete_topology

set_option pp.universes true

instance (S : Profinite.{u}ᵒᵖ) : has_colimits_of_shape
  (costructured_arrow to_Profinite.op S) (Type (u+1)) :=
begin
  haveI : has_colimits_of_size.{u+1} (Type (u+1)) := by apply_instance,
  haveI : has_colimits_of_size.{u u+1} (Type (u+1)) :=
    has_colimits_of_size_shrink.{u u+1 u+1 u+1} (Type (u+1)),
  exact has_colimits_of_size.has_colimits_of_shape (costructured_arrow to_Profinite.op S),
end

set_option pp.universes false

def colim_as_Kan_extension (X : Type (u+1)) : Profinite.{u}ᵒᵖ ⥤ Type (u+1) :=
  (Lan to_Profinite.op).obj (Fintype.incl.op ⋙ ulift_functor.{u+1}.op ⋙ (yoneda.obj X))

instance discrete_quotient_cofiltered (S : Profinite.{u}) :
  is_cofiltered (discrete_quotient S) := by fsplit

instance discrete_quotient_op_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (discrete_quotient S.unop)ᵒᵖ := by apply_instance

instance structured_arrow_inhabited (S : Profinite.{u}) :
  inhabited (structured_arrow S to_Profinite) :=
{ default := (dq_sa_functor S).obj ⊤ }

instance : full to_Profinite.{u} := by constructor

instance : faithful to_Profinite.{u} := by constructor

instance : reflects_limits to_Profinite.{u} := fully_faithful_reflects_limits _

instance : Π (Y : Fintype), unique (Y ⟶ (Fintype.of punit)) := λ Y,
{ to_inhabited := { default := λ y, punit.star, },
  uniq := λ f, (by ext), }

lemma is_terminal_Fintype_punit : is_terminal (Fintype.of punit) :=
  is_terminal.of_unique _

instance : has_terminal Fintype :=
  has_terminal_of_unique (Fintype.of punit)

instance unique_punit_Profinite : Π (Y : Profinite.{u}), unique (Y ⟶ (Profinite.of punit)) := λ Y,
{ to_inhabited := { default := ⟨λ y, punit.star, (by continuity)⟩ },
  uniq := λ f, (by ext), }

lemma is_terminal_Profinite_punit : is_terminal (Profinite.of punit) :=
  is_terminal.of_unique _

def limit_cone_pair (X Y : Fintype) : cone (pair X Y) :=
{ X := Fintype.of (X × Y),
  π := discrete.nat_trans (λ W,
    begin
      cases W,
      cases W,
      exact λ a, a.1,
      exact λ a, a.2,
    end), }

def is_limit_cone_pair (X Y : Fintype) : is_limit (limit_cone_pair X Y) :=
{ lift := λ s a,
  { fst := s.π.app { as := walking_pair.left } a,
    snd := s.π.app { as := walking_pair.right } a},
  fac' :=
  begin
    intros s j,
    cases j,
    cases j,
    refl,
    refl,
  end,
  uniq' :=
  begin
    intros s m h,
    have hl := h { as := walking_pair.left },
    have hr := h { as := walking_pair.right },
    dsimp at *,
    ext,
    dsimp,
    rw ← hl,
    refl,
    dsimp,
    rw ← hr,
    refl,
  end, }

instance has_limit_pair (X Y : Fintype) : has_limit (pair X Y) :=
begin
  use limit_cone_pair X Y,
  exact is_limit_cone_pair X Y,
end

instance hbp_Fintype : has_binary_products Fintype :=
  @has_binary_products_of_has_limit_pair _ _ has_limit_pair

instance dec_eq_fintype {X Y : Fintype} (f g : X ⟶ Y) :
  decidable_pred (λ (_x : X), _x ∈ {a : X | f a = g a}) :=
classical.dec_pred (λ (_x : X), _x ∈ {a : X | f a = g a})

instance equalizer_fintype {X Y : Fintype} (f g : X ⟶ Y) :
  fintype {a : X | f a = g a} := @set_fintype _ _ _ (dec_eq_fintype f g)

def equalizer_as_Fintype {X Y : Fintype} (f g : X ⟶ Y) : Fintype :=
  @Fintype.of {a : X | f a = g a} (equalizer_fintype f g)

def limit_cone_parallel_pair {X Y : Fintype} (f g : X ⟶ Y) : cone (parallel_pair f g) :=
{ X := equalizer_as_Fintype f g,
  π :=
  { app := λ W,
    begin
      cases W,
      exact λ x, x.val,
      exact λ x, f x.val,
    end,
    naturality' :=
    begin
      intros W₁ W₂ p,
      dsimp,
      cases p,
      { refl },
      { simp only [category_theory.category.id_comp,
          category_theory.limits.parallel_pair_map_right],
        ext,
        have hx : f x.val = g x.val := x.prop,
        unfold_coes,
        rw hx,
        refl, },
      { refl, },
    end } }

lemma lands_in_equalizer {X Y : Fintype} {f g : X ⟶ Y} {s : cone (parallel_pair f g)} (a : s.X.α) :
  f (s.π.app walking_parallel_pair.zero a) = g (s.π.app walking_parallel_pair.zero a) :=
begin
  cases s,
  cases s_π,
  dsimp,
  let h0 := s_π_app walking_parallel_pair.zero,
  dsimp at h0,
  let h1 := s_π_app walking_parallel_pair.one,
  dsimp at h1,
  let h2 := s_π_naturality' walking_parallel_pair_hom.left,
  dsimp at h2,
  let h3 := s_π_naturality' walking_parallel_pair_hom.right,
  dsimp at h3,
  rw h3 at h2,
  change (s_π_app walking_parallel_pair.zero) with h0 at h2,
  change (s_π_app walking_parallel_pair.zero) with h0,
  change f (h0 a) with (h0 ≫ f) a,
  change g (h0 a) with (h0 ≫ g) a,
  rw h2,
end

def is_limit_cone_parallel_pair {X Y : Fintype} (f g : X ⟶ Y) :
  is_limit (limit_cone_parallel_pair  f g) :=
{ lift := λ s a, ⟨s.π.app walking_parallel_pair.zero a, lands_in_equalizer a⟩,
  fac' :=
  begin
    intros s j,
    cases j,
    refl,
    dsimp,
    simp only [category_theory.limits.fork.condition,
      category_theory.limits.fork.app_one_eq_ι_comp_left],
    refl,
  end,
  uniq' :=
  begin
    intros s m h,
    have h0 := h walking_parallel_pair.zero,
    ext,
    simp only [subtype.coe_mk],
    rw ← h0,
    refl,
  end, }

instance has_limit_parallel_pair {X Y : Fintype} (f g : X ⟶ Y) : has_limit (parallel_pair f g) :=
begin
  use limit_cone_parallel_pair f g,
  exact is_limit_cone_parallel_pair f g,
end

instance he_Fintype : has_equalizers Fintype := has_equalizers_of_has_limit_parallel_pair _

instance hpb_Fintype : has_pullbacks Fintype :=
  @has_pullbacks_of_has_binary_products_of_has_equalizers _ _ hbp_Fintype he_Fintype

instance hpb_Fintype_u : has_pullbacks Fintype.{u} := hpb_Fintype.{u u}

instance fin_lim_Fintype : has_finite_limits Fintype :=
  @has_finite_limits_of_has_terminal_and_pullbacks _ _ _ hpb_Fintype

instance fin_lim_Fintype_u : has_finite_limits Fintype.{u} := fin_lim_Fintype.{u u}

-- prod.map_left_inverse.mpr ⟨(fintype_profinite_equiv X).left_inv,
-- (fintype_profinite_equiv Y).left_inv⟩,

lemma fintype_map_profinite_eq1 {X Y : Fintype} (f : X ⟶ Y) : f = to_Profinite.map f :=
  by { ext, refl }

lemma fintype_map_profinite_eq2 {X Y : Fintype} (f : to_Profinite.obj X ⟶ to_Profinite.obj Y) :
  f = to_Profinite.map f.to_fun :=
  by { ext, refl }

lemma fintype_map_profinite_eq3 {X Y : Fintype} (f : X ⟶ Y) :
  to_Profinite.map f = ⟨f, (continuous_bot : continuous f)⟩ :=
by { ext, refl }

instance pt_to_Profinite : is_iso (terminal_comparison to_Profinite.{u}) :=
begin
  let iso_punit : ⊤_ Fintype ≅ Fintype.of punit :=
    terminal_iso_is_terminal is_terminal_Fintype_punit,
  let iso_punit_Profinite : ⊤_ Profinite.{u} ≅ Profinite.of punit :=
    terminal_iso_is_terminal is_terminal_Profinite_punit,
  apply Profinite.is_iso_of_bijective,
  split,
  { intros a b h,
    dsimp at *,
    suffices : (fintype_profinite_equiv _).inv_fun a = (fintype_profinite_equiv _).inv_fun b,
    { apply_fun (fintype_profinite_equiv _).to_fun at this,
      assumption },
    apply_fun iso_punit.hom,
    { rw punit_eq_star (iso_punit.hom _),
      rw punit_eq_star (iso_punit.hom _) },
    { exact (equiv.injective (Fintype.equiv_equiv_iso.inv_fun iso_punit)) } },
  intro a,
  use (fintype_profinite_equiv _).to_fun (iso_punit.inv punit.star),
  apply_fun iso_punit_Profinite.hom,
  { rw punit_eq_star (iso_punit_Profinite.hom _),
    rw punit_eq_star (iso_punit_Profinite.hom _) },
  exact (homeo_of_iso _).injective,
end

instance : preserves_limit (functor.empty Fintype) to_Profinite.{u} :=
  preserves_terminal.of_iso_comparison to_Profinite.{u}

instance pldp_to_Profinite : preserves_limits_of_shape (discrete pempty) to_Profinite.{u} :=
  preserves_limits_of_shape_pempty_of_preserves_terminal to_Profinite.{u}

instance bp_to_Profinite (X Y : Fintype) : is_iso (prod_comparison to_Profinite.{u} X Y) :=
begin
  unfold prod_comparison,
  apply Profinite.is_iso_of_bijective,
  split,
  { intros a b h,
    type_check prod.lift (to_Profinite.map limits.prod.fst) (to_Profinite.map limits.prod.snd) a,
    type_check a,
    rw fintype_map_profinite_eq3 at h,
    rw fintype_map_profinite_eq3 at h,
    apply_fun (Profinite_to_CompHaus_Top_equiv _).inv_fun at h,
    apply_fun (Profinite_coe_equiv.{u u} X Y).to_fun at h,
    apply_fun (fintype_profinite_prod_equiv X Y).inv_fun at h,
    dsimp at *,
    sorry,
    -- dsimp at *,
    -- unfold_coes at *,
    -- have : is_iso (limits.prod.lift (fintype_profinite_equiv X).to_fun (fintype_profinite_equiv Y).to_fun),
    -- rw prod.ext_iff,
     },
  sorry,
  -- have : category_theory.limits.prod X Y = to_Profinite.obj (prod X Y),
  -- have h : (((prod_comparison to_Profinite X Y) a) : to_Profinite.obj (X × Y)).fst = a.fst,
  -- have h' := ((prod.lift (to_Profinite.map prod.fst) (to_Profinite.map prod.snd)) a).fst = a.fst,
  -- unfold_coes at h,
end

instance pl_pair_to_Profinite (X Y : Fintype) :
  preserves_limit (pair X Y) to_Profinite.{u} :=
preserves_limit_pair.of_iso_prod_comparison _ X Y

instance plbp_to_Profinite : preserves_limits_of_shape (discrete walking_pair) to_Profinite.{u} :=
{ preserves_limit := λ K, preserves_limit_of_iso_diagram _ (diagram_iso_pair _).symm, }

instance pfp_to_Profinite (J : Type) [fintype J] :
  preserves_limits_of_shape (discrete J) to_Profinite.{u} :=
preserves_finite_products_of_preserves_binary_and_terminal _ J

instance pp_to_Profinite {X Y : Fintype} (f g : X ⟶ Y) :
  is_iso (equalizer_comparison f g to_Profinite) := sorry

instance pl_parallel_pair_to_Profinite {X Y : Fintype} (f g : X ⟶ Y) :
  preserves_limit (parallel_pair f g) to_Profinite.{u} :=
preserves_equalizer.of_iso_comparison _ _ _

instance plpp_to_Profinite : preserves_limits_of_shape walking_parallel_pair to_Profinite.{u} :=
{ preserves_limit := λ K, preserves_limit_of_iso_diagram _ (diagram_iso_parallel_pair _).symm, }

instance pres_fin_lim_to_Profinite : preserves_finite_limits to_Profinite.{u} :=
  @preserves_finite_limits_of_preserves_equalizers_and_finite_products _ _ _ _ _ _
  to_Profinite.{u} _ pfp_to_Profinite

  -- _terminal_and_pullbacks to_Profinite.{u}

instance structured_arrow_cofiltered (S : Profinite) :
  is_cofiltered (structured_arrow S to_Profinite) :=
(@flat_of_preserves_finite_limits _ _ _ _
  fin_lim_Fintype to_Profinite pres_fin_lim_to_Profinite).cofiltered S

instance structured_arrow_cofiltered_u (S : Profinite.{u}) :
  is_cofiltered (structured_arrow S to_Profinite) :=
structured_arrow_cofiltered.{u u} S

instance costructured_arrow_filtered (S : Profiniteᵒᵖ) :
  is_filtered (costructured_arrow to_Profinite.op S) :=
@is_filtered.of_equivalence _ _
  (@category_theory.is_filtered_op_of_is_cofiltered _ _
  (structured_arrow_cofiltered S.unop)) _ _
  (structured_arrow_op_equivalence to_Profinite S.unop)

instance costructured_arrow_filtered_u (S : Profinite.{u}ᵒᵖ) :
  is_filtered (costructured_arrow to_Profinite.op S) :=
costructured_arrow_filtered.{u u} S

instance (X : Type (u+1)) : preserves_finite_limits (colim_as_Kan_extension X) :=
begin
  sorry,
end

def discrete_as_Kan_extension (X : Type (u+1)) : CondensedSet.{u} :=
{ val := colim_as_Kan_extension X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae (colim_as_Kan_extension X)).out 0 5,
    refine ⟨_,_,_⟩,
    { sorry },
    { sorry },
    { sorry },
  end, }
