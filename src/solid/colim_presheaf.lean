import category_theory.limits.kan_extension
import condensed.basic
import solid.dq_sa_comparison

noncomputable theory

universes u

open category_theory
open category_theory.limits
open Profinite
open opposite
open Fintype

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

def fintype_profinite_equiv (X : Fintype) : X ≃ to_Profinite.obj X :=
{ to_fun := λ x, x,
  inv_fun := λ x, x,
  left_inv := by tauto,
  right_inv := by tauto, }

instance : Π (Y : Fintype), unique (Y ⟶ (Fintype.of punit)) := λ Y,
{ to_inhabited := { default := λ y, punit.star, },
  uniq := λ f, (by ext), }

instance : has_terminal Fintype :=
  has_terminal_of_unique (Fintype.of punit)

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

instance : has_finite_limits Fintype :=
  @has_finite_limits_of_has_terminal_and_pullbacks _ _ _ hpb_Fintype

instance : preserves_finite_limits to_Profinite.{u} := sorry

instance structured_arrow_cofiltered (S : Profinite.{u}) :
  is_cofiltered (structured_arrow S to_Profinite) :=
(flat_of_preserves_finite_limits to_Profinite).cofiltered S

instance costructured_arrow_filtered (S : Profinite.{u}ᵒᵖ) :
  is_filtered (costructured_arrow to_Profinite.op S) :=
is_filtered.of_equivalence (structured_arrow_op_equivalence to_Profinite S.unop)

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
