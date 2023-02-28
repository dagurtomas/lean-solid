import category_theory.limits.constructions.pullbacks
import category_theory.limits.constructions.limits_of_products_and_equalizers
import category_theory.limits.shapes
import category_theory.Fintype

noncomputable theory

universe u

open category_theory
open category_theory.limits

instance : Π (Y : Fintype), unique (Y ⟶ (Fintype.of punit)) := λ Y,
{ to_inhabited := { default := λ y, punit.star, },
  uniq := λ f, (by ext), }

lemma is_terminal_Fintype_punit : is_terminal (Fintype.of punit) :=
  is_terminal.of_unique _

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

instance hpb_Fintype_u : has_pullbacks Fintype.{u} := hpb_Fintype.{u u}

instance fin_lim_Fintype : has_finite_limits Fintype :=
  @has_finite_limits_of_has_terminal_and_pullbacks _ _ _ hpb_Fintype

instance fin_lim_Fintype_u : has_finite_limits Fintype.{u} := fin_lim_Fintype.{u u}
