import data.finite.set

variable (α : Type*)

-- found that anonymous `instance` caused problems because autonaming clashed with root namespace.
-- this also teaches me that `instance` statements are actually "saved" even if unnamed.
-- For this reason also anonymous instances may clash
namespace demo

/-
Warming up...
-/

-- unfavoured
example (r : set α) : finite α → r.finite := sorry
-- rather keep `finite α` for typeclass inference than as hypothesis
example (s : set α)  [finite α] : s.finite := s.to_finite
-- find proof by `library_search`.
example (a : set α)  [finite α] : a.finite := by library_search

-- inspect the proof and find that typeclass inference is taking place.
-- Indeed the important work is in
instance [finite α] {s : set α} : finite s := subtype.finite
-- find the proof by `show_term`
instance nameclash [finite α] {s : set α} : finite s := by show_term {apply_instance}

/-

Now I want to prove a characterisation of being finite.

Generally speaking this is something like
`finite α ↔ condition α`

`set.to_finite` and `finite_coe_iff` (just above it) illustrate this.
-/

-- is it bad practice to def `Type u_1 → Prop`?
def im_fin' (α : Type*) := ∀ (β : Type*) (f : β → α), (set.range f).finite

-- Is this a good approach?
class my_finite (α : Type*) :=
  -- (im_fin : ∀ (β : Type*) (f : β → α), (set.range f).finite)
  (im_fin : im_fin' α)

instance gfinite {α} [hm : my_finite α] : finite α :=
begin
  rcases hm.im_fin with h,
  let fid : α → α := id,
  have hf : (set.range fid).finite := h α (id : α → α),
  have : (set.range fid) = set.univ,
  {
    -- slightly dissatisfying but ok
    finish,
  },
  rw this at hf,
  exact set.finite_univ_iff.mp hf,
end

instance mfinite [finite α] : my_finite α :=
  {im_fin := λ _ f, (set.range f).to_finite}

-- at the level of instances we should have
example {α} : my_finite α ↔ finite α := sorry

/-
How do I formulate a statement like that?
Should I try with the Prop predicate directly?
Note that it doesn't work with all typeclasses, `finite α` is special because it is somehow Prop valued.
-/
-- `fintype α` is `Type(u)` and not `Prop`
example {α} : im_fin' α ↔ fintype α := sorry

-- however you can say
example : im_fin' α → fintype α := sorry

-- miraculously there is this "Prop-valued predicate"
example {α} : im_fin' α ↔ finite α :=
begin
  split,
  { -- copy instance proof from above
    intro h,
    let fid : α → α := id,
    have hf : (set.range fid).finite := h α (id : α → α),
    have : (set.range fid) = set.univ,
    {
    -- slightly dissatisfying but ok
      finish,
    },
    rw this at hf,
    exact set.finite_univ_iff.mp hf,
  },
  -- now without instance resolution, the former proof breaks.
  -- maybe it can be fixed but is it the right thing to do?
  intros h _ f,
  have : finite (set.range f) := subtype.finite,
  -- exact (set.range f).to_finite,
end


end demo
