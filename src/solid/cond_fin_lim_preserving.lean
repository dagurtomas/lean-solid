import condensed.basic

noncomputable theory

universe u

open category_theory
open category_theory.limits

variable (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1))
variable [preserves_finite_limits X]

def condensed_of_fin_lim_preserving : CondensedSet.{u} :=
{ val := X,
  cond :=
  begin
    rw is_sheaf_iff_is_sheaf_of_type,
    rw (functor.is_proetale_sheaf_of_types_tfae X).out 0 5,
    refine ⟨_,_,_⟩,
    { sorry, },
    -- rw (functor.is_proetale_sheaf_of_types_tfae X).out 0 2,
    -- intros α _inst_2 S T f s P h,
    -- refine ⟨_,_⟩,
  end }
