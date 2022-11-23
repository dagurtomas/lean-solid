import condensed.ab
import topology.category.Profinite.as_limit
import topology.category.Top.basic
import category_theory.limits.has_limits
import hacks_and_tricks.by_exactI_hack


open category_theory
open Profinite
-- open classical
open Condensed

noncomputable theory

-- set_option pp.implicit true
-- set_option pp.universes true
-- set_option pp.all true
-- set_option class.instance_max_depth 100

universe u

variables (S T : Profinite.{u}) -- [inhabited (discrete_quotient S)]
variables (X : Top.{u}) [discrete_topology X]
variables (i j : discrete_quotient S)
variables (Y : Fintype.{u})
variables (f : (to_Top.obj S) ⟶ X)

def Cont_out (Y : Top.{u}) : Top.{u} ⥤ Type u :=
{
  obj := λ X, (Y ⟶ X),
  map := λ X₁ X₂ f, (λ g, g ≫ f),
  map_id' := by { intros, ext, refl, },
  map_comp' := by { intros, ext, refl, },
}

def Cont_in (X : Top.{u}) : Top.{u}ᵒᵖ ⥤ Type u :=
{
  obj := λ Y, (Y.unop ⟶ X),
  map := λ X₁ X₂ f, (λ g, f.unop ≫ g),
  map_id' := by { intros, ext, refl, },
  map_comp' := by { intros, ext, refl, },
}

def fin_incl : Fintype.{u} ⥤ Type u :=
{
  obj := λ X, X,
  map := λ X₁ X₂ f, f,
  map_id' := by { intros, refl, },
  map_comp' := by { intros, refl, },
}

def Colim_diagram (X : Top.{u}) : (discrete_quotient S)ᵒᵖ ⥤ Type u :=
  S.fintype_diagram.op ⋙ fin_incl.op ⋙ Top.discrete.op ⋙ (Cont_in X)

instance S_colim_exists : limits.has_colimit (Colim_diagram S X) :=
begin
  apply_instance,
end

def CSX_as_cone_map (S : Profinite.{u}) (X : Top.{u}) : (Colim_diagram S X) ⟶ (category_theory.functor.const (discrete_quotient S)ᵒᵖ).obj ((to_Top.obj S) ⟶ X) :=
{app :=
    begin
      intros i,
      refine as_hom _,
      dsimp,
      intros a,
      exact (S.as_limit_cone.π.app i.unop) ≫ a,
    end,
  naturality' :=
    begin
      intros i j f,
      tidy,
    end,
}

def CSX_as_cone (S : Profinite.{u}) (Y : Top.{u}) : limits.cocone (Colim_diagram S Y) :=
{
  X := ((to_Top.obj S) ⟶ Y),
  ι := CSX_as_cone_map S Y,
}

def can (S : Profinite.{u}) (X : Top.{u}) : ((limits.colimit (Colim_diagram S X)) ⟶ ((to_Top.obj S) ⟶ X)) :=
begin
  exact limits.colimit.desc (Colim_diagram S X) (CSX_as_cone S X),
end

lemma to_im_cont {X Y : Top.{u}} (f : X ⟶ Y) : continuous (set.range_factorization f) :=
begin
  have hfc : continuous f,
  exact continuous_map.continuous f,
  have h : ∀ (x : X), f x ∈ set.range f,
  intros x,
  exact set.mem_range_self x,
  exact continuous.subtype_mk hfc h,
end

def im {X Y : Top.{u}} (f: X ⟶ Y) : Top.{u} :=
begin
  have imf_top : topological_space (set.range f),
  apply_instance,
  exact ⟨(set.range f), imf_top⟩,
end

instance im_discrete {X Y : Top.{u}} (f : X ⟶ Y) [discrete_topology Y] : discrete_topology (im f) :=
begin
  exact subtype.discrete_topology,
end

def to_im {X Y : Top.{u}} (f : X ⟶ Y) : X ⟶ im f :=
begin
  refine ⟨set.range_factorization f, _⟩,
  norm_num,
  exact to_im_cont f,
end

lemma to_im_surj {X Y : Top.{u}} (f : X ⟶ Y) : function.surjective (to_im f) :=
begin
  tidy,
end


def im_as_discrete_quotient {S : Profinite.{u}} {X : Top.{u}} (g : (to_Top.obj S) ⟶ X) [discrete_topology X] : discrete_quotient S :=
begin
  let f := to_im g,

  have hdisc : discrete_topology (im g),
  apply_instance,

  -- Defining the equivalence relation of the image
  fconstructor,
  intros s1 s2,

  exact f s1 = f s2,
  split,
  tauto,
  split,
  tauto,
  intros x y z,
  dsimp,
  intros h j,
  rw h,
  exact j,

  -- Clopen fibres
  intros x,
  have h : {s2 : S | f x = f s2} = f ⁻¹' {f x},
  ext,
  split,
  intros hx1,
  have hx1' : f x = f x_1,
  exact hx1,
  exact mem_id_rel.mpr (eq.symm hx1),

  intros hx1,
  have hx1' : f x = f x_1,
  exact mem_id_rel.mp (eq.symm hx1),
  exact hx1',

  rw h,

  have hfc : continuous f,
  exact continuous_map.continuous f,

  refine (quotient_map.is_clopen_preimage _).mpr _,

  -- Show that f is a quotient map
  fconstructor,
  exact to_im_surj g,

  ext,
  split,

  -- -->
  intros hx1,
  unfold topological_space.coinduced,
  have hx1' : is_open (f ⁻¹' x_1),
  exact continuous_def.mp hfc x_1 hx1,
  exact hx1',

  -- <--
  intros hx1,
  exact is_open_discrete x_1,

  split,
  exact is_open_discrete _,
  exact is_closed_discrete _,
end

lemma im_eq_quotient_by_kernel {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
↥(im_as_discrete_quotient f) = quotient (setoid.ker (to_im f)) :=
begin
  refl,
end

-- noncomputable lemma im_as_disc_equiv_im {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
--   ↥(im_as_discrete_quotient f) ≃ ↥(im f) :=
-- begin
--   rw im_eq_quotient_by_kernel f,
--   sorry,
--   -- suffices h : (im f) = (set.range (to_im f)),
--   -- rw h,
--   -- refl,
--   -- rw h,
--   -- exact setoid.quotient_ker_equiv_range (to_im f),
-- end

-- \ u-| = ↥

def incl_im {X Y : Top.{u}} (f : X ⟶ Y) : (im f) ⟶ Y :=
begin
  let i : set.range f → Y := λ y, y,
  -- intros y,
  -- exact y,
  have hi : continuous i := continuous_induced_dom,
  exact ⟨i, hi⟩,
end

lemma factor_f {X Y : Top.{u}} (f : X ⟶ Y) : f = (to_im f) ≫ (incl_im f) :=
begin
  ext,
  refl,
end

lemma im_finite {X : CompHaus.{u}} {Y : Top.{u}}
  [discrete_topology Y] (f : (CompHaus.to_Top X) ⟶ Y) : fintype (im f) :=
begin
  have X_comp : is_compact (set.univ : set X),
  exact compact_univ,
  have im_comp : is_compact (set.range f),
  refine is_compact_range _,
  exact continuous_map.continuous f,
  rw is_compact_iff_finite at im_comp,
  exact set.finite.fintype im_comp,
end

def im_as_fintype {X : CompHaus.{u}} {Y : Top.{u}}
  [discrete_topology Y] (f : (CompHaus.to_Top X) ⟶ Y) : Fintype.{u} :=
begin
  exact ⟨(im f), (im_finite f)⟩,
end

def im_as_eq_rel {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
  setoid (to_Top.obj S) :=
begin
  exact ⟨(im_as_discrete_quotient f).rel, (im_as_discrete_quotient f).equiv⟩,
end

def im_as_quotient {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
  [discrete_topology X] : Type u := quotient (im_as_eq_rel f)

def map_to_im_as_quotient' {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
   [discrete_topology X] : (to_Top.obj S) → Top.discrete.obj (im_as_quotient f) := quotient.mk'

lemma cont_map_to_im_as_quotient' {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
   [discrete_topology X] : continuous (map_to_im_as_quotient' f) := (im_as_discrete_quotient f).proj_continuous

def map_to_im_as_quotient {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X)
   [discrete_topology X] : (to_Top.obj S) ⟶ Top.discrete.obj (im_as_quotient f) := ⟨(map_to_im_as_quotient' f), (cont_map_to_im_as_quotient' f)⟩

lemma im_eq_quotient {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
↥(im_as_discrete_quotient f) = quotient (im_as_eq_rel f) :=
begin
  refl,
end

def incl_im' {S : Profinite.{u}} {X : Top.{u}} (f : (to_Top.obj S) ⟶ X) [discrete_topology X] :
  Top.discrete.obj (fin_incl.obj (S.fintype_diagram.obj (im_as_discrete_quotient f))) ⟶ X :=
begin
  have heq1 : (im_as_discrete_quotient f).rel = (im_as_eq_rel f).rel := by refl,
  have h : ∀ a b : (to_Top.obj S), (im_as_discrete_quotient f).rel a b → f a = f b,
  intros a b,
  intros h',
  rw factor_f f,
  have h2 : (to_im f) a = (to_im f) b,
  exact h',
  have h3 : (to_im f ≫ incl_im f) a = (incl_im f) ((to_im f) a),
  refl,
  rw h3,
  rw h2,
  refl,
  let setmap : quotient (im_as_eq_rel f) → X := quot.lift f h,
  -- let setmap := incl_im_sets f,
  -- rw _inst_3 at setmap,
  rw ← (im_eq_quotient f) at setmap,
  have setmap2 : Top.discrete.obj (fin_incl.obj (S.fintype_diagram.obj (im_as_discrete_quotient f)))
    → (im_as_discrete_quotient f) := λ x, x,
  let g := setmap ∘ setmap2,
  have hg : continuous g,
  { exact continuous_bot,
  },
  exact ⟨g, hg⟩,
end

lemma discreteness_condition_necessary {S : Profinite.{u}} {X : Top.{u}} [discrete_topology X] : is_iso (can S X) :=
begin
  refine (is_iso_iff_bijective (can S X)).mpr _,
  split,
  { intros a b,
    intros h,
    have h' : (im_as_discrete_quotient (can S X a)) = (im_as_discrete_quotient (can S X b)) := by tauto,
    let i : discrete_quotient S := (im_as_discrete_quotient (can S X a)),
    let j : discrete_quotient S := (im_as_discrete_quotient (can S X b)),
    let F := Colim_diagram S X,
    let FS := S.diagram,
    -- let Slimcone : limits.limit_cone S.diagram := _,
    let Slim₁ : S ≅ (limit_cone S.diagram).X := iso_as_limit_cone_lift S,

    -- let Slim₂ := limits.limit.iso_limit_cone (Slimcone),
    let φ : F.obj (opposite.op i) ⟶ ((to_Top.obj S) ⟶ X) := (limits.colimit.ι F (opposite.op i)) ≫ (can S X),
    let pi := limits.limit.π FS i,
    sorry,
    -- let φ' := F.map (pi.op)
    -- have hia : i = im_as_discrete_quotient (can S X a) := by refl,
    -- have hib : i = im_as_discrete_quotient (can S X b) := by rw ← h',
    -- have h_im : to_im (can S X a) = to_im (can S X b),
    -- let n := limits.colimit.ι (Colim_diagram S X) (opposite.op i),
    -- let im_a := incl_im' (can S X a),
    -- -- have hab : im_a ≃ im_b,
    -- have hab : Top.discrete.obj (fin_incl.obj (S.fintype_diagram.obj (im_as_discrete_quotient (can S X a)))) = Top.discrete.obj (fin_incl.obj (S.fintype_diagram.obj (im_as_discrete_quotient (can S X b)))),
    -- rw h',
    -- let im_b : Top.discrete.obj (fin_incl.obj (S.fintype_diagram.obj i)) := incl_im' (can S X b),
    -- -- have im_b : Top.discrete.obj (fin_incl.obj (S.fintype_diagram.obj i)) ⟶ X,
    -- -- { rw hib,
    -- --   exact incl_im' (can S X b),
    -- -- },
    -- have hab' : im_a = im_b,

    -- -- TODO: define im_i in a similar way.
    -- -- have h2 : incl_im' (can S X a) = incl_im' (can S X b) := by tauto,
    -- let na := (limits.colimit.ι (Colim_diagram S X) (opposite.op (im_as_discrete_quotient (can S X a)))),
    -- let nb := (limits.colimit.ι (Colim_diagram S X) (opposite.op (im_as_discrete_quotient (can S X b)))),

    -- apply_fun limits.colimit.hom_ext at h,
    -- let ima := incl_im' (can S X a),
    -- let na := limits.colimit.ι (Colim_diagram S X) (opposite.op (im_as_discrete_quotient (can S X a))),
    -- have ha : a = na.app ima,
    -- { sorry,
    -- },
    -- rw ha,
    -- let imb := incl_im' (can S X b),
    -- let nb := limits.colimit.ι (Colim_diagram S X) (opposite.op (im_as_discrete_quotient (can S X b))),
    -- have hb : b = nb.app imb,
    -- { sorry,
    -- },
    -- rw hb,

  },
  { intros f,
    let a := limits.colimit.ι (Colim_diagram S X) (opposite.op (im_as_discrete_quotient f)),
    fconstructor,
    exact a.app (incl_im' f),
    ext,
    unfold can,
    tidy,
  },
end

-- lemma discreteness_condition_sufficient (S : Profinite.{u}) (X : CondensedSet.{u})
