import for_mathlib.Profinite.disjoint_union

open category_theory
open Profinite

noncomputable theory

universe u

instance topology_ulift (X : Type u) [topological_space X] : topological_space (ulift.{u+1 u} X) :=
  topological_space.coinduced ulift.up.{u+1 u} _inst_1

lemma ulift_up_continuous (X : Type u) [topological_space X] :
  continuous (ulift.up.{u+1 u} : X → ulift.{u+1 u} X) :=
  continuous_coinduced_rng

lemma ulift_down_continuous (X : Type u) [topological_space X] :
  continuous (ulift.down.{u+1 u} : ulift.{u+1 u} X → X) :=
begin
  have : topological_space.coinduced ulift.up.{u+1 u} =
    topological_space.induced ulift.down.{u+1 u} :=
    (equiv.induced_symm (⟨ulift.up.{u+1 u}, ulift.down.{u+1 u},
    ulift.down_up, ulift.up_down⟩ : X ≃ ulift.{u+1 u} X)).symm,
  have h : topology_ulift X = topological_space.induced ulift.down.{u+1 u} _inst_1,
  { rw ← this,
    refl },
  rw h,
  exact continuous_induced_dom,
end

lemma ulift_down_inducing (X : Type u) [topological_space X] :
  inducing (ulift.down.{u+1 u} :  ulift.{u+1 u} X → X) :=
{ induced := congr_fun ((equiv.induced_symm (⟨ulift.up.{u+1 u}, ulift.down.{u+1 u},
    ulift.down_up, ulift.up_down⟩ : X ≃ ulift.{u+1 u} X)).symm) _inst_1 }

def ulift_down_embedding (X : Type u) [topological_space X] :
  embedding (ulift.down.{u+1 u} : ulift.{u+1 u} X → X) :=
  ⟨ulift_down_inducing X, ulift.down_injective⟩

def Top_ulift : Top.{u} ⥤ Top.{u+1} :=
{
  obj := λ X, ⟨ulift.{u+1 u} X.α, topology_ulift X.α⟩,
  map := λ X Y f, ⟨ulift.up.{u+1 u} ∘ f ∘ ulift.down.{u+1 u}, continuous.comp
    (ulift_up_continuous Y.α) (continuous.comp f.continuous_to_fun (ulift_down_continuous X.α))⟩,
}

instance compact_of_ulift (X : Profinite.{u}) :
  compact_space (Top_ulift.{u}.obj (Profinite.to_Top.obj X)) :=
begin
  haveI hc : compact_space (Profinite.to_Top.obj X) := CompHaus.compact_space,
  have hcr := is_compact_range (ulift_up_continuous.{u} (Profinite.to_Top.obj X)),
  fconstructor,
  suffices h : (set.univ : set (Top_ulift.{u}.obj (Profinite.to_Top.obj X))) =
    set.range ulift.up.{u+1 u},
  { rw h, exact hcr, },
  have hs : function.surjective (ulift.up.{u+1 u} : Profinite.to_Top.obj X →
    Top_ulift.obj (Profinite.to_Top.obj X)) :=
    ulift.up_surjective,
  ext,
  split,
  { intros hx,
    obtain ⟨t,hs'⟩ := hs x,
    rw ← hs',
    tauto },
  tauto,
end

instance t2_of_ulift (X : Profinite.{u}) :
  t2_space (Top_ulift.{u}.obj (Profinite.to_Top.obj X)) :=
begin
  haveI : t2_space (Profinite.to_Top.obj X) := CompHaus.t2_space,
  exact embedding.t2_space (ulift_down_embedding X),
end

instance tot_disc_of_ulift (X : Profinite.{u}) :
  totally_disconnected_space (Top_ulift.{u}.obj (Profinite.to_Top.obj X)) :=
begin
  haveI : totally_disconnected_space (Profinite.to_Top.obj X) := X.is_totally_disconnected,
  have hi : is_totally_disconnected ((ulift.down.{u+1 u} '' set.univ) : set (Profinite.to_Top.obj X)) :=
    is_totally_disconnected_of_totally_disconnected_space _,
  exact ⟨embedding.is_totally_disconnected (ulift_down_embedding X) hi⟩,
end

def Profinite_ulift : Profinite.{u} ⥤ Profinite.{u+1} :=
{
  obj := λ X, Profinite.of (Top_ulift.{u}.obj (Profinite.to_Top.obj X)),
  map := λ X Y f, Top_ulift.map f,
}

lemma Profinite_ulift_map_to_pullback_cond {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  (Profinite_ulift.{u}.map (pullback.fst f g)) ≫ (Profinite_ulift.{u}.map f) =
  (Profinite_ulift.{u}.map (pullback.snd f g)) ≫ (Profinite_ulift.{u}.map g) :=
begin
  rw ← Profinite_ulift.map_comp' _ _,
  rw ← Profinite_ulift.map_comp' _ _,
  rw pullback.condition _ _,
end

def Profinite_ulift_map_to_pullback {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  Profinite_ulift.{u}.obj (pullback f g) ⟶ pullback (Profinite_ulift.{u}.map f)
  (Profinite_ulift.{u}.map g) :=
  pullback.lift _ _ _ _ (Profinite_ulift_map_to_pullback_cond f g)

instance Profinite_ulift_map_to_pullback_is_epi {X B : Profinite.{u}} (f g : X ⟶ B) :
  epi (Profinite_ulift_map_to_pullback f g) :=
begin
  refine (Profinite.epi_iff_surjective (Profinite_ulift_map_to_pullback f g)).mpr _,
  intros x,
  have h : f (ulift.down.{u+1 u} x.1.1) = g (ulift.down.{u+1 u} x.1.2),
  { cases x,
    cases x_val,
    cases x_val_snd,
    cases x_val_fst,
    dsimp at *,
    injections_and_clear,
    assumption },
  use ulift.up.{u+1 u} ⟨⟨(ulift.down.{u+1 u} x.1.1), (ulift.down.{u+1 u} x.1.2)⟩, h⟩,
  cases x,
  cases x_val,
  cases x_val_snd,
  cases x_val_fst,
  refl,
end

instance to_Top_Profinite_ulift_map_pullback_is_epi {X B : Profinite.{u}} (f g : X ⟶ B) :
  epi $ to_Top.map $ Profinite_ulift_map_to_pullback f g :=
(Top.epi_iff_surjective (Profinite_ulift_map_to_pullback f g)).mpr
  ((Profinite.epi_iff_surjective (Profinite_ulift_map_to_pullback f g)).mp
  (Profinite_ulift_map_to_pullback_is_epi f g))

lemma Profinite_ulift_fst {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  (Profinite_ulift_map_to_pullback f g) ≫ pullback.fst _ _ =
  (Profinite_ulift.{u}.map (pullback.fst f g)) :=
  pullback.lift_fst _ _ _ _ (Profinite_ulift_map_to_pullback_cond f g)

lemma Profinite_ulift_snd {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
  (Profinite_ulift_map_to_pullback f g) ≫ pullback.snd _ _ =
  (Profinite_ulift.{u}.map (pullback.snd f g)) :=
  pullback.lift_snd _ _ _ _ (Profinite_ulift_map_to_pullback_cond f g)

instance Profinite_ulift_faithful : faithful Profinite_ulift.{u} :=
{ map_injective' := begin
    intros X Y f g h,
    have hf : (Profinite_ulift.map f).to_fun = ulift.up.{u+1 u} ∘ f ∘ ulift.down.{u+1 u} := by refl,
    have hg : (Profinite_ulift.map g).to_fun = ulift.up.{u+1 u} ∘ g ∘ ulift.down.{u+1 u} := by refl,
    apply_fun (λ x, x.to_fun) at h,
    rw hf at h,
    rw hg at h,
    ext,
    obtain ⟨a', hh⟩ := ulift.down_surjective a,
    rw function.funext_iff at h,
    have h' := h a',
    norm_num at h',
    rw hh at h',
    exact h',
  end, }

instance Profinite_ulift_to_Top_faithful : faithful (Profinite_ulift.{u} ⋙ to_Top.{u+1}) :=
  faithful.comp Profinite_ulift to_Top

instance Profinite_ulift_full : full Profinite_ulift.{u} :=
begin
  have h : ∀ (X Y : Profinite.{u}), function.surjective (Profinite_ulift.{u}.map : (X ⟶ Y) →
    (Profinite_ulift.obj X ⟶ Profinite_ulift.obj Y)),
  intros X Y f,
  let a := ulift.down.{u+1 u} ∘ f ∘ ulift.up.{u+1 u},
  have ha : continuous a := continuous.comp (ulift_down_continuous Y.to_CompHaus.to_Top.α)
    (continuous.comp f.continuous_to_fun (ulift_up_continuous X.to_CompHaus.to_Top.α)),
  use ⟨a, ha⟩,
  ext,
  norm_num,
  have hf : ∀ (X Y : Profinite.{u}) (i : X ⟶ Y),
    (Profinite_ulift.map i).to_fun = ulift.up.{u+1 u} ∘ i ∘ ulift.down.{u+1 u} :=
    by { intros X Y i, refl },
  have hfidX := hf X X (𝟙 X),
  rw Profinite_ulift.{u}.map_id' X at hfidX,
  dsimp at hfidX,
  have hfidY := hf Y Y (𝟙 Y),
  rw Profinite_ulift.{u}.map_id' Y at hfidY,
  dsimp at hfidY,
  dsimp,
  have : ⇑(Profinite_ulift.map {to_fun := a, continuous_to_fun := ha}) =
    ulift.up.{u+1 u} ∘  a ∘ ulift.down.{u+1 u} := hf X Y ⟨a, ha⟩,
  rw this,
  have hfa : a = ulift.down.{u+1 u} ∘ f ∘ ulift.up.{u+1 u} := by refl,
  rw hfa,
  rw ← function.comp.assoc ulift.up _ ulift.down,
  rw ← function.comp.assoc ulift.up ulift.down (f ∘ ulift.up),
  rw ← hfidY,
  rw function.comp.assoc id _ ulift.down,
  rw function.comp.assoc f ulift.up ulift.down,
  rw ← hfidX,
  simp only [eq_self_iff_true, function.comp.right_id, function.comp.left_id],
  exact category_theory.functor.full_of_surjective _ h,
end

instance Profinite_ulift_to_Top_full : full (Profinite_ulift.{u} ⋙ to_Top.{u+1}) :=
  full.comp Profinite_ulift to_Top


instance (S : Profinite.{u+1}) : compact_space (to_Top.obj S) := S.to_CompHaus.is_compact

instance compact_of_Profinite_ulift (S : Profinite.{u}) :
  compact_space ((Profinite_ulift ⋙ to_Top).obj S) :=
  (Profinite_ulift.obj S).to_CompHaus.is_compact

instance t2_of_Profinite_ulift (S : Profinite.{u}) :
  t2_space ((Profinite_ulift ⋙ to_Top).obj S) :=
  (Profinite_ulift.obj S).to_CompHaus.is_hausdorff

instance totally_disconnected_of_Profinite_ulift (S : Profinite.{u}) :
  totally_disconnected_space ((Profinite_ulift ⋙ to_Top).obj S) :=
  (Profinite_ulift.obj S).is_totally_disconnected

lemma Profinite_ulift_preserves_closed_subsets {S : Profinite.{u}}
  (C : set $ Profinite_ulift.obj S) (hC : is_closed C) :
  is_closed (C ∘ (ulift.up.{u+1 u} : S → Profinite_ulift.obj S) : set S) :=
begin
  have : C ∘ ulift.up = ulift.up ⁻¹' C := by refl,
  rw this,
  exact (continuous_iff_is_closed).mp (ulift_up_continuous _) C hC,
end
