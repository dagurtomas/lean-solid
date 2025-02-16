import topology.connected
import topology.separation
import solid.for_nobeling.connected_discrete

universe u

def I_type (α : Type u) [topological_space α] :=
  {fI : α → bool // continuous fI}

def map_to_I (α : Type u) [topological_space α] : α → (Π (i : {fI : α → bool // continuous fI}), (function.const {fI : α → bool // continuous fI} bool) i) :=
  λ a i, ((coe : {fI : α → bool // continuous fI} → (α → bool)) i) a

def map_to_I' (α : Type u) [topological_space α] : α → ({fI : α → bool // continuous fI} → bool) :=
  λ a i, ((coe : {fI : α → bool // continuous fI} → (α → bool)) i) a

lemma inj_to_prod' (α : Type u) [topological_space α] [totally_separated_space α] :
  continuous (map_to_I' α) ∧ function.injective (map_to_I' α) :=
begin
  let I := {fI : α → bool // continuous fI},
  let f : α → (I → bool) := map_to_I' α,
  have hf : f = map_to_I' α := by triv,
  split,
  { refine continuous_pi _,
    intros i,
    cases i, assumption, },
  { rw ← hf,
    intros a b hab,
    let s : set α := {a, b},
    have h : ∀ fi : α → bool, continuous fi → ∀ x ∈ s, ∀ y ∈ s, fi x = fi y,
    { intros fi hfi x hx y hy,
      cases hx, cases hy, work_on_goal 1 { induction hy, induction hx, refl }, work_on_goal 1 { induction hy, induction hx, dsimp at * }, work_on_goal 2 { induction hx, cases hy, work_on_goal 1 { induction hy, dsimp at * }, work_on_goal 2 { induction hy, refl } },
      { let fi' : I := ⟨fi, hfi⟩,
        have hab' : f x fi' = f y fi' := by { rw hab },
        exact hab' },
      { let fi' : I := ⟨fi, hfi⟩,
        have hab' : f y fi' = f x fi' := by { rw hab },
        exact hab'.symm } },
    by_contra',
    have h' := exists_clopen_of_totally_separated this,
    obtain ⟨U, hU, h₁⟩ := h',
    let fi := set.bool_indicator U,
    specialize h (set.bool_indicator U) _ a _ b _,
    { exact (continuous_bool_indicator_iff_clopen U).mpr hU },
    { exact set.mem_insert a {b} },
    { exact set.mem_insert_of_mem a rfl },
    apply h₁.2,
    cases h₁, cases hU,
    rw (set.mem_iff_bool_indicator U a) at h₁_left,
    rw h₁_left at h,
    rw set.mem_iff_bool_indicator U b,
    exact h.symm, },
end

lemma inj_to_prod (α : Type u) [topological_space α] [totally_separated_space α] :
  ∃ (I : Type u), ∃ (f : α → (Π (i : I), (function.const I bool) i)), continuous f ∧
  function.injective f :=
begin
  let I := {fI : α → bool // continuous fI},
  use I,
  let f : α → (Π (i : I), (function.const I bool) i) := λ a i, ((coe : I → (α → bool)) i) a,
  use f,
  split,
  { refine continuous_pi _,
    intros i,
    cases i, assumption, },
  { intros a b hab,
    let s : set α := {a, b},
    have h : ∀ fi : α → bool, continuous fi → ∀ x ∈ s, ∀ y ∈ s, fi x = fi y,
    { intros fi hfi x hx y hy,
      cases hx, cases hy, work_on_goal 1 { induction hy, induction hx, refl }, work_on_goal 1 { induction hy, induction hx, dsimp at * }, work_on_goal 2 { induction hx, cases hy, work_on_goal 1 { induction hy, dsimp at * }, work_on_goal 2 { induction hy, refl } },
      { let fi' : I := ⟨fi, hfi⟩,
        have hab' : f x fi' = f y fi' := by { rw hab },
        exact hab' },
      { let fi' : I := ⟨fi, hfi⟩,
        have hab' : f y fi' = f x fi' := by { rw hab },
        exact hab'.symm } },
    by_contra',
    have h' := exists_clopen_of_totally_separated this,
    obtain ⟨U, hU, h₁⟩ := h',
    let fi := set.bool_indicator U,
    specialize h (set.bool_indicator U) _ a _ b _,
    { exact (continuous_bool_indicator_iff_clopen U).mpr hU },
    { exact set.mem_insert a {b} },
    { exact set.mem_insert_of_mem a rfl },
    apply h₁.2,
    cases h₁, cases hU,
    rw (set.mem_iff_bool_indicator U a) at h₁_left,
    rw h₁_left at h,
    rw set.mem_iff_bool_indicator U b,
    exact h.symm, },
end

lemma compact_finite_intersection {α S : Type*} {U : set α} [topological_space α] [compact_space α]
  (hU : is_open U) {F : S → set α} (hF : ∀ s : S, is_closed (F s)) (hFi : (⋂ s : S, F s) ⊆ U) :
  ∃ S₀ : finset S, (⋂ s ∈ S₀, (F s)) ⊆ U :=
begin
  have hUc : is_compact Uᶜ := is_closed.is_compact (is_closed_compl_iff.mpr hU),
  let UF : S → set α := λ s, (F s)ᶜ,
  have hUo : ∀ s : S, is_open (UF s) := λ s, is_open_compl_iff.mpr (hF s),
  have hsU : Uᶜ ⊆ ⋃ s : S, UF s,
  { rw set.Union_eq_compl_Inter_compl,
    rw set.compl_subset_compl,
    dsimp only [UF],
    intros x hx,
    simp at hx,
    apply hFi,
    exact set.mem_Inter.mpr hx },
  { obtain ⟨S₀, h⟩ := is_compact.elim_finite_subcover hUc UF hUo hsU,
    use S₀,
    rw ← set.compl_subset_compl,
    rw set.Inter_eq_compl_Union_compl,
    simp only [set.compl_Inter, set.compl_Union],
    simp only [UF] at h,
    intros u hu,
    obtain ⟨t, i, hi⟩ := h hu,
    use t,
    split,
    cases i,
    use i_w,
    simp only [compl_compl, set.Union_congr_Prop],
    exact i_h,
    exact hi, },
end



def quasicomponent {α : Type*} (x : α) [topological_space α] : set α :=
  ⋂ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z

lemma quasicomponent_eq_component_of_compact_space {α : Type*} (x : α) [topological_space α]
  [compact_space α] [t2_space α] : connected_component x = quasicomponent x :=
begin
  haveI h_normal : normal_space α := normal_of_compact_t2,
  haveI hQclosed : is_closed (quasicomponent x),
        { refine is_closed_Inter _,
          intros i,
          cases i,
          exact i_property.1.2 },
  haveI hQinQ : quasicomponent x ⊆ quasicomponent x := by tauto,
  haveI h' : x ∈ quasicomponent x,
      { unfold quasicomponent,
        refine set.mem_Inter.mpr _,
        intros i,
        cases i,
        exact i_property.2}, -- TODO: golf
  ext y,
  split,
  { intros hy,
    apply connected_component_subset_Inter_clopen,
    exact hy },
  { suffices h : is_preconnected (quasicomponent x),
    { unfold connected_component,
      intros hy,
      use quasicomponent x,
      split, split, exact h, exact h', exact hy},
    { rw is_preconnected_iff_subset_of_fully_disjoint_closed hQclosed,
      intros X₁ X₂ hX₁ hX₂ hX₁uX₂ hX₁nX₂,
      obtain ⟨U, V, h⟩ := normal_separation hX₁ hX₂ hX₁nX₂,
      have hUVc : closure U ⊆ Vᶜ,
      { rw is_closed.closure_subset_iff (is_closed_compl_iff.mpr h.2.1),
        exact disjoint.subset_compl_right h.2.2.2.2, },
      have hVUc : closure V ⊆ Uᶜ,
      { rw is_closed.closure_subset_iff (is_closed_compl_iff.mpr h.1),
        exact disjoint.subset_compl_right (h.2.2.2.2).symm, },
      -- let S := {s : set α // is_clopen s ∧ quasicomponent x ⊆ s ∧ s ⊆ U ∪ V},
      let S := {s : set α // is_clopen s ∧ x ∈ s},
      let F : S → set α := λ s, s,
      have hF : ∀ s : S, is_closed (F s),
      { intros s, cases s, exact s_property.1.2, },
      have hUV : is_open (U ∪ V) := is_open.union h.1 h.2.1,
      have h_inter : (⋂ (s : S), F s) ⊆ U ∪ V := λ a ha, set.union_subset_union h.2.2.1 h.2.2.2.1 (hX₁uX₂ ha),
      obtain ⟨S₀, hS₀⟩ := compact_finite_intersection hUV hF h_inter,
      let F' := (⋂ (s : S) (H : s ∈ S₀), (λ (s : S), F s) s),
      have hx : x ∈ X₁ ∪ X₂ := hX₁uX₂ h',
      cases hx,
      { left,
        have hFclopen : is_clopen F',
        { refine is_clopen_bInter_finset _,
          intros i hi,
          simp only [],
          cases i,
          exact i_property.1 },
        have hFU : is_clopen (U ∩ F'),
        { split, { exact is_open.inter h.1 (is_clopen.is_open hFclopen) },
          refine is_closed_of_closure_subset _,
          intros a ha,
          have hUVF : (U ∪ V) ∩ F' = F',
          { ext, split,
            exact λ hx1, (set.inter_subset_right (U ∪ V) F') hx1,
            intros hx1,
            split, exact hS₀ hx1, exact hx1 },
          have hUUV : (closure U) ∩ (U ∪ V) = U,
          { ext, split,
            { intros hx1,
              cases hx1.2, { exact h_1 },
              exfalso,
              exact hUVc hx1.1 h_1, },
            { intros hx1,
              split,
              exact subset_closure hx1,
              left,
              exact hx1 } },
          rw ← hUUV,
          rw set.inter_assoc,
          rw hUVF,
          rw ← is_closed.closure_eq hFclopen.2,
          exact closure_inter_subset_inter_closure U F' ha },
        have hQUF : quasicomponent x ⊆ U ∩ F',
        { have hxUF : x ∈ U ∩ F',
          { split,
            { exact h.2.2.1 hx },
            { simp only [set.mem_Inter, subtype.forall],
              intros a b hab,
              -- exact b.2.1 h'
              exact b.2 } },
          have hUF : U ∩ F' ∈ {Z : set α | is_clopen Z ∧ x ∈ Z} := ⟨hFU, hxUF⟩,
          unfold quasicomponent,
          intros x1 hx1,
          rw set.mem_Inter at hx1,
          exact hx1 ⟨(U ∩ F'), hUF⟩ },
        have hXQ : X₂ ∩ (quasicomponent x) = ∅,
        { apply set.eq_empty_of_subset_empty,
          intros a ha,
          have ha' := set.inter_subset_inter_right X₂ hQUF ha,
          have ha'' := set.inter_subset_inter_left (U ∩ F') h.2.2.2.1 ha',
          rw ← set.inter_assoc at ha'',
          rw set.inter_comm V U at ha'',
          rw (set.disjoint_iff_inter_eq_empty.mp h.2.2.2.2) at ha'',
          exact ha''.1 },
        intros a ha,
        cases hX₁uX₂ ha, { exact h_1 },
        exfalso,
        exact (set.ext_iff.mp hXQ a).mp ⟨h_1, ha⟩, },
      { right,
        have hFclopen : is_clopen F',
        { refine is_clopen_bInter_finset _,
          intros i hi,
          simp only [],
          cases i,
          exact i_property.1 },
        have hFU : is_clopen (V ∩ F'),
        { split, { exact is_open.inter h.2.1 (is_clopen.is_open hFclopen) },
          refine is_closed_of_closure_subset _,
          intros a ha,
          have hUVF : (U ∪ V) ∩ F' = F',
          { ext, split,
            exact λ hx1, (set.inter_subset_right (U ∪ V) F') hx1,
            intros hx1,
            split, exact hS₀ hx1, exact hx1 },
          have hUUV : (closure V) ∩ (U ∪ V) = V,
          { ext, split,
            { intros hx1,
              cases hx1.2, swap, { exact h_1 },
              exfalso,
              exact hVUc hx1.1 h_1, },
            { intros hx1,
              split,
              exact subset_closure hx1,
              right,
              exact hx1 } },
          rw ← hUUV,
          rw set.inter_assoc,
          rw hUVF,
          rw ← is_closed.closure_eq hFclopen.2,
          exact closure_inter_subset_inter_closure V F' ha },
        have hQUF : quasicomponent x ⊆ V ∩ F',
        { have hxUF : x ∈ V ∩ F',
          { split,
            { exact h.2.2.2.1 hx },
            { simp only [set.mem_Inter, subtype.forall],
              intros a b hab,
              -- exact b.2.1 h'
              exact b.2 } },
          have hUF : V ∩ F' ∈ {Z : set α | is_clopen Z ∧ x ∈ Z} := ⟨hFU, hxUF⟩,
          unfold quasicomponent,
          intros x1 hx1,
          rw set.mem_Inter at hx1,
          exact hx1 ⟨(V ∩ F'), hUF⟩ },
        have hXQ : X₁ ∩ (quasicomponent x) = ∅,
        { apply set.eq_empty_of_subset_empty,
          intros a ha,
          have ha' := set.inter_subset_inter_right X₁ hQUF ha,
          have ha'' := set.inter_subset_inter_left (V ∩ F') h.2.2.1 ha',
          rw ← set.inter_assoc at ha'',
          rw (set.disjoint_iff_inter_eq_empty.mp h.2.2.2.2) at ha'',
          exact ha''.1 },
        intros a ha,
        cases hX₁uX₂ ha, swap, { exact h_1 },
        exfalso,
        exact (set.ext_iff.mp hXQ a).mp ⟨h_1, ha⟩ } } },
end

instance totally_separated_of_totally_disconnected_compact_hausdorff (α : Type*)
  [topological_space α] [hc : compact_space α] [htd :totally_disconnected_space α] [hh : t2_space α] :
  totally_separated_space α :=
begin
  fconstructor,
  intros x hx y hy hxy,
  have hcompx : connected_component x = {x} :=
    totally_disconnected_space_iff_connected_component_singleton.mp htd x,
  have hcqx : connected_component x = quasicomponent x :=
    quasicomponent_eq_component_of_compact_space x,
  rw hcompx at hcqx,
  obtain ⟨V, Y, h⟩ := t2_separation hxy,
  let S := {s : set α // is_clopen s ∧ x ∈ s},
  let F : S → set α := λ s, s,
  have hF : ∀ s : S, is_closed (F s),
  { intros s, cases s, exact s_property.1.2, },
  have h_inter : (⋂ (s : S), F s) ⊆ V :=
    λ a ha, (set.singleton_subset_iff.mpr h.2.2.1) ((set.ext_iff.mp hcqx a).mpr ha),
  obtain ⟨S₀, hS₀⟩ := compact_finite_intersection h.1 hF h_inter,
  let U := (⋂ (s : S) (H : s ∈ S₀), (λ (s : S), F s) s),
  have hU : is_clopen U,
  { refine is_clopen_bInter_finset _,
    intros i hi,
    cases i,
    exact i_property.1 },
  have hxU : x ∈ U,
  { simp only [set.mem_Inter, subtype.forall],
    intros a b hab,
    exact b.2 },
  have hyUc : y ∈ Uᶜ, -- := λ hyU, h.2.2.2.2 ⟨(hS₀ hyU), h.2.2.2.1⟩,
  { intros hyU,
    have hy₁ := hS₀ hyU,
    have hy₂ := h.2.2.2.1,
    have : V ∩ Y ⊆ ∅ := set.subset_empty_iff.mpr (set.disjoint_iff_inter_eq_empty.mp h.2.2.2.2),
    exact this ⟨hy₁, hy₂⟩, },
  have huniv : set.univ ⊆ U ∪ Uᶜ := (set.subset.antisymm_iff.mp (set.union_compl_self U)).2,
  have hdisjoint : disjoint U Uᶜ := set.disjoint_iff_inter_eq_empty.mpr (set.inter_compl_self U),
  use U,
  use Uᶜ,
  exact ⟨hU.1, is_open_compl_iff.mpr hU.2, hxU, hyUc, huniv, hdisjoint⟩,
end
