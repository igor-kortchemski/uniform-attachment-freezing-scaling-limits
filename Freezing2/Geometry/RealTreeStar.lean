module

public import Freezing2.Geometry.RealTreeDegree
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Stars in real trees

We study the configurations of finitely many points of a real tree around branch points.

* `StarSet m` is the set of distance matrices of `m` points hanging off a common center at
  positive distances; `TwoStarSet` is the set of distance matrices of two stars of three
  arms with distinct centers. Both sets are measurable.
* In a real tree, the connected components of `X \ {x}` are open, and the degree is an
  isometry invariant.
* Under the four-point condition, `m` points `yᵢ ≠ x` such that `x` lies between any two of
  them lie in pairwise distinct components of `X \ {x}`, so `x` has degree at least `m`.
  Hence if `m ≥ 2` points of a real tree have a star distance matrix, some point has degree
  at least `m`.
* Conversely, around a point of degree at least `m` there are `m` nonempty open sets such
  that any choice of one point in each has a star distance matrix; around two distinct points
  of degree at least `4` there are six nonempty open sets realizing two-star matrices.
-/

@[expose] public section

open Set Topology Metric

namespace Freezing2.RealTree

/-- Distance matrices of `m` points lying at positive distances `a i` from a common
center, every pair being joined through that center. -/
def StarSet (m : ℕ) : Set (Fin m → Fin m → ℝ) :=
  {D | ∃ a : Fin m → ℝ, (∀ i, 0 < a i) ∧ ∀ i j, D i j = if i = j then 0 else a i + a j}

/-- Distance matrices of two stars of three arms with distinct centers at distance `L`:
points `0, 1, 2` hang off the first center, points `3, 4, 5` off the second. -/
def TwoStarSet : Set (Fin 6 → Fin 6 → ℝ) :=
  {D | ∃ a : Fin 6 → ℝ, ∃ L : ℝ, 0 < L ∧ (∀ i, 0 < a i) ∧ ∀ i j, D i j =
    if i = j then 0 else a i + a j + if ((i : ℕ) < 3 ↔ (j : ℕ) < 3) then 0 else L}

section Measurability

/-- An open subset of a locally compact second countable space is `σ`-compact. -/
theorem isSigmaCompact_of_isOpen {α : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    [SecondCountableTopology α] {U : Set α} (hU : IsOpen U) : IsSigmaCompact U := by
  have := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

/-- A `σ`-compact subset of a Hausdorff space is Borel measurable. -/
theorem measurableSet_of_isSigmaCompact {α : Type*} [TopologicalSpace α] [T2Space α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {s : Set α} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n ↦ (hK n).measurableSet

theorem measurableSet_starSet (m : ℕ) : MeasurableSet (StarSet m) := by
  set f : (Fin m → ℝ) → Fin m → Fin m → ℝ :=
    fun a i j ↦ if i = j then 0 else a i + a j with hfdef
  have hU : IsOpen {a : Fin m → ℝ | ∀ i, 0 < a i} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
  have hf : Continuous f := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    by_cases hij : i = j
    · simp only [hfdef, ite_eq_left hij]
      exact continuous_const
    · simp only [hfdef, ite_eq_right hij]
      exact (continuous_apply i).add (continuous_apply j)
  have hS : StarSet m = f '' {a | ∀ i, 0 < a i} := by
    ext D
    constructor
    · rintro ⟨a, ha, hD⟩
      exact ⟨a, ha, funext fun i ↦ funext fun j ↦ (hD i j).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, fun i j ↦ rfl⟩
  rw [hS]
  exact measurableSet_of_isSigmaCompact ((isSigmaCompact_of_isOpen hU).image hf)

theorem measurableSet_twoStarSet : MeasurableSet TwoStarSet := by
  set f : (Fin 6 → ℝ) × ℝ → Fin 6 → Fin 6 → ℝ :=
    fun p i j ↦ if i = j then 0 else p.1 i + p.1 j +
      if ((i : ℕ) < 3 ↔ (j : ℕ) < 3) then 0 else p.2 with hfdef
  have hU : IsOpen {p : (Fin 6 → ℝ) × ℝ | (∀ i, 0 < p.1 i) ∧ 0 < p.2} := by
    simp only [ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt continuous_const continuous_snd)
  have hf : Continuous f := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    by_cases hij : i = j
    · simp only [hfdef, ite_eq_left hij]
      exact continuous_const
    · have h1 : Continuous fun p : (Fin 6 → ℝ) × ℝ ↦ p.1 i + p.1 j :=
        ((continuous_apply i).comp continuous_fst).add ((continuous_apply j).comp continuous_fst)
      by_cases h3 : ((i : ℕ) < 3 ↔ (j : ℕ) < 3)
      · simp only [hfdef, ite_eq_right hij, ite_eq_left h3]
        exact h1.add continuous_const
      · simp only [hfdef, ite_eq_right hij, ite_eq_right h3]
        exact h1.add continuous_snd
  have hS : TwoStarSet = f '' {p | (∀ i, 0 < p.1 i) ∧ 0 < p.2} := by
    ext D
    constructor
    · rintro ⟨a, L, hL, ha, hD⟩
      exact ⟨(a, L), ⟨ha, hL⟩, funext fun i ↦ funext fun j ↦ (hD i j).symm⟩
    · rintro ⟨⟨a, L⟩, ⟨ha, hL⟩, rfl⟩
      exact ⟨a, L, hL, ha, fun i j ↦ rfl⟩
  rw [hS]
  exact measurableSet_of_isSigmaCompact ((isSigmaCompact_of_isOpen hU).image hf)

end Measurability

variable {X : Type*} [MetricSpace X]

section Components

/-- A segment is continuous on its parameter interval. -/
theorem IsSegment.continuousOn {s t : X} {γ : ℝ → X} (hγ : IsSegment s t γ) :
    ContinuousOn γ (Icc 0 (dist s t)) := by
  refine Metric.continuousOn_iff.mpr fun a ha ε hε ↦ ⟨ε, hε, fun b hb hab ↦ ?_⟩
  rw [hγ.2.2 b hb a ha, ← Real.dist_eq]
  exact hab

/-- In a real tree, if `d(a, b) < d(a, x)` then `b` lies in the component of `a` in
`X \ {x}`: the segment from `a` to `b` avoids `x`. -/
theorem mem_connectedComponentIn_of_dist_lt (hT : IsRealTree X) {x a b : X}
    (h : dist a b < dist a x) : b ∈ connectedComponentIn ({x}ᶜ : Set X) a := by
  obtain ⟨γ, hγ⟩ := (hT a b).1
  have hsub : γ '' Icc 0 (dist a b) ⊆ {x}ᶜ := by
    rintro _ ⟨r, hr, rfl⟩ (hrx : γ r = x)
    have hd := hγ.dist_left hr
    rw [hrx] at hd
    linarith [hr.2]
  have ha : a ∈ γ '' Icc 0 (dist a b) := ⟨0, left_mem_Icc.mpr dist_nonneg, hγ.1⟩
  have hb : b ∈ γ '' Icc 0 (dist a b) := ⟨dist a b, right_mem_Icc.mpr dist_nonneg, hγ.2.1⟩
  exact (isPreconnected_Icc.image γ hγ.continuousOn).subset_connectedComponentIn ha hsub hb

/-- In a real tree, the connected components of `X \ {x}` are open. -/
theorem isOpen_connectedComponentIn_compl (hT : IsRealTree X) (x y : X) :
    IsOpen (connectedComponentIn ({x}ᶜ : Set X) y) := by
  rw [Metric.isOpen_iff]
  intro w hw
  have hwx : w ≠ x := connectedComponentIn_subset _ _ hw
  refine ⟨dist w x, dist_pos.mpr hwx, fun v hv ↦ ?_⟩
  rw [connectedComponentIn_eq hw]
  exact mem_connectedComponentIn_of_dist_lt hT (mem_ball'.mp hv)

/-- In a real tree, two points `y, z ≠ x` in different components of `X \ {x}` satisfy
`d(y, z) = d(y, x) + d(x, z)`. -/
theorem dist_eq_of_ne_component (hT : IsRealTree X) {x y z : X} (hy : y ≠ x) (hz : z ≠ x)
    (hyz : connectedComponentIn ({x}ᶜ : Set X) y ≠ connectedComponentIn {x}ᶜ z) :
    dist y z = dist y x + dist x z := by
  obtain ⟨γ, hγ⟩ := (hT y z).1
  exact (mem_segment_of_ne_component hy hz hyz hγ).symm

end Components

section Invariance

variable {Y : Type*} [MetricSpace Y]

/-- A homeomorphism maps the components of `X \ {x}` to those of `Y \ {e x}`. -/
theorem image_connectedComponentIn_compl (e : X ≃ₜ Y) {x y : X} (hy : y ≠ x) :
    e '' connectedComponentIn ({x}ᶜ : Set X) y = connectedComponentIn ({e x}ᶜ : Set Y) (e y) := by
  rw [e.image_connectedComponentIn (s := ({x}ᶜ : Set X)) hy, image_compl_eq e.bijective,
    image_singleton]

/-- The degree is invariant under homeomorphisms. -/
theorem degree_homeomorph (e : X ≃ₜ Y) (x : X) : degree (e x) = degree x := by
  have key : complementComponents (e x) = image e '' complementComponents x := by
    ext C
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨connectedComponentIn {x}ᶜ (e.symm y), ⟨e.symm y, fun h ↦ hy ?_, rfl⟩, ?_⟩
      · rw [← h, e.apply_symm_apply]
      · rw [image_connectedComponentIn_compl e (fun h ↦ hy (by rw [← h, e.apply_symm_apply])),
          e.apply_symm_apply]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨e y, fun h ↦ hy (e.injective h), image_connectedComponentIn_compl e hy⟩
  unfold degree
  rw [key, (image_injective.mpr e.injective).encard_image]

/-- The degree is invariant under isometries. -/
theorem degree_isometryEquiv (e : X ≃ᵢ Y) (x : X) : degree (e x) = degree x :=
  degree_homeomorph e.toHomeomorph x

end Invariance

section Degree

/-- Under the four-point condition, if `x` lies between `y ≠ x` and `z ≠ x`, then `y` and `z`
lie in different components of `X \ {x}`. -/
theorem connectedComponentIn_ne_of_between (h4 : FourPoint X) {x y z : X} (hy : y ≠ x)
    (hz : z ≠ x) (h : dist y x + dist x z = dist y z) :
    connectedComponentIn ({x}ᶜ : Set X) y ≠ connectedComponentIn {x}ᶜ z := by
  intro heq
  have hzC : z ∈ connectedComponentIn ({x}ᶜ : Set X) y := by
    rw [heq]
    exact mem_connectedComponentIn hz
  have hO₁ : IsOpen {p : X | 0 < gromovProduct x y p} :=
    isOpen_lt continuous_const (continuous_gromovProduct x y)
  have hO₂ : IsOpen {p : X | p ≠ x ∧ gromovProduct x y p = 0} :=
    isOpen_gromovProduct_eq_zero h4 x y
  have hcover : connectedComponentIn ({x}ᶜ : Set X) y ⊆
      {p : X | 0 < gromovProduct x y p} ∪ {p : X | p ≠ x ∧ gromovProduct x y p = 0} := by
    intro p hp
    have hpx : p ≠ x := connectedComponentIn_subset _ _ hp
    rcases eq_or_lt_of_le (gromovProduct_nonneg x y p) with h0 | h0
    · exact Or.inr ⟨hpx, h0.symm⟩
    · exact Or.inl h0
  have hy1 : 0 < gromovProduct x y y := by
    unfold gromovProduct
    rw [dist_self]
    linarith [dist_pos.mpr hy.symm]
  have hz2 : gromovProduct x y z = 0 := by
    unfold gromovProduct
    rw [dist_comm x y, ← h]
    ring
  obtain ⟨p, -, h1, h2⟩ := isPreconnected_connectedComponentIn _ _ hO₁ hO₂ hcover
    ⟨y, mem_connectedComponentIn hy, hy1⟩ ⟨z, hzC, hz, hz2⟩
  have h1' : 0 < gromovProduct x y p := h1
  linarith [h2.2]

/-- Under the four-point condition, if `x` lies between any two of `m` points `yᵢ ≠ x`, then
`x` has degree at least `m`. -/
theorem le_degree_of_between (h4 : FourPoint X) {m : ℕ} {x : X} (y : Fin m → X)
    (hy : ∀ i, y i ≠ x) (h : ∀ i j, i ≠ j → dist (y i) x + dist x (y j) = dist (y i) (y j)) :
    (m : ℕ∞) ≤ degree x := by
  unfold degree
  rw [le_encard_iff_exists_fin_injective]
  refine ⟨fun i ↦ connectedComponentIn {x}ᶜ (y i), fun i ↦ ⟨y i, hy i, rfl⟩, fun i j hij ↦ ?_⟩
  by_contra hne
  exact connectedComponentIn_ne_of_between h4 (hy i) (hy j) (h i j hne) hij

/-- **Branch points from star configurations.** If `m ≥ 2` points of a real tree have a
star distance matrix, some point has degree at least `m`. -/
theorem exists_le_degree_of_mem_starSet (hT : IsRealTree X) (h4 : FourPoint X) {m : ℕ}
    (hm : 2 ≤ m) (y : Fin m → X) (hD : (fun i j ↦ dist (y i) (y j)) ∈ StarSet m) :
    ∃ x : X, (m : ℕ∞) ≤ degree x := by
  obtain ⟨a, ha, hD⟩ := hD
  have hd : ∀ i j, dist (y i) (y j) = if i = j then 0 else a i + a j := hD
  obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin m, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have hd01 : dist (y i₀) (y i₁) = a i₀ + a i₁ := by rw [hd, ite_eq_right h01]
  obtain ⟨x, hx0, hx1⟩ : ∃ x, dist (y i₀) x = a i₀ ∧ dist x (y i₁) = a i₁ := by
    obtain ⟨γ, hγ⟩ := (hT (y i₀) (y i₁)).1
    have hmem : a i₀ ∈ Icc 0 (dist (y i₀) (y i₁)) :=
      ⟨(ha i₀).le, by rw [hd01]; linarith [ha i₁]⟩
    refine ⟨γ (a i₀), hγ.dist_left hmem, ?_⟩
    rw [hγ.dist_right hmem, hd01]
    ring
  have harm : ∀ i, dist (y i) x = a i := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0, hx0]
    by_cases hi1 : i = i₁
    · rw [hi1, dist_comm, hx1]
    have hq := h4 (y i₀) (y i₁) (y i) x
    rw [hd01, hd i₀ i, ite_eq_right (Ne.symm hi0), hd i₁ i, ite_eq_right (Ne.symm hi1), hx0,
      dist_comm (y i₁) x, hx1] at hq
    have hlow := dist_triangle (y i₀) x (y i)
    rw [hd i₀ i, ite_eq_right (Ne.symm hi0), hx0] at hlow
    have e := dist_comm x (y i)
    rcases le_max_iff.mp hq with hq | hq <;> linarith
  refine ⟨x, le_degree_of_between h4 y (fun i hi ↦ ?_) (fun i j hij ↦ ?_)⟩
  · have h0 := harm i
    rw [hi, dist_self] at h0
    linarith [ha i]
  · rw [harm i, dist_comm x (y j), harm j, hd, ite_eq_right hij]

end Degree

section OpenStars

/-- Around a point of degree at least `m` of a real tree, there are `m` nonempty open sets
(components of `X \ {x}`) such that any choice of one point in each has a star distance
matrix. -/
theorem exists_open_star (hT : IsRealTree X) {m : ℕ} {x : X} (hx : (m : ℕ∞) ≤ degree x) :
    ∃ U : Fin m → Set X, (∀ i, IsOpen (U i) ∧ (U i).Nonempty) ∧
      ∀ y : Fin m → X, (∀ i, y i ∈ U i) → (fun i j ↦ dist (y i) (y j)) ∈ StarSet m := by
  obtain ⟨f, hf, hinj⟩ := (le_encard_iff_exists_fin_injective _ m).mp hx
  have hf' : ∀ i, ∃ w, w ≠ x ∧ f i = connectedComponentIn ({x}ᶜ : Set X) w := hf
  choose w hw hfw using hf'
  refine ⟨f, fun i ↦ ⟨?_, ?_⟩, fun y hy ↦ ?_⟩
  · rw [hfw i]
    exact isOpen_connectedComponentIn_compl hT x (w i)
  · rw [hfw i]
    exact ⟨w i, mem_connectedComponentIn (hw i)⟩
  · have hyx : ∀ i, y i ≠ x := fun i ↦ by
      have h := hy i
      rw [hfw i] at h
      exact connectedComponentIn_subset _ _ h
    have hcomp : ∀ i, connectedComponentIn ({x}ᶜ : Set X) (y i) = f i := fun i ↦ by
      have h := hy i
      rw [hfw i] at h ⊢
      exact (connectedComponentIn_eq h).symm
    refine ⟨fun i ↦ dist (y i) x, fun i ↦ dist_pos.mpr (hyx i), fun i j ↦ ?_⟩
    by_cases hij : i = j
    · simp [hij]
    · rw [ite_eq_right hij]
      have hne : connectedComponentIn ({x}ᶜ : Set X) (y i) ≠ connectedComponentIn {x}ᶜ (y j) := by
        rw [hcomp, hcomp]
        exact fun h ↦ hij (hinj h)
      show dist (y i) (y j) = dist (y i) x + dist (y j) x
      rw [dist_eq_of_ne_component hT (hyx i) (hyx j) hne, dist_comm x (y j)]

/-- If `x ≠ x'` and `x` has degree at least `m + 1`, there are `m` points whose components in
`X \ {x}` are pairwise distinct and do not contain `x'`. -/
theorem exists_components_avoiding {x x' : X} (hne : x ≠ x') {m : ℕ}
    (hx : (m : ℕ∞) + 1 ≤ degree x) :
    ∃ w : Fin m → X, (∀ i, w i ≠ x) ∧ (∀ i, x' ∉ connectedComponentIn ({x}ᶜ : Set X) (w i)) ∧
      ∀ i j, connectedComponentIn ({x}ᶜ : Set X) (w i) = connectedComponentIn {x}ᶜ (w j) →
        i = j := by
  have hmem : connectedComponentIn ({x}ᶜ : Set X) x' ∈ complementComponents x :=
    ⟨x', Ne.symm hne, rfl⟩
  have hm : (m : ℕ∞) ≤ (complementComponents x \ {connectedComponentIn {x}ᶜ x'}).encard := by
    unfold degree at hx
    rw [← encard_sdiff_singleton_add_one hmem] at hx
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp hx
  obtain ⟨f, hf, hinj⟩ := (le_encard_iff_exists_fin_injective _ m).mp hm
  have hf' : ∀ i, ∃ w, w ≠ x ∧ f i = connectedComponentIn ({x}ᶜ : Set X) w := fun i ↦ (hf i).1
  choose w hw hfw using hf'
  refine ⟨w, hw, fun i hx'i ↦ (hf i).2 ?_, fun i j hij ↦ hinj ?_⟩
  · rw [mem_singleton_iff, hfw i, connectedComponentIn_eq hx'i]
  · rw [hfw i, hfw j, hij]

/-- In a real tree, let `x ≠ x'`, let `p ≠ x` lie in a component of `X \ {x}` not containing
`x'`, and `q ≠ x'` in a component of `X \ {x'}` not containing `x`. Then the segment from `p`
to `q` passes through `x` and `x'`. -/
theorem dist_eq_add_add (hT : IsRealTree X) {x x' p q : X} (hne : x ≠ x') (hp : p ≠ x)
    (hpx' : x' ∉ connectedComponentIn ({x}ᶜ : Set X) p) (hq : q ≠ x')
    (hqx : x ∉ connectedComponentIn ({x'}ᶜ : Set X) q) :
    dist p q = dist p x + dist x x' + dist x' q := by
  have hpx'' : p ≠ x' := by
    rintro rfl
    exact hpx' (mem_connectedComponentIn hp)
  have h1 : connectedComponentIn ({x}ᶜ : Set X) p ≠ connectedComponentIn {x}ᶜ x' := by
    intro h
    exact hpx' (h ▸ mem_connectedComponentIn (Ne.symm hne))
  have hd1 := dist_eq_of_ne_component hT hp (Ne.symm hne) h1
  have hlt : dist p x < dist p x' := by
    rw [hd1]
    linarith [dist_pos.mpr hne]
  have hxmem : x ∈ connectedComponentIn ({x'}ᶜ : Set X) p :=
    mem_connectedComponentIn_of_dist_lt hT hlt
  have h2 : connectedComponentIn ({x'}ᶜ : Set X) p ≠ connectedComponentIn {x'}ᶜ q := by
    intro h
    exact hqx (h ▸ hxmem)
  rw [dist_eq_of_ne_component hT hpx'' hq h2, hd1]

/-- Around two distinct points of degree at least `4` of a real tree, there are six nonempty
open sets such that any choice of one point in each has a two-star distance matrix. -/
theorem exists_open_twoStar (hT : IsRealTree X) (_h4 : FourPoint X) {x x' : X} (hne : x ≠ x')
    (hx : 4 ≤ degree x) (hx' : 4 ≤ degree x') :
    ∃ U : Fin 6 → Set X, (∀ i, IsOpen (U i) ∧ (U i).Nonempty) ∧
      ∀ y : Fin 6 → X, (∀ i, y i ∈ U i) → (fun i j ↦ dist (y i) (y j)) ∈ TwoStarSet := by
  obtain ⟨wA, hwA, hAx', hAinj⟩ :=
    exists_components_avoiding hne (m := 3) (le_trans (by norm_num) hx)
  obtain ⟨wB, hwB, hBx, hBinj⟩ :=
    exists_components_avoiding (Ne.symm hne) (m := 3) (le_trans (by norm_num) hx')
  refine ⟨fun i ↦ if (i : ℕ) < 3 then connectedComponentIn {x}ᶜ (wA ⟨i % 3, by omega⟩)
    else connectedComponentIn {x'}ᶜ (wB ⟨i % 3, by omega⟩), fun i ↦ ?_, fun y hy ↦ ?_⟩
  · dsimp only
    split_ifs
    · exact ⟨isOpen_connectedComponentIn_compl hT _ _, _, mem_connectedComponentIn (hwA _)⟩
    · exact ⟨isOpen_connectedComponentIn_compl hT _ _, _, mem_connectedComponentIn (hwB _)⟩
  have hyA : ∀ i : Fin 6, (i : ℕ) < 3 → y i ≠ x ∧ connectedComponentIn ({x}ᶜ : Set X) (y i) =
      connectedComponentIn {x}ᶜ (wA ⟨i % 3, by omega⟩) := by
    intro i hi
    have h := hy i
    dsimp only at h
    rw [ite_eq_left hi] at h
    exact ⟨connectedComponentIn_subset _ _ h, (connectedComponentIn_eq h).symm⟩
  have hyB : ∀ i : Fin 6, ¬ (i : ℕ) < 3 → y i ≠ x' ∧ connectedComponentIn ({x'}ᶜ : Set X) (y i) =
      connectedComponentIn {x'}ᶜ (wB ⟨i % 3, by omega⟩) := by
    intro i hi
    have h := hy i
    dsimp only at h
    rw [ite_eq_right hi] at h
    exact ⟨connectedComponentIn_subset _ _ h, (connectedComponentIn_eq h).symm⟩
  have hAB : ∀ i j : Fin 6, (i : ℕ) < 3 → ¬ (j : ℕ) < 3 →
      dist (y i) (y j) = dist (y i) x + dist x x' + dist x' (y j) := by
    intro i j hi hj
    refine dist_eq_add_add hT hne (hyA i hi).1 ?_ (hyB j hj).1 ?_
    · rw [(hyA i hi).2]
      exact hAx' _
    · rw [(hyB j hj).2]
      exact hBx _
  refine ⟨fun i ↦ if (i : ℕ) < 3 then dist (y i) x else dist (y i) x', dist x x',
    dist_pos.mpr hne, fun i ↦ ?_, fun i j ↦ ?_⟩
  · dsimp only
    split_ifs with hi
    · exact dist_pos.mpr (hyA i hi).1
    · exact dist_pos.mpr (hyB i hi).1
  show dist (y i) (y j) = _
  beta_reduce
  by_cases hij : i = j
  · simp [hij]
  rw [ite_eq_right hij]
  have hi6 := i.isLt
  have hj6 := j.isLt
  have hval : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
  by_cases hi : (i : ℕ) < 3 <;> by_cases hj : (j : ℕ) < 3
  · rw [ite_eq_left hi, ite_eq_left hj, ite_eq_left (iff_of_true hi hj), add_zero]
    have hne' : connectedComponentIn ({x}ᶜ : Set X) (y i) ≠ connectedComponentIn {x}ᶜ (y j) := by
      rw [(hyA i hi).2, (hyA j hj).2]
      intro h
      have := congrArg Fin.val (hAinj _ _ h)
      simp only at this
      omega
    rw [dist_eq_of_ne_component hT (hyA i hi).1 (hyA j hj).1 hne', dist_comm x (y j)]
  · rw [ite_eq_left hi, ite_eq_right hj, ite_eq_right (fun h ↦ hj (h.mp hi)), hAB i j hi hj,
      dist_comm x' (y j)]
    ring
  · rw [ite_eq_right hi, ite_eq_left hj, ite_eq_right (fun h ↦ hi (h.mpr hj)),
      dist_comm (y i) (y j), hAB j i hj hi, dist_comm x' (y i)]
    ring
  · rw [ite_eq_right hi, ite_eq_right hj, ite_eq_left (iff_of_false hi hj), add_zero]
    have hne' : connectedComponentIn ({x'}ᶜ : Set X) (y i) ≠ connectedComponentIn {x'}ᶜ (y j) := by
      rw [(hyB i hi).2, (hyB j hj).2]
      intro h
      have := congrArg Fin.val (hBinj _ _ h)
      simp only at this
      omega
    rw [dist_eq_of_ne_component hT (hyB i hi).1 (hyB j hj).1 hne', dist_comm x' (y j)]

end OpenStars

end Freezing2.RealTree
