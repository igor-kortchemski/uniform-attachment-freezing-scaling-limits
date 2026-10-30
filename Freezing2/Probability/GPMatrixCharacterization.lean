module

public import Freezing2.Geometry.GromovProkhorov
public import Freezing2.Geometry.RowSpace
public import Freezing2.Probability.SampledDistanceLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# The Gromov--Prokhorov topology through sampled distance matrices

Background subsection `GPdef` of the source, Lemma `equivGP` (inventory item
N15), cited there from Löhr 2013.

For a Polish measured space `X` with law `μ`, let `(xᵢ)` be an iid sequence of
law `μ` and `M^X = (d(xᵢ, xⱼ))_{i,j ∈ ℕ}`. Its law `matrixLaw` lives on the
product space `ℕ → ℕ → ℝ`. The laws `blockLaw k` of its top-left `k × k`
blocks are the finite iid matrix laws `iidDistanceLawOn`. Both depend only on
the law on the support, hence are invariant under GP isometry and are defined
on `GPSpace`.

Main results.
* `tendsto_iff_forall_tendsto_map_arrayBlock`: on `ℕ → ℕ → ℝ`, convergence in
  distribution is convergence in distribution of every finite top-left block.
  Every open set is an increasing union of open sets determined by one block,
  and the portmanteau theorem applies.
* `GPSpace.levyProkhorovDist_blockLaw_le` (direct half): the block law of
  order `k` is `2k`-Lipschitz from the GP distance to the Lévy--Prokhorov
  distance. A GP realization is restricted to the closed separable hull of the
  two images, and iid products are compared one coordinate at a time.
* `GPSpace.tendsto_of_forall_tendsto_blockLaw` (converse half): convergence of
  all block laws implies GP convergence. The finite space `gpMatrixSpace`
  reconstructed from `m + 1` samples is GP-close to the space, up to the
  Lévy--Prokhorov distance from the empirical measure to the law. The mean of
  this distance is bounded, uniformly over all Polish measured spaces, by
  `2ε + kη` plus the probability that the first of `k + 1` iid points is
  `ε`-far from the others, a closed-set probability of the `(k+1)`-block law,
  once `(m+1)η² ≥ 1` (`PolishMeasuredSpace.integral_dist_gpMatrixSpace_le`:
  cells around `k` auxiliary iid centres and a variance bound). The
  portmanteau theorem transfers the far probability from the limit to the
  approximating spaces, and the triangle inequality through the
  reconstruction concludes.
* `GPSpace.equivGP`, `GPSpace.tendsto_iff_tendsto_matrixLaw`: Lemma `equivGP`,
  for sequences and for countably generated filters.
* Consequences: `GPSpace.matrixLaw_injective` (Gromov's reconstruction theorem
  for Polish measured spaces) and `GPSpace.isEmbedding_matrixLaw`.

The converse half uses neither the Gromov--Prokhorov--Winter relative
compactness criterion nor a separate reconstruction theorem: the limit space is
compared directly with reconstructions from finitely many of its samples, and
uniqueness of limits is a consequence.
-/

@[expose] public section

open Filter MeasureTheory Metric ProbabilityTheory Set TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction

universe u

namespace Freezing2

section Arrays

/-- The infinite array of pairwise distances along a sequence of points. -/
def distanceArray {X : Type*} [PseudoMetricSpace X] (ω : ℕ → X) : ℕ → ℕ → ℝ :=
  fun i j ↦ dist (ω i) (ω j)

theorem continuous_distanceArray {X : Type*} [PseudoMetricSpace X] :
    Continuous (distanceArray (X := X)) := by
  unfold distanceArray
  fun_prop

/-- The top-left `k × k` block of an infinite array. -/
def arrayBlock (k : ℕ) (M : ℕ → ℕ → ℝ) : Fin k → Fin k → ℝ := fun i j ↦ M i j

theorem continuous_arrayBlock (k : ℕ) : Continuous (arrayBlock k) := by
  unfold arrayBlock
  fun_prop

/-- Every point of an open set of arrays has a neighbourhood inside the set
that is determined by a single finite block. -/
theorem exists_arrayBlock_preimage_subset {G : Set (ℕ → ℕ → ℝ)} (hG : IsOpen G)
    {M : ℕ → ℕ → ℝ} (hM : M ∈ G) :
    ∃ k : ℕ, ∃ V : Set (Fin k → Fin k → ℝ), IsOpen V ∧ arrayBlock k M ∈ V ∧
      arrayBlock k ⁻¹' V ⊆ G := by
  classical
  have hc : Continuous (fun F : ℕ × ℕ → ℝ ↦ fun i j ↦ F (i, j)) := by fun_prop
  obtain ⟨I, w, hw, hsub⟩ := isOpen_pi_iff.1 (hG.preimage hc) (fun p ↦ M p.1 p.2) hM
  set k := I.sup (fun p ↦ max p.1 p.2) + 1 with hkdef
  have hk : ∀ p ∈ I, p.1 < k ∧ p.2 < k := by
    intro p hp
    have h := Finset.le_sup (f := fun p : ℕ × ℕ ↦ max p.1 p.2) hp
    constructor <;> omega
  let get : (Fin k → Fin k → ℝ) → ℕ × ℕ → ℝ := fun B p ↦
    if h : p.1 < k ∧ p.2 < k then B ⟨p.1, h.1⟩ ⟨p.2, h.2⟩ else 0
  have hget : ∀ p, Continuous fun B ↦ get B p := by
    intro p
    by_cases h : p.1 < k ∧ p.2 < k
    · simp only [get, h, and_self, dite_true]
      fun_prop
    · simp only [get, h, dite_false]
      exact continuous_const
  have hgetM : ∀ p ∈ I, get (arrayBlock k M) p = M p.1 p.2 := by
    intro p hp
    simp only [get, (hk p hp).1, (hk p hp).2, and_self, dite_true, arrayBlock]
  refine ⟨k, ⋂ p ∈ I, (fun B ↦ get B p) ⁻¹' w p, ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset fun p hp ↦ (hw p hp).1.preimage (hget p)
  · simp only [mem_iInter, mem_preimage]
    intro p hp
    rw [hgetM p hp]
    exact (hw p hp).2
  · intro M' hM'
    simp only [mem_preimage, mem_iInter] at hM'
    have hmem : (fun p : ℕ × ℕ ↦ M' p.1 p.2) ∈ (I : Set (ℕ × ℕ)).pi w := by
      intro p hp
      have h := hM' p hp
      simpa only [get, (hk p hp).1, (hk p hp).2, and_self, dite_true, arrayBlock] using h
    exact hsub hmem

/-- Restriction of a block to a smaller top-left block. -/
def blockRestrict {k l : ℕ} (h : k ≤ l) (B : Fin l → Fin l → ℝ) : Fin k → Fin k → ℝ :=
  fun i j ↦ B (Fin.castLE h i) (Fin.castLE h j)

theorem continuous_blockRestrict {k l : ℕ} (h : k ≤ l) : Continuous (blockRestrict h) := by
  unfold blockRestrict
  fun_prop

theorem blockRestrict_arrayBlock {k l : ℕ} (h : k ≤ l) (M : ℕ → ℕ → ℝ) :
    blockRestrict h (arrayBlock l M) = arrayBlock k M := rfl

/-- Convergence in distribution on the countable product `ℕ → ℕ → ℝ` follows
from convergence in distribution of every finite top-left block. Every open set
is an increasing union of open sets determined by one finite block. -/
theorem tendsto_of_forall_tendsto_map_arrayBlock {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {P : ι → ProbabilityMeasure (ℕ → ℕ → ℝ)}
    {Q : ProbabilityMeasure (ℕ → ℕ → ℝ)}
    (h : ∀ k, Tendsto (fun i ↦ (P i).map (arrayBlock k)) L (𝓝 (Q.map (arrayBlock k)))) :
    Tendsto P L (𝓝 Q) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  let V : (k : ℕ) → Set (Fin k → Fin k → ℝ) := fun k ↦
    ⋃₀ {V | IsOpen V ∧ arrayBlock k ⁻¹' V ⊆ G}
  have hVopen (k : ℕ) : IsOpen (V k) := isOpen_sUnion fun _ hV ↦ hV.1
  let W : ℕ → Set (ℕ → ℕ → ℝ) := fun k ↦ arrayBlock k ⁻¹' V k
  have hWG (k : ℕ) : W k ⊆ G := by
    intro M hM
    obtain ⟨U, hU, hMU⟩ := mem_sUnion.1 hM
    exact hU.2 hMU
  have hWmono : Monotone W := by
    intro k l hkl M hM
    obtain ⟨U, hU, hMU⟩ := mem_sUnion.1 hM
    refine mem_sUnion.2 ⟨blockRestrict hkl ⁻¹' U,
      ⟨hU.1.preimage (continuous_blockRestrict hkl), ?_⟩, hMU⟩
    intro M' hM'
    exact hU.2 hM'
  have hWcover : ⋃ k, W k = G := by
    apply Subset.antisymm (iUnion_subset hWG)
    intro M hM
    obtain ⟨k, U, hU, hMU, hUG⟩ := exists_arrayBlock_preimage_subset hG hM
    exact mem_iUnion.2 ⟨k, mem_sUnion.2 ⟨U, ⟨hU, hUG⟩, hMU⟩⟩
  rw [← hWcover, hWmono.measure_iUnion]
  refine iSup_le fun k ↦ ?_
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (h k) (hVopen k)
  have hmeas : MeasurableSet (V k) := (hVopen k).measurableSet
  have hm : Measurable (arrayBlock k) := (continuous_arrayBlock k).measurable
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_apply hm hmeas] at hlim
  exact hlim.trans
    (liminf_le_liminf (Eventually.of_forall fun i ↦ measure_mono (subset_iUnion W k)))

/-- Convergence in distribution on `ℕ → ℕ → ℝ` is equivalent to convergence in
distribution of every finite top-left block. -/
theorem tendsto_iff_forall_tendsto_map_arrayBlock {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {P : ι → ProbabilityMeasure (ℕ → ℕ → ℝ)}
    {Q : ProbabilityMeasure (ℕ → ℕ → ℝ)} :
    Tendsto P L (𝓝 Q) ↔
      ∀ k, Tendsto (fun i ↦ (P i).map (arrayBlock k)) L (𝓝 (Q.map (arrayBlock k))) :=
  ⟨fun h k ↦ ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q h
    (continuous_arrayBlock k), tendsto_of_forall_tendsto_map_arrayBlock⟩

end Arrays

section ArrayLaws

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y]

theorem measurable_distanceArray : Measurable (distanceArray (X := X)) :=
  continuous_distanceArray.measurable

omit [BorelSpace X] [SecondCountableTopology X] in
/-- The law of the infinite matrix of distances of an iid sequence of law `μ`. -/
noncomputable def iidDistanceArrayLawOn (μ : ProbabilityMeasure X) :
    ProbabilityMeasure (ℕ → ℕ → ℝ) :=
  ⟨(Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure X))).map distanceArray, inferInstance⟩

/-- The finite blocks of the infinite iid matrix law are the finite iid matrix laws. -/
theorem map_iidDistanceArrayLawOn_arrayBlock (μ : ProbabilityMeasure X) (k : ℕ) :
    (iidDistanceArrayLawOn μ).map (arrayBlock k) = iidDistanceLawOn μ k := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure X))).map distanceArray).map
      (arrayBlock k) = (Measure.pi (fun _ : Fin k ↦ (μ : Measure X))).map (distanceMatrix k)
  have hpre : (Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure X))).map
      (fun ω (i : Fin k) ↦ ω i) = Measure.pi (fun _ : Fin k ↦ (μ : Measure X)) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun i : Fin k ↦ (i : ℕ))
      Fin.val_injective, Measure.infinitePi_eq_pi]
  have hr : Measurable fun (ω : ℕ → X) (i : Fin k) ↦ ω i :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (i : ℕ)
  rw [Measure.map_map (continuous_arrayBlock k).measurable measurable_distanceArray, ← hpre,
    Measure.map_map (continuous_distanceMatrix k).measurable hr]
  rfl

omit [SecondCountableTopology X] in
/-- An isometric image of the sampling law has the same infinite matrix law. -/
theorem iidDistanceArrayLawOn_map_isometry (μ : ProbabilityMeasure X) (f : X → Y)
    (hf : Isometry f) : iidDistanceArrayLawOn (μ.map f) = iidDistanceArrayLawOn μ := by
  apply ProbabilityMeasure.toMeasure_injective
  have hfm : Measurable f := hf.continuous.measurable
  change (Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure X).map f)).map distanceArray =
    (Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure X))).map distanceArray
  have hp := Measure.infinitePi_map_pi (μ := fun _ : ℕ ↦ (μ : Measure X))
    (f := fun _ : ℕ ↦ f) (fun _ ↦ hfm)
  have hpm : Measurable fun (x : ℕ → X) (i : ℕ) ↦ f (x i) :=
    measurable_pi_iff.mpr fun i ↦ hfm.comp (measurable_pi_apply i)
  rw [← hp, Measure.map_map measurable_distanceArray hpm]
  congr 1
  funext ω i j
  exact hf.dist_eq _ _

end ArrayLaws

namespace PolishMeasuredSpace

/-- The law of a Polish measured space, carried by the closed support. -/
noncomputable def supportProb (X : PolishMeasuredSpace.{u}) :
    ProbabilityMeasure (X.law : Measure X).support :=
  ⟨supportLaw (X.law : Measure X), inferInstance⟩

theorem law_eq_map_supportProb (X : PolishMeasuredSpace.{u}) :
    X.law = X.supportProb.map Subtype.val :=
  ProbabilityMeasure.toMeasure_injective (map_supportLaw (X.law : Measure X)).symm

/-- The law of the `k × k` block `(d(xᵢ, xⱼ))_{i,j<k}` of the sampled distance
matrix, for an iid sequence `(xᵢ)` of law `μ^X`. -/
noncomputable def blockLaw (X : PolishMeasuredSpace.{u}) (k : ℕ) :
    ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  iidDistanceLawOn X.law k

/-- The law of the source's `M^X = (d(xᵢ, xⱼ))_{i,j ∈ ℕ}`, for an iid sequence
`(xᵢ)` of law `μ^X`, on the product space `ℕ → ℕ → ℝ`. -/
noncomputable def matrixLaw (X : PolishMeasuredSpace.{u}) : ProbabilityMeasure (ℕ → ℕ → ℝ) :=
  iidDistanceArrayLawOn X.law

theorem map_matrixLaw_arrayBlock (X : PolishMeasuredSpace.{u}) (k : ℕ) :
    X.matrixLaw.map (arrayBlock k) = X.blockLaw k :=
  map_iidDistanceArrayLawOn_arrayBlock X.law k

/-- Only the law on the support matters for the block laws. -/
theorem blockLaw_eq_supportProb (X : PolishMeasuredSpace.{u}) (k : ℕ) :
    X.blockLaw k = iidDistanceLawOn X.supportProb k := by
  have h := iidDistanceLawOn_map_isometry X.supportProb Subtype.val isometry_subtype_coe k
  rw [← law_eq_map_supportProb X] at h
  exact h

/-- Only the law on the support matters for the matrix law. -/
theorem matrixLaw_eq_supportProb (X : PolishMeasuredSpace.{u}) :
    X.matrixLaw = iidDistanceArrayLawOn X.supportProb := by
  have h := iidDistanceArrayLawOn_map_isometry X.supportProb Subtype.val isometry_subtype_coe
  rw [← law_eq_map_supportProb X] at h
  exact h

/-- GP-isometric spaces have the same block laws. -/
theorem blockLaw_eq_of_gpIsometric {X Y : PolishMeasuredSpace.{u}} (h : GPIsometric X Y)
    (k : ℕ) : X.blockLaw k = Y.blockLaw k := by
  obtain ⟨e, he⟩ := h
  have hY : X.supportProb.map e = Y.supportProb := ProbabilityMeasure.toMeasure_injective he
  rw [blockLaw_eq_supportProb, blockLaw_eq_supportProb, ← hY,
    iidDistanceLawOn_map_isometry _ _ e.isometry]

/-- GP-isometric spaces have the same matrix law. -/
theorem matrixLaw_eq_of_gpIsometric {X Y : PolishMeasuredSpace.{u}} (h : GPIsometric X Y) :
    X.matrixLaw = Y.matrixLaw := by
  obtain ⟨e, he⟩ := h
  have hY : X.supportProb.map e = Y.supportProb := ProbabilityMeasure.toMeasure_injective he
  rw [matrixLaw_eq_supportProb, matrixLaw_eq_supportProb, ← hY,
    iidDistanceArrayLawOn_map_isometry _ _ e.isometry]

end PolishMeasuredSpace

namespace GPSpace

/-- The finite block laws, well defined on GP classes. -/
noncomputable def blockLaw (k : ℕ) : GPSpace.{u} → ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  Quotient.lift (fun X : PolishMeasuredSpace.{u} ↦ X.blockLaw k)
    (fun _ _ h ↦ PolishMeasuredSpace.blockLaw_eq_of_gpIsometric h k)

/-- The law of the infinite distance matrix `M^X`, well defined on GP classes. -/
noncomputable def matrixLaw : GPSpace.{u} → ProbabilityMeasure (ℕ → ℕ → ℝ) :=
  Quotient.lift (fun X : PolishMeasuredSpace.{u} ↦ X.matrixLaw)
    (fun _ _ h ↦ PolishMeasuredSpace.matrixLaw_eq_of_gpIsometric h)

@[simp] theorem blockLaw_toGPSpace (k : ℕ) (X : PolishMeasuredSpace.{u}) :
    blockLaw k (toGPSpace X) = X.blockLaw k := rfl

@[simp] theorem matrixLaw_toGPSpace (X : PolishMeasuredSpace.{u}) :
    matrixLaw (toGPSpace X) = X.matrixLaw := rfl

/-- The block laws are the finite-dimensional marginals of the matrix law. -/
theorem map_matrixLaw_arrayBlock (k : ℕ) (X : GPSpace.{u}) :
    (matrixLaw X).map (arrayBlock k) = blockLaw k X := by
  induction X using Quotient.inductionOn with
  | _ X => exact X.map_matrixLaw_arrayBlock k

/-- Convergence in distribution of matrix laws is convergence of every block law. -/
theorem tendsto_matrixLaw_iff_forall_tendsto_blockLaw {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {X : ι → GPSpace.{u}} {Y : GPSpace.{u}} :
    Tendsto (fun i ↦ matrixLaw (X i)) L (𝓝 (matrixLaw Y)) ↔
      ∀ k, Tendsto (fun i ↦ blockLaw k (X i)) L (𝓝 (blockLaw k Y)) := by
  rw [tendsto_iff_forall_tendsto_map_arrayBlock]
  simp only [map_matrixLaw_arrayBlock]

end GPSpace

section ProductProkhorov

variable {S W : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [SecondCountableTopology S] [MetricSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]

/-- Changing the first factor of a product law moves it, for the max metric, by
at most the Lévy--Prokhorov distance of the first factors. -/
theorem levyProkhorovEDist_prod_left_le (α β : Measure S) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] (ρ : Measure W) [IsProbabilityMeasure ρ] :
    levyProkhorovEDist (α.prod ρ) (β.prod ρ) ≤ levyProkhorovEDist α β := by
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε _ hB
  rw [Measure.prod_apply_symm hB, Measure.prod_apply_symm isOpen_thickening.measurableSet]
  calc ∫⁻ w, α ((fun a ↦ (a, w)) ⁻¹' B) ∂ρ
      ≤ ∫⁻ w, (β ((fun a ↦ (a, w)) ⁻¹' thickening ε.toReal B) + ε) ∂ρ := by
        refine lintegral_mono fun w ↦ ?_
        have hBw : MeasurableSet ((fun a ↦ (a, w)) ⁻¹' B) := hB.preimage measurable_prodMk_right
        refine (left_measure_le_of_levyProkhorovEDist_lt hε hBw).trans
          (add_le_add (measure_mono fun a ha ↦ ?_) le_rfl)
        obtain ⟨a', ha', hd⟩ := mem_thickening_iff.1 ha
        exact mem_thickening_iff.2 ⟨(a', w), ha', by simpa [Prod.dist_eq] using hd⟩
    _ = ∫⁻ w, β ((fun a ↦ (a, w)) ⁻¹' thickening ε.toReal B) ∂ρ + ε := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

omit [SecondCountableTopology W] in
/-- Changing the second factor of a product law moves it, for the max metric, by
at most the Lévy--Prokhorov distance of the second factors. -/
theorem levyProkhorovEDist_prod_right_le (ρ : Measure W) [IsProbabilityMeasure ρ]
    (α β : Measure S) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    levyProkhorovEDist (ρ.prod α) (ρ.prod β) ≤ levyProkhorovEDist α β := by
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε _ hB
  rw [Measure.prod_apply hB, Measure.prod_apply isOpen_thickening.measurableSet]
  calc ∫⁻ w, α (Prod.mk w ⁻¹' B) ∂ρ
      ≤ ∫⁻ w, (β (Prod.mk w ⁻¹' thickening ε.toReal B) + ε) ∂ρ := by
        refine lintegral_mono fun w ↦ ?_
        have hBw : MeasurableSet (Prod.mk w ⁻¹' B) := hB.preimage measurable_prodMk_left
        refine (left_measure_le_of_levyProkhorovEDist_lt hε hBw).trans
          (add_le_add (measure_mono fun a ha ↦ ?_) le_rfl)
        obtain ⟨a', ha', hd⟩ := mem_thickening_iff.1 ha
        exact mem_thickening_iff.2 ⟨(w, a'), ha', by simpa [Prod.dist_eq] using hd⟩
    _ = ∫⁻ w, β (Prod.mk w ⁻¹' thickening ε.toReal B) ∂ρ + ε := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] in
/-- Prepending a coordinate is nonexpansive for the max metrics. -/
theorem lipschitzWith_finCons (k : ℕ) :
    LipschitzWith 1 (fun p : S × (Fin k → S) ↦ (Fin.cons p.1 p.2 : Fin (k + 1) → S)) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [NNReal.coe_one, one_mul]
  refine (dist_pi_le_iff dist_nonneg).2 fun i ↦ ?_
  cases i using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero, Prod.dist_eq]
    exact le_max_left _ _
  | succ j =>
    simp only [Fin.cons_succ, Prod.dist_eq]
    exact (dist_le_pi_dist p.2 q.2 j).trans (le_max_right _ _)

omit [MetricSpace S] [BorelSpace S] [SecondCountableTopology S] in
theorem piFinSuccAbove_zero_symm_eq (k : ℕ) :
    ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ S) 0).symm =
      fun p : S × (Fin k → S) ↦ (Fin.cons p.1 p.2 : Fin (k + 1) → S) := by
  funext p
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

/-- Iid products of laws at Lévy--Prokhorov distance `δ` are at distance at most
`k δ` for the max metric. -/
theorem levyProkhorovEDist_pi_le (α β : Measure S) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] : ∀ k : ℕ,
    levyProkhorovEDist (Measure.pi fun _ : Fin k ↦ α) (Measure.pi fun _ : Fin k ↦ β) ≤
      k * levyProkhorovEDist α β
  | 0 => by
    rw [Measure.pi_of_empty, Measure.pi_of_empty, levyProkhorovEDist_self]
    exact bot_le
  | k + 1 => by
    have hα := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ α) 0).symm
    have hβ := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ β) 0).symm
    rw [← hα.map_eq, ← hβ.map_eq, piFinSuccAbove_zero_symm_eq]
    calc _ ≤ levyProkhorovEDist (α.prod (Measure.pi fun _ : Fin k ↦ α))
          (β.prod (Measure.pi fun _ : Fin k ↦ β)) :=
          levyProkhorovEDist_map_le _ _ (lipschitzWith_finCons k)
      _ ≤ levyProkhorovEDist (α.prod (Measure.pi fun _ : Fin k ↦ α))
            (β.prod (Measure.pi fun _ : Fin k ↦ α)) +
          levyProkhorovEDist (β.prod (Measure.pi fun _ : Fin k ↦ α))
            (β.prod (Measure.pi fun _ : Fin k ↦ β)) :=
          levyProkhorovEDist_triangle _ _ _
      _ ≤ levyProkhorovEDist α β + k * levyProkhorovEDist α β :=
          add_le_add (levyProkhorovEDist_prod_left_le _ _ _)
            ((levyProkhorovEDist_prod_right_le _ _ _).trans (levyProkhorovEDist_pi_le α β k))
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * levyProkhorovEDist α β := by push_cast; ring

end ProductProkhorov

/-- A `K`-Lipschitz map with `1 ≤ K` multiplies the Lévy--Prokhorov distance by
at most `K`. -/
theorem levyProkhorovDist_map_le_mul {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {K : ℝ≥0} (hK : 1 ≤ K)
    {f : X → Y} (hf : LipschitzWith K f) :
    levyProkhorovDist (μ.map f) (ν.map f) ≤ K * levyProkhorovDist μ ν := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := zero_lt_one.trans_le hK1
  have hfm : Measurable f := hf.continuous.measurable
  have hd0 : 0 ≤ levyProkhorovDist μ ν := ENNReal.toReal_nonneg
  apply levyProkhorovDist_le_of_forall_le _ _ (by positivity)
  intro ε B hε hB
  have hε0 : 0 < ε := lt_of_le_of_lt (by positivity) hε
  have hlt : levyProkhorovEDist μ ν < ENNReal.ofReal (ε / K) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _), lt_div_iff₀ hKpos]
    change levyProkhorovDist μ ν * K < ε
    linarith
  have h := left_measure_le_of_levyProkhorovEDist_lt hlt (hB.preimage hfm)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  rw [Measure.map_apply hfm hB, Measure.map_apply hfm isOpen_thickening.measurableSet]
  refine h.trans (add_le_add (measure_mono ?_) (ENNReal.ofReal_le_ofReal (div_le_self hε0.le hK1)))
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
  refine mem_thickening_iff.2 ⟨f z, hz, ?_⟩
  calc dist (f x) (f z) ≤ K * dist x z := hf.dist_le_mul x z
    _ < K * (ε / K) := by gcongr
    _ = ε := by field_simp

/-- The distance matrix of `k` points is `2`-Lipschitz for the max metrics. -/
theorem lipschitzWith_distanceMatrix {X : Type*} [PseudoMetricSpace X] (k : ℕ) :
    LipschitzWith 2 (distanceMatrix (X := X) k) := by
  refine LipschitzWith.of_dist_le_mul fun v w ↦ ?_
  have h2 : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [h2]
  refine (dist_pi_le_iff (by positivity)).2 fun i ↦ (dist_pi_le_iff (by positivity)).2 fun j ↦ ?_
  calc dist (dist (v i) (v j)) (dist (w i) (w j)) ≤ dist (v i) (w i) + dist (v j) (w j) :=
        dist_dist_dist_le _ _ _ _
    _ ≤ dist v w + dist v w := add_le_add (dist_le_pi_dist v w i) (dist_le_pi_dist v w j)
    _ = 2 * dist v w := by ring

/-- Quantitative continuity of finite sampled-matrix laws on a fixed separable
metric space. -/
theorem levyProkhorovDist_iidDistanceLawOn_le {S : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [SecondCountableTopology S] (α β : ProbabilityMeasure S) (k : ℕ) :
    levyProkhorovDist (iidDistanceLawOn α k : Measure (Fin k → Fin k → ℝ))
        (iidDistanceLawOn β k : Measure (Fin k → Fin k → ℝ)) ≤
      2 * k * levyProkhorovDist (α : Measure S) (β : Measure S) := by
  change levyProkhorovDist ((Measure.pi fun _ : Fin k ↦ (α : Measure S)).map (distanceMatrix k))
    ((Measure.pi fun _ : Fin k ↦ (β : Measure S)).map (distanceMatrix k)) ≤ _
  have h1 := levyProkhorovDist_map_le_mul (Measure.pi fun _ : Fin k ↦ (α : Measure S))
    (Measure.pi fun _ : Fin k ↦ (β : Measure S)) (by norm_num : (1 : ℝ≥0) ≤ 2)
    (lipschitzWith_distanceMatrix k)
  have h2 : levyProkhorovDist (Measure.pi fun _ : Fin k ↦ (α : Measure S))
      (Measure.pi fun _ : Fin k ↦ (β : Measure S)) ≤
      k * levyProkhorovDist (α : Measure S) (β : Measure S) := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k)
      (levyProkhorovEDist_ne_top _ _)) (levyProkhorovEDist_pi_le (α : Measure S) (β : Measure S) k)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have h2' : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [h2'] at h1
  calc _ ≤ 2 * levyProkhorovDist (Measure.pi fun _ : Fin k ↦ (α : Measure S))
        (Measure.pi fun _ : Fin k ↦ (β : Measure S)) := h1
    _ ≤ 2 * (k * levyProkhorovDist (α : Measure S) (β : Measure S)) := by gcongr
    _ = _ := by ring

/-- Restricting to a closed subspace cannot increase the Lévy--Prokhorov distance. -/
theorem levyProkhorovEDist_le_map_subtype_val {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] {S : Set Z} (hS : IsClosed S) (α β : Measure S) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] :
    levyProkhorovEDist α β ≤ levyProkhorovEDist (α.map Subtype.val) (β.map Subtype.val) := by
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε _ hB
  have hm : MeasurableEmbedding (Subtype.val : S → Z) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  have hi : MeasurableSet (Subtype.val '' B) := hm.measurableSet_image.mpr hB
  have h := left_measure_le_of_levyProkhorovEDist_lt hε hi
  rw [Measure.map_apply measurable_subtype_coe hi,
    Measure.map_apply measurable_subtype_coe isOpen_thickening.measurableSet,
    Subtype.val_injective.preimage_image,
    preimage_thickening_image_of_isometry isometry_subtype_coe] at h
  exact h

namespace PolishMeasuredSpace

/-- A GP realization of cost below `δ` gives block laws at Lévy--Prokhorov
distance at most `2 k δ`. The ambient space is replaced by the closed separable
hull of the two images. -/
theorem levyProkhorovDist_blockLaw_le_of_distance_lt (X Y : PolishMeasuredSpace.{u}) (k : ℕ)
    {δ : ℝ} (hδ : distance X Y < δ) :
    levyProkhorovDist (X.blockLaw k : Measure (Fin k → Fin k → ℝ))
      (Y.blockLaw k : Measure (Fin k → Fin k → ℝ)) ≤ 2 * k * δ := by
  obtain ⟨r, ⟨Z, m, i, j, hi, hj, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (gpCosts_nonempty _ _) hδ
  let := m
  let : MeasurableSpace Z := _root_.borel Z
  have : BorelSpace Z := ⟨rfl⟩
  set S : Set Z := closure (range i ∪ range j) with hSdef
  have hSsep : IsSeparable S :=
    ((isSeparable_range hi.continuous).union (isSeparable_range hj.continuous)).closure
  have : SeparableSpace S := hSsep.separableSpace
  have hSc : IsClosed S := isClosed_closure
  let κX : X → S := fun x ↦ ⟨i x, subset_closure (Or.inl ⟨x, rfl⟩)⟩
  let κY : Y → S := fun y ↦ ⟨j y, subset_closure (Or.inr ⟨y, rfl⟩)⟩
  have hκX : Isometry κX := Isometry.of_dist_eq fun x y ↦ hi.dist_eq x y
  have hκY : Isometry κY := Isometry.of_dist_eq fun x y ↦ hj.dist_eq x y
  have hX : X.blockLaw k = iidDistanceLawOn (X.law.map κX) k :=
    (iidDistanceLawOn_map_isometry _ _ hκX k).symm
  have hY : Y.blockLaw k = iidDistanceLawOn (Y.law.map κY) k :=
    (iidDistanceLawOn_map_isometry _ _ hκY k).symm
  rw [hX, hY]
  refine (levyProkhorovDist_iidDistanceLawOn_le _ _ k).trans ?_
  have hS : levyProkhorovDist ((X.law : Measure X).map κX) ((Y.law : Measure Y).map κY) ≤
      levyProkhorovDist ((X.law : Measure X).map i) ((Y.law : Measure Y).map j) := by
    have h := levyProkhorovEDist_le_map_subtype_val hSc ((X.law : Measure X).map κX)
      ((Y.law : Measure Y).map κY)
    rw [Measure.map_map measurable_subtype_coe hκX.continuous.measurable,
      Measure.map_map measurable_subtype_coe hκY.continuous.measurable] at h
    exact ENNReal.toReal_mono (levyProkhorovEDist_ne_top _ _) h
  have hk : (0 : ℝ) ≤ 2 * k := by positivity
  calc 2 * (k : ℝ) * levyProkhorovDist ((X.law.map κX : ProbabilityMeasure S) : Measure S)
        ((Y.law.map κY : ProbabilityMeasure S) : Measure S)
      ≤ 2 * k * levyProkhorovDist ((X.law : Measure X).map i) ((Y.law : Measure Y).map j) :=
        mul_le_mul_of_nonneg_left hS hk
    _ ≤ 2 * k * δ := mul_le_mul_of_nonneg_left hr.le hk

/-- The block law of order `k` is `2k`-Lipschitz from the GP distance to the
Lévy--Prokhorov distance. -/
theorem levyProkhorovDist_blockLaw_le (X Y : PolishMeasuredSpace.{u}) (k : ℕ) :
    levyProkhorovDist (X.blockLaw k : Measure (Fin k → Fin k → ℝ))
      (Y.blockLaw k : Measure (Fin k → Fin k → ℝ)) ≤ 2 * k * distance X Y := by
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := X.levyProkhorovDist_blockLaw_le_of_distance_lt Y k
    (lt_add_of_pos_right (distance X Y) (show 0 < η / (2 * k + 1) by positivity))
  have hsmall : 2 * (k : ℝ) * (η / (2 * k + 1)) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ 2 * k * (distance X Y + η / (2 * k + 1)) := h
    _ = 2 * k * distance X Y + 2 * k * (η / (2 * k + 1)) := by ring
    _ ≤ 2 * k * distance X Y + η := by linarith

end PolishMeasuredSpace

namespace GPSpace

/-- The block law of order `k` is `2k`-Lipschitz on the GP space. -/
theorem levyProkhorovDist_blockLaw_le (k : ℕ) (X Y : GPSpace.{u}) :
    levyProkhorovDist (blockLaw k X : Measure (Fin k → Fin k → ℝ))
      (blockLaw k Y : Measure (Fin k → Fin k → ℝ)) ≤ 2 * k * dist X Y := by
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact X.levyProkhorovDist_blockLaw_le Y k

/-- GP convergence implies convergence in distribution of each finite block. -/
theorem continuous_blockLaw (k : ℕ) : Continuous (blockLaw.{u} k) := by
  have hL : LipschitzWith (2 * k : ℝ≥0)
      (fun X : GPSpace.{u} ↦ LevyProkhorov.ofMeasure (blockLaw k X)) := by
    refine LipschitzWith.of_dist_le_mul fun X Y ↦ ?_
    rw [LevyProkhorov.dist_probabilityMeasure_def]
    push_cast
    exact levyProkhorovDist_blockLaw_le k X Y
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp hL.continuous

/-- GP convergence implies convergence in distribution of the matrix law. -/
theorem continuous_matrixLaw : Continuous matrixLaw.{u} := by
  rw [continuous_iff_continuousAt]
  intro X
  apply tendsto_of_forall_tendsto_map_arrayBlock
  intro k
  simp only [map_matrixLaw_arrayBlock]
  exact (continuous_blockLaw k).continuousAt

end GPSpace

section Empirical

/-- A finite family of disjoint cells of small diameter, and a remainder, bound
the Lévy--Prokhorov distance by the diameter, the discrepancies on the cells,
and the first mass of the remainder. -/
theorem levyProkhorovDist_le_cells {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (ν μ : Measure Ω) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] {k : ℕ} {A : Fin k → Set Ω} (hmeas : ∀ i, MeasurableSet (A i))
    (hbdd : ∀ i, Bornology.IsBounded (A i)) {ρ : ℝ} (hρ : 0 ≤ ρ) (hdiam : ∀ i, diam (A i) ≤ ρ)
    (hdisj : Pairwise fun i j ↦ Disjoint (A i) (A j)) {T : Set Ω}
    (hcover : ∀ x, x ∉ T → ∃ i, x ∈ A i) :
    levyProkhorovDist ν μ ≤ ρ + (∑ i, |ν.real (A i) - μ.real (A i)|) + ν.real T := by
  classical
  set S := ∑ i, |ν.real (A i) - μ.real (A i)|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hT : 0 ≤ ν.real T := measureReal_nonneg
  apply levyProkhorovDist_le_of_forall_le _ _ (by positivity)
  intro ε B hε hB
  let J := Finset.univ.filter fun i ↦ (A i ∩ B).Nonempty
  have hsub : B ⊆ (⋃ i ∈ J, A i) ∪ T := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Or.inr hxT
    · obtain ⟨i, hi⟩ := hcover x hxT
      exact Or.inl (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, x, hi, hx⟩, hi⟩)
  have hthick : (⋃ i ∈ J, A i) ⊆ thickening ε B := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    obtain ⟨z, hzi, hzB⟩ := (Finset.mem_filter.mp hi).2
    exact mem_thickening_iff.mpr ⟨z, hzB,
      (dist_le_diam_of_mem (hbdd i) hyi hzi).trans_lt (by linarith [hdiam i])⟩
  have hdisjJ : PairwiseDisjoint (↑J : Set (Fin k)) A := fun i _ j _ hij ↦ hdisj hij
  have h1 : ν.real B ≤ (∑ i ∈ J, ν.real (A i)) + ν.real T :=
    calc
      ν.real B ≤ ν.real ((⋃ i ∈ J, A i) ∪ T) := measureReal_mono hsub
      _ ≤ ν.real (⋃ i ∈ J, A i) + ν.real T := measureReal_union_le _ _
      _ ≤ _ := add_le_add (measureReal_biUnion_finset_le _ _) le_rfl
  have h2 : ∑ i ∈ J, ν.real (A i) ≤ ∑ i ∈ J, μ.real (A i) + S :=
    calc
      ∑ i ∈ J, ν.real (A i) ≤ ∑ i ∈ J, (μ.real (A i) + |ν.real (A i) - μ.real (A i)|) :=
        Finset.sum_le_sum fun i _ ↦ by linarith [le_abs_self (ν.real (A i) - μ.real (A i))]
      _ = ∑ i ∈ J, μ.real (A i) + ∑ i ∈ J, |ν.real (A i) - μ.real (A i)| :=
        Finset.sum_add_distrib
      _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) fun _ _ _ ↦ abs_nonneg _)
  have h3 : ∑ i ∈ J, μ.real (A i) ≤ μ.real (thickening ε B) := by
    rw [← measureReal_biUnion_finset hdisjJ fun i _ ↦ hmeas i]
    exact measureReal_mono hthick
  have hreal : ν.real B ≤ μ.real (thickening ε B) + ε := by linarith
  rw [← ofReal_measureReal (measure_ne_top ν B),
    ← ofReal_measureReal (measure_ne_top μ (thickening ε B)),
    ← ENNReal.ofReal_add measureReal_nonneg (by linarith)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The empirical measure of a finite tuple of points, with uniform weights. -/
noncomputable def tupleEmpirical {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (t : Fin (m + 1) → Ω) : Measure Ω :=
  (uniformIndexLaw m : Measure (Fin (m + 1))).map t

instance {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (t : Fin (m + 1) → Ω) :
    IsProbabilityMeasure (tupleEmpirical t) := by
  unfold tupleEmpirical
  infer_instance

theorem tupleEmpirical_real_apply {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (t : Fin (m + 1) → Ω) {A : Set Ω} (hA : MeasurableSet A) :
    (tupleEmpirical t).real A = ∑ i, A.indicator (fun _ ↦ (1 : ℝ) / (m + 1)) (t i) := by
  classical
  rw [measureReal_def, tupleEmpirical, Measure.map_apply (measurable_of_countable _) hA]
  change (Measure.uniformOfFinset (Finset.univ : Finset (Fin (m + 1))) _).toReal = _
  rw [Measure.uniformOfFinset_apply, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_div]
  simp only [Set.indicator_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_natCast, mem_preimage]
  push_cast
  ring

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem measurable_tupleEmpirical_real {m : ℕ} {A : Set Ω} (hA : MeasurableSet A) :
    Measurable fun t : Fin (m + 1) → Ω ↦ (tupleEmpirical t).real A := by
  simp_rw [tupleEmpirical_real_apply _ hA]
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_const.indicator hA).comp (measurable_pi_apply i)

theorem integrable_tupleEmpirical_real {m : ℕ} {A : Set Ω} (hA : MeasurableSet A)
    (P : Measure (Fin (m + 1) → Ω)) [IsProbabilityMeasure P] :
    Integrable (fun t ↦ (tupleEmpirical t).real A) P := by
  refine Integrable.of_bound (measurable_tupleEmpirical_real hA).aestronglyMeasurable 1
    (Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- The empirical frequency of a set is an unbiased estimator of its mass. -/
theorem integral_tupleEmpirical_real {m : ℕ} {A : Set Ω} (hA : MeasurableSet A) :
    ∫ t, (tupleEmpirical t).real A ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) = μ.real A := by
  have hg : Measurable (A.indicator fun _ : Ω ↦ (1 : ℝ) / (m + 1)) :=
    measurable_const.indicator hA
  have hi (i : Fin (m + 1)) : ∫ t, A.indicator (fun _ ↦ (1 : ℝ) / (m + 1)) (t i)
      ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) = μ.real A * (1 / (m + 1)) := by
    have h := integral_map (μ := Measure.pi fun _ : Fin (m + 1) ↦ μ)
      (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin (m + 1) ↦ μ) i).map_eq,
      integral_indicator_const _ hA, smul_eq_mul] at h
    exact h.symm
  simp_rw [tupleEmpirical_real_apply _ hA]
  rw [integral_finsetSum _ fun i _ ↦ ?_]
  · simp_rw [hi]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    push_cast
    ring
  · exact Integrable.of_bound (hg.comp (measurable_pi_apply i)).aestronglyMeasurable
      (1 / (m + 1)) (Eventually.of_forall fun t ↦ (norm_indicator_le_norm_self _ _).trans
        (le_of_eq (Real.norm_of_nonneg (by positivity))))

/-- The mean absolute deviation of an empirical frequency is at most `η` once
`(m+1) η² ≥ 1`, uniformly in the law and in the set. -/
theorem integral_abs_tupleEmpirical_sub_le {m : ℕ} {A : Set Ω} (hA : MeasurableSet A)
    {η : ℝ} (hη : 0 < η) (hm : 1 ≤ (m + 1) * η ^ 2) :
    ∫ t, |(tupleEmpirical t).real A - μ.real A| ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) ≤ η := by
  set P := Measure.pi fun _ : Fin (m + 1) ↦ μ with hP
  set p := μ.real A with hp
  set g : Ω → ℝ := A.indicator fun _ ↦ (1 : ℝ) / (m + 1) with hgdef
  have hg : Measurable g := measurable_const.indicator hA
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hgIcc : ∀ x, g x ∈ Icc (0 : ℝ) (1 / (m + 1)) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hgdef, Set.indicator_of_mem hx, mem_Icc, le_refl, and_true]
      positivity
    · simp only [hgdef, Set.indicator_of_notMem hx, mem_Icc, le_refl, true_and]
      positivity
  have hgL : MemLp g 2 μ := memLp_of_bounded (Eventually.of_forall hgIcc) hg.aestronglyMeasurable 2
  set Y : (Fin (m + 1) → Ω) → ℝ := ∑ i, fun t ↦ g (t i) with hYdef
  have hYeq : ∀ t, Y t = (tupleEmpirical t).real A := by
    intro t
    rw [tupleEmpirical_real_apply _ hA, hYdef, Finset.sum_apply]
  have hYm : Measurable Y := by
    rw [show Y = fun t ↦ (tupleEmpirical t).real A from funext hYeq]
    exact measurable_tupleEmpirical_real hA
  have hEY : ∫ t, Y t ∂P = p := by
    rw [show Y = fun t ↦ (tupleEmpirical t).real A from funext hYeq]
    exact integral_tupleEmpirical_real μ hA
  have hVar : variance Y P ≤ 1 / (4 * (m + 1)) := by
    rw [hYdef, variance_sum_pi fun _ ↦ hgL]
    have hv : variance g μ ≤ ((1 / (m + 1) - 0) / 2) ^ 2 :=
      variance_le_sq_of_bounded (Eventually.of_forall hgIcc) hg.aemeasurable
    calc ∑ _i : Fin (m + 1), variance g μ ≤
          ∑ _i : Fin (m + 1), ((1 / ((m : ℝ) + 1) - 0) / 2) ^ 2 :=
          Finset.sum_le_sum fun _ _ ↦ hv
      _ = 1 / (4 * (m + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          push_cast
          ring
  have hsq : ∫ t, (Y t - p) ^ 2 ∂P = variance Y P := by
    rw [variance_eq_integral hYm.aemeasurable, hEY]
  have hYIcc : ∀ t, Y t ∈ Icc (0 : ℝ) 1 := fun t ↦ by
    rw [hYeq]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hYL : MemLp Y 2 P := memLp_of_bounded (Eventually.of_forall hYIcc) hYm.aestronglyMeasurable 2
  have hsqi : Integrable (fun t ↦ (Y t - p) ^ 2) P := (hYL.sub (memLp_const p)).integrable_sq
  have hint : Integrable (fun t ↦ ((Y t - p) ^ 2 / η + η) / 2) P :=
    ((hsqi.div_const η).add (integrable_const η)).div_const 2
  have hpt : ∀ t, |Y t - p| ≤ ((Y t - p) ^ 2 / η + η) / 2 := by
    intro t
    have h := sq_nonneg (|Y t - p| - η)
    rw [sub_sq, sq_abs] at h
    rw [div_add' _ _ _ hη.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc ∫ t, |(tupleEmpirical t).real A - p| ∂P = ∫ t, |Y t - p| ∂P := by
        simp_rw [hYeq]
    _ ≤ ∫ t, ((Y t - p) ^ 2 / η + η) / 2 ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = (variance Y P / η + η) / 2 := by
        rw [integral_div, integral_add (hsqi.div_const η) (integrable_const η), integral_div,
          hsq, integral_const, probReal_univ, one_smul]
    _ ≤ (1 / (4 * (m + 1)) / η + η) / 2 := by gcongr
    _ ≤ η := by
        rw [div_le_iff₀ two_pos, div_div, div_add' _ _ _ (by positivity),
          div_le_iff₀ (by positivity)]
        nlinarith

end Moments

section Cells

variable {S : Type*} [MetricSpace S]

/-- The `i`-th cell of the covering by the `ε`-balls around the points `s j`:
the points of the ball around `s i` lying in no earlier ball. -/
def ballCell {k : ℕ} (s : Fin k → S) (ε : ℝ) (i : Fin k) : Set S :=
  ball (s i) ε ∩ ⋂ j, ⋂ (_ : j < i), (ball (s j) ε)ᶜ

/-- The points at distance at least `ε` from every `s i`. -/
def farSet {k : ℕ} (s : Fin k → S) (ε : ℝ) : Set S :=
  {x | ∀ i, ε ≤ dist x (s i)}

theorem measurableSet_ballCell [MeasurableSpace S] [OpensMeasurableSpace S] {k : ℕ}
    (s : Fin k → S) (ε : ℝ) (i : Fin k) : MeasurableSet (ballCell s ε i) :=
  measurableSet_ball.inter
    (MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦ measurableSet_ball.compl)

theorem isClosed_farSet {k : ℕ} (s : Fin k → S) (ε : ℝ) : IsClosed (farSet s ε) := by
  simp only [farSet, ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem isBounded_ballCell {k : ℕ} (s : Fin k → S) (ε : ℝ) (i : Fin k) :
    Bornology.IsBounded (ballCell s ε i) :=
  isBounded_ball.subset inter_subset_left

theorem diam_ballCell_le {k : ℕ} (s : Fin k → S) {ε : ℝ} (hε : 0 ≤ ε) (i : Fin k) :
    diam (ballCell s ε i) ≤ 2 * ε :=
  (diam_mono inter_subset_left isBounded_ball).trans (diam_ball hε)

theorem pairwise_disjoint_ballCell {k : ℕ} (s : Fin k → S) (ε : ℝ) :
    Pairwise fun i j ↦ Disjoint (ballCell s ε i) (ballCell s ε j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Set.disjoint_left.2 fun x hxi hxj ↦ (mem_iInter₂.1 hxj.2 i h) hxi.1
  · exact Set.disjoint_left.2 fun x hxi hxj ↦ (mem_iInter₂.1 hxi.2 j h) hxj.1

theorem exists_mem_ballCell {k : ℕ} (s : Fin k → S) {ε : ℝ} {x : S} (hx : x ∉ farSet s ε) :
    ∃ i, x ∈ ballCell s ε i := by
  classical
  simp only [farSet, mem_ofPred_eq, not_forall, not_le] at hx
  obtain ⟨i0, hi0⟩ := hx
  let F := Finset.univ.filter fun i ↦ dist x (s i) < ε
  have hF : F.Nonempty := ⟨i0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0⟩⟩
  refine ⟨F.min' hF, ?_, ?_⟩
  · exact mem_ball.2 (Finset.mem_filter.1 (F.min'_mem hF)).2
  · refine mem_iInter₂.2 fun j hj hxj ↦ ?_
    have hle : F.min' hF ≤ j :=
      F.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_ball.1 hxj⟩)
    exact absurd hj (not_lt.2 hle)

end Cells

section Uniform

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [SecondCountableTopology S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [SecondCountableTopology S] in
/-- For fixed centres `s`, the empirical measure of `m + 1` fresh iid points is
close to the law, in mean, up to the mass far from the centres. -/
theorem integral_le_of_le_levyProkhorovDist_of_centres {m k : ℕ} {ε η : ℝ} (hε : 0 < ε)
    (hη : 0 < η) (hm : 1 ≤ (m + 1) * η ^ 2) (F : (Fin (m + 1) → S) → ℝ)
    (hF0 : ∀ t, 0 ≤ F t) (hF : ∀ t, F t ≤ levyProkhorovDist (tupleEmpirical t) μ)
    (s : Fin k → S) :
    ∫ t, F t ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) ≤ 2 * ε + k * η + μ.real (farSet s ε) := by
  set P := Measure.pi fun _ : Fin (m + 1) ↦ μ with hP
  have hA := measurableSet_ballCell s ε
  have hT : MeasurableSet (farSet s ε) := (isClosed_farSet s ε).measurableSet
  have hiA : ∀ i, Integrable (fun t ↦
      |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)|) P :=
    fun i ↦ ((integrable_tupleEmpirical_real (hA i) P).sub (integrable_const _)).abs
  have hiS : Integrable (fun t ↦ ∑ i,
      |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)|) P :=
    integrable_finsetSum _ fun i _ ↦ hiA i
  have hiT := integrable_tupleEmpirical_real hT P
  have hGF : ∀ t, F t ≤ 2 * ε + (∑ i,
      |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)|) +
      (tupleEmpirical t).real (farSet s ε) := fun t ↦
    (hF t).trans (levyProkhorovDist_le_cells (tupleEmpirical t) μ hA (isBounded_ballCell s ε)
      (by positivity) (diam_ballCell_le s hε.le) (pairwise_disjoint_ballCell s ε)
      (fun x hx ↦ exists_mem_ballCell s hx))
  have hiCS : Integrable (fun t ↦ 2 * ε + ∑ i,
      |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)|) P :=
    (integrable_const _).add hiS
  have hiG : Integrable (fun t ↦ 2 * ε + (∑ i,
      |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)|) +
      (tupleEmpirical t).real (farSet s ε)) P := hiCS.add hiT
  calc ∫ t, F t ∂P ≤ ∫ t, (2 * ε + (∑ i,
        |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)|) +
        (tupleEmpirical t).real (farSet s ε)) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall hF0) hiG (Eventually.of_forall hGF)
    _ = 2 * ε + (∑ i, ∫ t,
        |(tupleEmpirical t).real (ballCell s ε i) - μ.real (ballCell s ε i)| ∂P) +
        ∫ t, (tupleEmpirical t).real (farSet s ε) ∂P := by
        rw [integral_add hiCS hiT, integral_add (integrable_const _) hiS,
          integral_const, probReal_univ, one_smul, integral_finsetSum _ fun i _ ↦ hiA i]
    _ ≤ 2 * ε + (∑ _i : Fin k, η) + μ.real (farSet s ε) := by
        rw [integral_tupleEmpirical_real μ hT]
        gcongr with i
        exact integral_abs_tupleEmpirical_sub_le μ (hA i) hη hm
    _ = 2 * ε + k * η + μ.real (farSet s ε) := by simp

theorem measurable_measure_farSet {k : ℕ} (ε : ℝ) :
    Measurable fun s : Fin k → S ↦ μ (farSet s ε) := by
  have hC : IsClosed {p : (Fin k → S) × S | ∀ i, ε ≤ dist p.2 (p.1 i)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const
      (continuous_snd.dist ((continuous_apply i).comp continuous_fst))
  exact measurable_measure_prodMk_left hC.measurableSet

/-- Uniform estimate for empirical measures: averaging the previous bound over
`k` iid centres. -/
theorem integral_le_of_le_levyProkhorovDist {m k : ℕ} {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (hm : 1 ≤ (m + 1) * η ^ 2) (F : (Fin (m + 1) → S) → ℝ) (hF0 : ∀ t, 0 ≤ F t)
    (hF : ∀ t, F t ≤ levyProkhorovDist (tupleEmpirical t) μ) :
    ∫ t, F t ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) ≤
      2 * ε + k * η + ∫ s, μ.real (farSet s ε) ∂(Measure.pi fun _ : Fin k ↦ μ) := by
  set Q := Measure.pi fun _ : Fin k ↦ μ with hQ
  have hTi : Integrable (fun s : Fin k → S ↦ μ.real (farSet s ε)) Q :=
    Integrable.of_bound (measurable_measure_farSet μ ε).ennreal_toReal.aestronglyMeasurable 1
      (Eventually.of_forall fun s ↦ by
        rw [Real.norm_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  calc ∫ t, F t ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) =
        ∫ _s, ∫ t, F t ∂(Measure.pi fun _ : Fin (m + 1) ↦ μ) ∂Q := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ ∫ s, (2 * ε + k * η + μ.real (farSet s ε)) ∂Q :=
        integral_mono (integrable_const _) ((integrable_const _).add hTi) fun s ↦
          integral_le_of_le_levyProkhorovDist_of_centres μ hε hη hm F hF0 hF s
    _ = 2 * ε + k * η + ∫ s, μ.real (farSet s ε) ∂Q := by
        rw [integral_add (integrable_const _) hTi, integral_const, probReal_univ, one_smul]

end Uniform

end Empirical

section FarFirst

/-- Square matrices of order `k + 1` whose first point is at distance at least
`ε` from the `k` other points. -/
def farFirstSet (k : ℕ) (ε : ℝ) : Set (Fin (k + 1) → Fin (k + 1) → ℝ) :=
  {M | ∀ i : Fin k, ε ≤ M 0 i.succ}

theorem isClosed_farFirstSet (k : ℕ) (ε : ℝ) : IsClosed (farFirstSet k ε) := by
  simp only [farFirstSet, ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const
    ((continuous_apply i.succ).comp (continuous_apply 0))

variable {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [SecondCountableTopology S]

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S] in
theorem isClosed_farPairs (k : ℕ) (ε : ℝ) :
    IsClosed {p : S × (Fin k → S) | ∀ i, ε ≤ dist p.1 (p.2 i)} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const
    (continuous_fst.dist ((continuous_apply i).comp continuous_snd))

/-- The probability that the first point is `ε`-far from `k` further iid points. -/
theorem iidDistanceLawOn_farFirstSet (μ : ProbabilityMeasure S) (k : ℕ) (ε : ℝ) :
    (iidDistanceLawOn μ (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) (farFirstSet k ε) =
      ((μ : Measure S).prod (Measure.pi fun _ : Fin k ↦ (μ : Measure S)))
        {p | ∀ i, ε ≤ dist p.1 (p.2 i)} := by
  change ((Measure.pi fun _ : Fin (k + 1) ↦ (μ : Measure S)).map (distanceMatrix (k + 1)))
    (farFirstSet k ε) = _
  rw [Measure.map_apply (continuous_distanceMatrix _).measurable
    (isClosed_farFirstSet k ε).measurableSet]
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ (μ : Measure S)) 0
  rw [← he.measure_preimage (isClosed_farPairs k ε).measurableSet.nullMeasurableSet]
  congr 1

/-- The mean far mass of `k` iid centres is a closed-set probability of the
`(k+1)`-block law. -/
theorem integral_measureReal_farSet_eq (μ : ProbabilityMeasure S) (k : ℕ) (ε : ℝ) :
    ∫ s, (μ : Measure S).real (farSet s ε) ∂(Measure.pi fun _ : Fin k ↦ (μ : Measure S)) =
      ((iidDistanceLawOn μ (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
        (farFirstSet k ε)).toReal := by
  rw [iidDistanceLawOn_farFirstSet, Measure.prod_apply_symm (isClosed_farPairs k ε).measurableSet]
  exact integral_toReal (measurable_measure_farSet (μ : Measure S) ε).aemeasurable
    (Eventually.of_forall fun _ ↦ measure_lt_top _ _)

/-- For a fixed law, the probability that the first point is `ε`-far from `k`
further iid points tends to zero: almost every point lies in the support. -/
theorem tendsto_iidDistanceLawOn_farFirstSet (μ : ProbabilityMeasure S) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k ↦ (iidDistanceLawOn μ (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
      (farFirstSet k ε)) atTop (𝓝 0) := by
  set ν := (μ : Measure S) with hν
  have hC : IsClosed {p : S × S | ε ≤ dist p.1 p.2} := isClosed_le continuous_const continuous_dist
  have hf : Measurable fun x : S ↦ ν {y | ε ≤ dist x y} :=
    measurable_measure_prodMk_left hC.measurableSet
  have heq : ∀ k, (iidDistanceLawOn μ (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
      (farFirstSet k ε) = ∫⁻ x, ν {y | ε ≤ dist x y} ^ k ∂ν := by
    intro k
    rw [iidDistanceLawOn_farFirstSet, Measure.prod_apply (isClosed_farPairs k ε).measurableSet]
    refine lintegral_congr fun x ↦ ?_
    have hpi : Prod.mk x ⁻¹' {p : S × (Fin k → S) | ∀ i, ε ≤ dist p.1 (p.2 i)} =
        Set.pi univ fun _ ↦ {y | ε ≤ dist x y} := by
      ext s
      simp
    rw [hpi, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [heq]
  have h := tendsto_lintegral_of_dominated_convergence (μ := ν) (f := fun _ ↦ 0) (fun _ ↦ 1)
    (fun k ↦ hf.pow_const k)
    (fun k ↦ Eventually.of_forall fun x ↦ pow_le_one₀ bot_le prob_le_one) (by simp) ?_
  · rwa [lintegral_zero] at h
  filter_upwards [Measure.support_mem_ae (μ := ν)] with x hx
  have hpos : 0 < ν (ball x ε) := (Measure.mem_support_iff_forall x).1 hx _ (ball_mem_nhds x hε)
  have hcompl : {y | ε ≤ dist x y} = (ball x ε)ᶜ := by
    ext y
    simp [dist_comm]
  have hlt : ν {y | ε ≤ dist x y} < 1 := by
    rw [hcompl, prob_compl_eq_one_sub measurableSet_ball]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt

end FarFirst

/-- The GP class of the finite space reconstructed from an `(m+1) × (m+1)`
matrix: its rows with uniform weights. -/
noncomputable def gpMatrixSpace (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → ℝ) : GPSpace.{u} :=
  MeasuredGHSpace.gpProjection (matrixSpace.{u} m M)

theorem continuous_gpMatrixSpace (m : ℕ) : Continuous (gpMatrixSpace.{u} m) :=
  MeasuredGHSpace.continuous_gpProjection.comp (continuous_matrixSpace m)

namespace PolishMeasuredSpace

/-- The reconstruction of a sampled distance matrix is GP-close to the space:
its distance is at most the Lévy--Prokhorov distance from the empirical measure
of the sample to the law. Neither compactness nor full support is needed. -/
theorem dist_gpMatrixSpace_le (X : PolishMeasuredSpace.{u}) {m : ℕ} (t : Fin (m + 1) → X) :
    dist (toGPSpace X) (gpMatrixSpace.{u} m (distanceMatrix (m + 1) t)) ≤
      levyProkhorovDist (tupleEmpirical t) (X.law : Measure X) := by
  classical
  let M := distanceMatrix (m + 1) t
  have hrow (l : Fin (m + 1)) (r : range M) (h : (r : Fin (m + 1) → ℝ) = M l) :
      t (Classical.choose r.2) = t l := by
    have hc := Classical.choose_spec r.2
    have h0 : dist (M (Classical.choose r.2)) (M l) = 0 := by rw [hc, h, dist_self]
    rw [dist_distanceMatrix_row] at h0
    exact dist_eq_zero.mp h0
  let i : (rowSpace.{u} m M) → X := fun x ↦ t (Classical.choose x.down.2)
  have hi_row (l : Fin (m + 1)) : i (RowSpace.rowPoint M l) = t l := hrow l _ rfl
  have hi : Isometry i := by
    apply Isometry.of_dist_eq
    intro x y
    obtain ⟨l, rfl⟩ := RowSpace.rowPoint_surjective M x
    obtain ⟨l', rfl⟩ := RowSpace.rowPoint_surjective M y
    rw [hi_row, hi_row]
    exact (dist_distanceMatrix_row t l l').symm
  have hmap : ((rowSpace.{u} m M).law : Measure (rowSpace.{u} m M)).map i = tupleEmpirical t := by
    rw [rowSpace_map_law m M i hi.continuous.measurable]
    unfold tupleEmpirical
    congr 1
    funext l
    exact hi_row l
  rw [gpMatrixSpace, matrixSpace, MeasuredGHSpace.gpProjection_toMeasuredGHSpace,
    GPSpace.dist_toGPSpace, distance_comm]
  have h := gpDistance_le_of_isometries_of_borelSpace
    ((rowSpace.{u} m M).law : Measure (rowSpace.{u} m M)) (X.law : Measure X) X i id hi
    isometry_id
  rwa [hmap, Measure.map_id] at h

/-- **Uniform empirical estimate.** The mean GP distance from a space to the
reconstruction of `m + 1` iid samples is bounded through any number `k` of
auxiliary centres and a scale `ε`, by a quantity read off the `(k+1)`-block
law. The bound is uniform over all Polish measured spaces. -/
theorem integral_dist_gpMatrixSpace_le (X : PolishMeasuredSpace.{u}) {m k : ℕ} {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (hm : 1 ≤ (m + 1) * η ^ 2) :
    ∫ M, dist (toGPSpace X) (gpMatrixSpace.{u} m M)
        ∂(X.blockLaw (m + 1) : Measure (Fin (m + 1) → Fin (m + 1) → ℝ)) ≤
      2 * ε + k * η +
        ((X.blockLaw (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
          (farFirstSet k ε)).toReal := by
  have hc : Continuous fun M ↦ dist (toGPSpace X) (gpMatrixSpace.{u} m M) :=
    continuous_const.dist (continuous_gpMatrixSpace m)
  change ∫ M, _ ∂((Measure.pi fun _ : Fin (m + 1) ↦ (X.law : Measure X)).map
    (distanceMatrix (m + 1))) ≤ _
  rw [integral_map (continuous_distanceMatrix (m + 1)).measurable.aemeasurable
    hc.aestronglyMeasurable]
  refine (integral_le_of_le_levyProkhorovDist (X.law : Measure X) (k := k) hε hη hm _
    (fun _ ↦ dist_nonneg) (fun t ↦ X.dist_gpMatrixSpace_le t)).trans_eq ?_
  rw [blockLaw, integral_measureReal_farSet_eq]

/-- GP distances are at most one. -/
theorem distance_le_one (X Y : PolishMeasuredSpace.{u}) : distance X Y ≤ 1 := by
  let : MetricSpace (X ⊕ Y) := metricSpaceSum
  let : MeasurableSpace (X ⊕ Y) := _root_.borel (X ⊕ Y)
  have : BorelSpace (X ⊕ Y) := ⟨rfl⟩
  refine (gpDistance_le_of_isometries_of_borelSpace (X.law : Measure X) (Y.law : Measure Y)
    (X ⊕ Y) Sum.inl Sum.inr (Isometry.of_dist_eq fun _ _ ↦ rfl)
    (Isometry.of_dist_eq fun _ _ ↦ rfl)).trans ?_
  have h := levyProkhorovEDist_le_max_measure_univ ((X.law : Measure X).map Sum.inl)
    ((Y.law : Measure Y).map Sum.inr)
  simp only [measure_univ, max_self] at h
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (h.trans ENNReal.ofReal_one.ge)

end PolishMeasuredSpace

namespace GPSpace

/-- GP distances are at most one. -/
theorem dist_le_one (X Y : GPSpace.{u}) : dist X Y ≤ 1 := by
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact X.distance_le_one Y

/-- The GP distance from a fixed class to the reconstruction of a matrix, as a
bounded continuous test function on matrices. -/
noncomputable def distToMatrixSpace (Z : GPSpace.{u}) (m : ℕ) :
    (Fin (m + 1) → Fin (m + 1) → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun M ↦ dist Z (gpMatrixSpace.{u} m M), continuous_const.dist (continuous_gpMatrixSpace m)⟩
    1 fun M M' ↦ by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := dist_le_one Z (gpMatrixSpace.{u} m M)
      have h2 := dist_le_one Z (gpMatrixSpace.{u} m M')
      have h3 := dist_nonneg (x := Z) (y := gpMatrixSpace.{u} m M)
      have h4 := dist_nonneg (x := Z) (y := gpMatrixSpace.{u} m M')
      rw [abs_le]
      constructor <;> linarith

@[simp] theorem distToMatrixSpace_apply (Z : GPSpace.{u}) (m : ℕ)
    (M : Fin (m + 1) → Fin (m + 1) → ℝ) :
    distToMatrixSpace Z m M = dist Z (gpMatrixSpace.{u} m M) := rfl

/-- **Converse half of Lemma `equivGP`.** Convergence in distribution of every
finite block of the sampled distance matrices implies GP convergence. The
limit is compared directly with reconstructions from finitely many samples,
through the uniform empirical estimate; no compactness argument is needed. -/
theorem tendsto_of_forall_tendsto_blockLaw {ι : Type*} {L : Filter ι} {X : ι → GPSpace.{u}}
    {Y : GPSpace.{u}} (h : ∀ k, Tendsto (fun i ↦ blockLaw k (X i)) L (𝓝 (blockLaw k Y))) :
    Tendsto X L (𝓝 Y) := by
  rw [Metric.tendsto_nhds]
  intro τ hτ
  obtain ⟨Y₀, rfl⟩ : ∃ Y₀ : PolishMeasuredSpace.{u}, toGPSpace Y₀ = Y :=
    ⟨Quotient.out Y, Quotient.out_eq Y⟩
  set ε := τ / 16 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨k, hk⟩ := ((tendsto_iidDistanceLawOn_farFirstSet Y₀.law hε).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (show 0 < τ / 16 by positivity)))).exists
  have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (h (k + 1))
    (isClosed_farFirstSet k ε)
  have hev : ∀ᶠ i in L, (blockLaw (k + 1) (X i) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
      (farFirstSet k ε) < ENNReal.ofReal (τ / 16) :=
    eventually_lt_of_limsup_lt (hlimsup.trans_lt hk)
  set η := τ / (16 * (k + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 ≤ (m + 1) * η ^ 2 := by
    obtain ⟨m, hm⟩ := exists_nat_ge (1 / η ^ 2)
    refine ⟨m, ?_⟩
    rw [div_le_iff₀ (by positivity)] at hm
    nlinarith [sq_nonneg η]
  have hkη : (k : ℝ) * η ≤ τ / 16 := by
    rw [hηdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hbound : ∀ Z : PolishMeasuredSpace.{u},
      (Z.blockLaw (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) (farFirstSet k ε) <
        ENNReal.ofReal (τ / 16) →
      ∫ M, dist (toGPSpace Z) (gpMatrixSpace.{u} m M)
        ∂(Z.blockLaw (m + 1) : Measure (Fin (m + 1) → Fin (m + 1) → ℝ)) < τ / 4 := by
    intro Z hZ
    have h1 := Z.integral_dist_gpMatrixSpace_le (k := k) hε hη hm
    have h2 := ENNReal.toReal_lt_of_lt_ofReal hZ
    linarith
  set f := distToMatrixSpace (toGPSpace Y₀) m with hf
  have hconv := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (h (m + 1)) f
  have hY : ∫ M, f M ∂(blockLaw (m + 1) (toGPSpace Y₀) :
      Measure (Fin (m + 1) → Fin (m + 1) → ℝ)) < τ / 4 := hbound Y₀ hk
  have hev2 : ∀ᶠ i in L, ∫ M, f M ∂(blockLaw (m + 1) (X i) :
      Measure (Fin (m + 1) → Fin (m + 1) → ℝ)) < τ / 2 :=
    hconv.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev, hev2] with i hi1 hi2
  obtain ⟨Xi, hXi⟩ : ∃ Xi : PolishMeasuredSpace.{u}, toGPSpace Xi = X i :=
    ⟨Quotient.out (X i), Quotient.out_eq (X i)⟩
  rw [← hXi] at hi1 hi2 ⊢
  have hE := hbound Xi hi1
  set P := (Xi.blockLaw (m + 1) : Measure (Fin (m + 1) → Fin (m + 1) → ℝ)) with hP
  have hia : Integrable (fun M ↦ dist (toGPSpace Xi) (gpMatrixSpace.{u} m M)) P :=
    (distToMatrixSpace (toGPSpace Xi) m).integrable P
  have hib : Integrable (fun M ↦ f M) P := f.integrable P
  calc dist (toGPSpace Xi) (toGPSpace Y₀) = ∫ _M, dist (toGPSpace Xi) (toGPSpace Y₀) ∂P := by
        rw [integral_const, probReal_univ, one_smul]
    _ ≤ ∫ M, (dist (toGPSpace Xi) (gpMatrixSpace.{u} m M) + f M) ∂P :=
        integral_mono (integrable_const _) (hia.add hib) fun M ↦ by
          rw [hf, distToMatrixSpace_apply, dist_comm (toGPSpace Y₀)]
          exact dist_triangle _ _ _
    _ = ∫ M, dist (toGPSpace Xi) (gpMatrixSpace.{u} m M) ∂P + ∫ M, f M ∂P :=
        integral_add hia hib
    _ < τ / 4 + τ / 2 := add_lt_add hE hi2
    _ < τ := by linarith

/-- GP convergence is equivalent to convergence in distribution of every finite
block of the sampled distance matrices. -/
theorem tendsto_iff_forall_tendsto_blockLaw {ι : Type*} {L : Filter ι} {X : ι → GPSpace.{u}}
    {Y : GPSpace.{u}} :
    Tendsto X L (𝓝 Y) ↔ ∀ k, Tendsto (fun i ↦ blockLaw k (X i)) L (𝓝 (blockLaw k Y)) :=
  ⟨fun h k ↦ ((continuous_blockLaw k).tendsto Y).comp h, tendsto_of_forall_tendsto_blockLaw⟩

/-- GP convergence is equivalent to convergence in distribution of the matrix laws
on `ℕ → ℕ → ℝ`, along any countably generated filter. -/
theorem tendsto_iff_tendsto_matrixLaw {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {X : ι → GPSpace.{u}} {Y : GPSpace.{u}} :
    Tendsto X L (𝓝 Y) ↔ Tendsto (fun i ↦ matrixLaw (X i)) L (𝓝 (matrixLaw Y)) := by
  rw [tendsto_matrixLaw_iff_forall_tendsto_blockLaw, tendsto_iff_forall_tendsto_blockLaw]

/-- **Lemma `equivGP`** (cited from Löhr 2013). For `Xⁿ, X ∈ 𝕂_GP`, `Xⁿ → X` in
the GP topology if and only if the sampled distance matrices `M^{Xⁿ}` converge in
distribution to `M^X`. -/
theorem equivGP (X : ℕ → GPSpace.{u}) (Y : GPSpace.{u}) :
    Tendsto X atTop (𝓝 Y) ↔ Tendsto (fun n ↦ matrixLaw (X n)) atTop (𝓝 (matrixLaw Y)) :=
  tendsto_iff_tendsto_matrixLaw

/-- Gromov's reconstruction theorem for Polish measured spaces: the law of the
sampled distance matrix determines the GP class. -/
theorem matrixLaw_injective : Function.Injective matrixLaw.{u} := by
  intro X Y hXY
  have h : Tendsto (fun _ : ℕ ↦ X) atTop (𝓝 Y) :=
    tendsto_iff_tendsto_matrixLaw.2 (by rw [hXY]; exact tendsto_const_nhds)
  exact tendsto_nhds_unique tendsto_const_nhds h

/-- The GP topology is the topology induced by the law of the sampled distance
matrix: `X ↦ law of M^X` is a topological embedding of `𝕂_GP` into the
probability measures on `ℕ → ℕ → ℝ`. -/
theorem isEmbedding_matrixLaw : Topology.IsEmbedding matrixLaw.{u} := by
  refine ⟨Topology.isInducing_iff_nhds.2 fun X ↦ le_antisymm
    (continuous_matrixLaw.tendsto X).le_comap ?_, matrixLaw_injective⟩
  have h : Tendsto id (Filter.comap matrixLaw (𝓝 (matrixLaw X))) (𝓝 X) := by
    refine tendsto_of_forall_tendsto_blockLaw fun k ↦ ?_
    simp only [id, ← map_matrixLaw_arrayBlock]
    exact ((ProbabilityMeasure.continuous_map (continuous_arrayBlock k)).tendsto
      (matrixLaw X)).comp tendsto_comap
  exact h

/-- The GP projection of a compact measured space has the sampled-distance laws
of `SampledDistanceLaw`. -/
theorem blockLaw_gpProjection (k : ℕ) (X : MeasuredGHSpace.{u}) :
    blockLaw k (MeasuredGHSpace.gpProjection X) = MeasuredGHSpace.sampledDistanceLaw k X := by
  induction X using Quotient.inductionOn with
  | _ X => rfl

end GPSpace

end Freezing2
