module

public import Freezing2.Probability.AnnealedSampling
public import Freezing2.Probability.GHTightCriterion
public import Freezing2.Probability.GHPTightness

/-!
# Tightness in the leaf-tightness criterion

First half of Proposition `C.1`. A covering radius at most `δ` for some sample
gives a cover by `k + 1` balls of radius `2δ`; together with a bound on the
sampled distances it also bounds the diameter. Markov's inequality transfers
these deterministic facts to the annealed laws. Leaf-tightness controls the
covering numbers, and convergence of the sampled matrices controls the largest
sampled distance, so the GH tightness criterion and the GHP compact-preimage
property give tightness of the laws of the random measured spaces.
-/

@[expose] public section

open Filter MeasureTheory Set Metric Topology GromovHausdorff
open scoped ENNReal NNReal

universe u

namespace Freezing2

open GHCovering

/-- The sampled matrix has an entry larger than `t`. -/
def matrixExceeds (k : ℕ) (t : ℝ) : Set (Fin k → Fin k → ℝ) := {m | ∃ i j, t < m i j}

theorem isOpen_matrixExceeds (k : ℕ) (t : ℝ) : IsOpen (matrixExceeds k t) := by
  have he : matrixExceeds k t = ⋃ i, ⋃ j, {m : Fin k → Fin k → ℝ | t < m i j} := by
    ext m
    simp [matrixExceeds]
  rw [he]
  exact isOpen_iUnion fun i ↦ isOpen_iUnion fun j ↦
    isOpen_lt continuous_const ((continuous_apply j).comp (continuous_apply i))

namespace CompactMeasuredSpace

variable (X : CompactMeasuredSpace.{u})

theorem measurable_sampleCoverRadius (k : ℕ) :
    Measurable (sampleCoverRadiusOn (fullCarrierCompact X) k) :=
  ((continuous_sampleCoverRadiusOn (X := X) k).comp
    (continuous_const.prodMk continuous_id)).measurable

theorem iidCoverRadiusLaw_apply (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    (iidCoverRadiusLaw X k : Measure ℝ) s =
      (ProbabilityMeasure.pi (fun _ : Fin (k + 1) ↦ X.law) : Measure (Fin (k + 1) → X))
        (sampleCoverRadiusOn (fullCarrierCompact X) k ⁻¹' s) := by
  rw [iidCoverRadiusLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_sampleCoverRadius X k) hs]

theorem iidDistanceLaw_apply (k : ℕ) {s : Set (Fin k → Fin k → ℝ)} (hs : MeasurableSet s) :
    (iidDistanceLaw X k : Measure (Fin k → Fin k → ℝ)) s =
      (ProbabilityMeasure.pi (fun _ : Fin k ↦ X.law) : Measure (Fin k → X))
        (distanceMatrix k ⁻¹' s) := by
  rw [iidDistanceLaw, iidDistanceLawOn, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (continuous_distanceMatrix k).measurable hs]

/-- A sample within Hausdorff distance `δ` of the whole carrier. -/
theorem exists_dist_le_of_sampleCoverRadius_le {k : ℕ} {v : Fin (k + 1) → X} {δ : ℝ}
    (hv : sampleCoverRadiusOn (fullCarrierCompact X) k v ≤ δ) (x : X) :
    ∃ i, dist x (v i) ≤ δ := by
  have hfin : hausdorffEDist (univ : Set X) (range v) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded univ_nonempty (range_nonempty v)
      isBounded_of_compactSpace (finite_range v).isCompact.isBounded
  have hH : hausdorffDist (univ : Set X) (range v) ≤ δ := by
    change dist (fullCarrierCompact X) (finiteSampleRange k v) ≤ δ at hv
    rwa [TopologicalSpace.NonemptyCompacts.dist_eq] at hv
  obtain ⟨y, ⟨i, rfl⟩, hy⟩ := (finite_range v).isCompact.exists_infDist_eq_dist
    (range_nonempty v) x
  exact ⟨i, hy ▸ (infDist_le_hausdorffDist_of_mem (mem_univ x) hfin).trans hH⟩

/-- Positive probability of a covering radius at most `δ` gives a cover by
`k + 1` open balls of radius `2δ`. -/
theorem coverable_of_iidCoverRadiusLaw_lt_one (k : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (h : (iidCoverRadiusLaw X k : Measure ℝ) (Ioi δ) < 1) :
    Coverable X (k + 1) (2 * δ) := by
  classical
  rw [iidCoverRadiusLaw_apply X k measurableSet_Ioi] at h
  have hne : (sampleCoverRadiusOn (fullCarrierCompact X) k ⁻¹' Ioi δ)ᶜ.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    rw [hemp, measure_univ] at h
    exact lt_irrefl _ h
  obtain ⟨v, hv⟩ := hne
  simp only [mem_compl_iff, mem_preimage, mem_Ioi, not_lt] at hv
  refine ⟨Finset.univ.image v, Finset.card_image_le.trans (by simp), fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := exists_dist_le_of_sampleCoverRadius_le X hv x
  exact ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i), by linarith⟩

/-- A large diameter forces either a large covering radius or a large sampled
distance, for the same `k + 1` samples. -/
theorem one_le_coverRadius_add_matrixExceeds (k : ℕ) {δ D : ℝ}
    (hD : D < diam (univ : Set X)) :
    1 ≤ (iidCoverRadiusLaw X k : Measure ℝ) (Ioi δ) +
      (iidDistanceLaw X (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
        (matrixExceeds (k + 1) (D - 2 * δ)) := by
  rw [iidCoverRadiusLaw_apply X k measurableSet_Ioi,
    iidDistanceLaw_apply X (k + 1) (isOpen_matrixExceeds _ _).measurableSet]
  let μ := (ProbabilityMeasure.pi (fun _ : Fin (k + 1) ↦ X.law) : Measure (Fin (k + 1) → X))
  have hcover : (univ : Set (Fin (k + 1) → X)) ⊆
      sampleCoverRadiusOn (fullCarrierCompact X) k ⁻¹' Ioi δ ∪
        distanceMatrix (k + 1) ⁻¹' matrixExceeds (k + 1) (D - 2 * δ) := by
    intro v _
    by_contra hv
    simp only [mem_union, mem_preimage, mem_Ioi, not_or, not_lt, matrixExceeds,
      mem_ofPred_eq, not_exists, distanceMatrix] at hv
    obtain ⟨hr, hd⟩ := hv
    have hdist (x y : X) : dist x y ≤ D := by
      obtain ⟨i, hi⟩ := exists_dist_le_of_sampleCoverRadius_le X hr x
      obtain ⟨j, hj⟩ := exists_dist_le_of_sampleCoverRadius_le X hr y
      calc
        dist x y ≤ dist x (v i) + dist (v i) (v j) + dist (v j) y := dist_triangle4 _ _ _ _
        _ ≤ δ + (D - 2 * δ) + δ := by
          have := dist_comm (v j) y
          linarith [hd i j]
        _ = D := by ring
    have hD0 : 0 ≤ D := (dist_self (Classical.arbitrary X)).symm.le.trans
      (hdist (Classical.arbitrary X) (Classical.arbitrary X))
    exact (not_lt_of_ge (diam_le_of_forall_dist_le hD0 fun x _ y _ ↦ hdist x y)) hD
  calc
    (1 : ℝ≥0∞) = μ univ := measure_univ.symm
    _ ≤ _ := (measure_mono hcover).trans (measure_union_le _ _)

end CompactMeasuredSpace

namespace MeasuredGHSpace

theorem measurable_sampledCoverRadiusLaw_apply (k : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable (fun X : MeasuredGHSpace.{u} ↦ (sampledCoverRadiusLaw k X : Measure ℝ) s) :=
  (Measure.measurable_coe hs).comp
    (measurable_toMeasure_of_continuous (continuous_sampledCoverRadiusLaw k))

theorem measurable_sampledDistanceLaw_apply (k : ℕ) {s : Set (Fin k → Fin k → ℝ)}
    (hs : MeasurableSet s) :
    Measurable (fun X : MeasuredGHSpace.{u} ↦
      (sampledDistanceLaw k X : Measure (Fin k → Fin k → ℝ)) s) :=
  (Measure.measurable_coe hs).comp
    (measurable_toMeasure_of_continuous (continuous_sampledDistanceLaw k))

theorem coverable_of_sampledCoverRadiusLaw_lt_one (k : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (X : MeasuredGHSpace.{u}) (h : (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi δ) < 1) :
    Coverable (underlyingGH X).Rep (k + 1) (2 * δ) := by
  induction X using Quotient.inductionOn with
  | _ X =>
    change Coverable (toGHSpace X).Rep (k + 1) (2 * δ)
    rw [coverable_toGHSpace_rep_iff]
    exact X.coverable_of_iidCoverRadiusLaw_lt_one k hδ h

theorem one_le_of_lt_diam (k : ℕ) {δ D : ℝ} (X : MeasuredGHSpace.{u})
    (hD : D < diam (univ : Set (underlyingGH X).Rep)) :
    1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi δ) +
      (sampledDistanceLaw (k + 1) X : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
        (matrixExceeds (k + 1) (D - 2 * δ)) := by
  induction X using Quotient.inductionOn with
  | _ X =>
    change D < diam (univ : Set (toGHSpace X).Rep) at hD
    rw [diam_toGHSpace_rep] at hD
    exact X.one_le_coverRadius_add_matrixExceeds k hD

/-- Markov bound for covering numbers. -/
theorem measure_not_coverable_le (P : ProbabilityMeasure MeasuredGHSpace.{u}) (k : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    (P : Measure MeasuredGHSpace.{u})
      {X | ¬ Coverable (underlyingGH X).Rep (k + 1) (2 * δ)} ≤
      (annealedCoverRadiusLaw P k : Measure ℝ) (Ioi δ) := by
  have hsub : {X : MeasuredGHSpace.{u} | ¬ Coverable (underlyingGH X).Rep (k + 1) (2 * δ)} ⊆
      {X | 1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi δ)} := fun X hX ↦ by
    by_contra h
    exact hX (coverable_of_sampledCoverRadiusLaw_lt_one k hδ X (not_le.mp h))
  rw [annealedCoverRadiusLaw, continuousMixture_apply _ _ measurableSet_Ioi]
  calc
    _ ≤ (P : Measure MeasuredGHSpace.{u})
          {X | 1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi δ)} := measure_mono hsub
    _ = 1 * (P : Measure MeasuredGHSpace.{u})
          {X | 1 ≤ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi δ)} := (one_mul _).symm
    _ ≤ _ := mul_meas_ge_le_lintegral₀
        (measurable_sampledCoverRadiusLaw_apply k measurableSet_Ioi).aemeasurable 1

/-- Markov bound for diameters. -/
theorem measure_lt_diam_le (P : ProbabilityMeasure MeasuredGHSpace.{u}) (k : ℕ) (δ D : ℝ) :
    (P : Measure MeasuredGHSpace.{u}) {X | D < diam (univ : Set (underlyingGH X).Rep)} ≤
      (annealedCoverRadiusLaw P k : Measure ℝ) (Ioi δ) +
        (annealedDistanceLaw P (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
          (matrixExceeds (k + 1) (D - 2 * δ)) := by
  have hE := (isOpen_matrixExceeds (k + 1) (D - 2 * δ)).measurableSet
  let f : MeasuredGHSpace.{u} → ℝ≥0∞ := fun X ↦ (sampledCoverRadiusLaw k X : Measure ℝ) (Ioi δ) +
    (sampledDistanceLaw (k + 1) X : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
      (matrixExceeds (k + 1) (D - 2 * δ))
  have hf : Measurable f := (measurable_sampledCoverRadiusLaw_apply k measurableSet_Ioi).add
    (measurable_sampledDistanceLaw_apply (k + 1) hE)
  rw [annealedCoverRadiusLaw, annealedDistanceLaw, continuousMixture_apply _ _ measurableSet_Ioi,
    continuousMixture_apply _ _ hE, ← lintegral_add_left
      (measurable_sampledCoverRadiusLaw_apply k measurableSet_Ioi)]
  calc
    _ ≤ (P : Measure MeasuredGHSpace.{u}) {X | 1 ≤ f X} :=
      measure_mono fun X hX ↦ one_le_of_lt_diam k X hX
    _ = 1 * (P : Measure MeasuredGHSpace.{u}) {X | 1 ≤ f X} := (one_mul _).symm
    _ ≤ ∫⁻ X, f X ∂(P : Measure MeasuredGHSpace.{u}) :=
      mul_meas_ge_le_lintegral₀ hf.aemeasurable 1

end MeasuredGHSpace

end Freezing2

namespace Freezing2

open GHCovering

/-- Some sampled distance is at least `t`. -/
def matrixAtLeast (k : ℕ) (t : ℝ) : Set (Fin k → Fin k → ℝ) := {m | ∃ i j, t ≤ m i j}

theorem isClosed_matrixAtLeast (k : ℕ) (t : ℝ) : IsClosed (matrixAtLeast k t) := by
  have he : matrixAtLeast k t = ⋃ i, ⋃ j, {m : Fin k → Fin k → ℝ | t ≤ m i j} := by
    ext m
    simp [matrixAtLeast]
  rw [he]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_iUnion_of_finite fun j ↦
    isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))

theorem matrixExceeds_subset_matrixAtLeast (k : ℕ) (t : ℝ) :
    matrixExceeds k t ⊆ matrixAtLeast k t := fun _ ⟨i, j, h⟩ ↦ ⟨i, j, h.le⟩

/-- A single finite law gives small probability to a large sampled entry. -/
theorem tendsto_measure_matrixAtLeast (k : ℕ) (μ : Measure (Fin k → Fin k → ℝ))
    [IsFiniteMeasure μ] : Tendsto (fun t : ℕ ↦ μ (matrixAtLeast k t)) atTop (𝓝 0) := by
  have hanti : Antitone (fun t : ℕ ↦ matrixAtLeast k t) := fun a b hab m ⟨i, j, h⟩ ↦
    ⟨i, j, le_trans (by exact_mod_cast hab) h⟩
  have hempty : ⋂ t : ℕ, matrixAtLeast k t = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨t, ht⟩ := exists_nat_gt (∑ i, ∑ j, |m i j|)
    obtain ⟨i, j, hij⟩ := mem_iInter.mp hm t
    have h1 : |m i j| ≤ ∑ j', |m i j'| :=
      Finset.single_le_sum (f := fun j' ↦ |m i j'|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j', |m i j'| ≤ ∑ i', ∑ j', |m i' j'| :=
      Finset.single_le_sum (f := fun i' ↦ ∑ j', |m i' j'|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
    linarith [le_abs_self (m i j)]
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun t : ℕ ↦ matrixAtLeast k t)
    (fun t ↦ (isClosed_matrixAtLeast k t).measurableSet.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at h
  exact h

namespace MeasuredGHSpace

/-- Leaf-tightness gives, for each radius and error, one sample size working
for all large indices. -/
theorem exists_annealedCoverRadius_le {P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u}}
    (hleaf : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ k N : ℕ, ∀ n ≥ N, (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ) ≤ η := by
  obtain ⟨k, hk⟩ := ((hleaf δ hδ).eventually (gt_mem_nhds hη)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hk)
  exact ⟨k, N, fun n hn ↦ (hN n hn).le⟩

/-- **Tightness half of Proposition `C.1`.** Convergent annealed sampled
matrices and leaf-tightness make the laws of the random measured spaces tight. -/
theorem isTightMeasureSet_of_leafTight {P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u}}
    {L : ∀ k : ℕ, ProbabilityMeasure (Fin k → Fin k → ℝ)}
    (hM : ∀ k : ℕ, Tendsto (fun n ↦ annealedDistanceLaw (P n) k) atTop (𝓝 (L k)))
    (hleaf : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (range fun n ↦ (P n : Measure MeasuredGHSpace.{u})) := by
  let : MeasurableSpace GHSpace := borel GHSpace
  have : BorelSpace GHSpace := ⟨rfl⟩
  rw [isTightMeasureSet_range_iff_underlyingGH]
  have hmap (n : ℕ) {s : Set GHSpace} (hs : MeasurableSet s) :
      ((P n : Measure MeasuredGHSpace.{u}).map underlyingGH) s =
        (P n : Measure MeasuredGHSpace.{u}) (underlyingGH ⁻¹' s) :=
    Measure.map_apply continuous_underlyingGH.measurable hs
  apply isTightMeasureSet_range_of_coverable
  · intro η hη
    have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨k, N₁, hN₁⟩ := exists_annealedCoverRadius_le hleaf one_pos hη2
    obtain ⟨t, ht⟩ := ((tendsto_measure_matrixAtLeast (k + 1)
      (L (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))).eventually
        (gt_mem_nhds hη2)).exists
    have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hM (k + 1))
      (isClosed_matrixAtLeast (k + 1) t)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt (hlim.trans_lt ht))
    refine ⟨(t : ℝ) + 2, max N₁ N₂, fun n hn ↦ ?_⟩
    have hset : {p : GHSpace | (t : ℝ) + 2 < diam (univ : Set p.Rep)} =
        {p : GHSpace | diam (univ : Set p.Rep) ≤ (t : ℝ) + 2}ᶜ := by
      ext p
      simp [not_le]
    rw [hset, hmap n (isClosed_setOf_diam_le _).measurableSet.compl, ← hset]
    · calc
        _ ≤ (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi 1) +
            (annealedDistanceLaw (P n) (k + 1) : Measure (Fin (k + 1) → Fin (k + 1) → ℝ))
              (matrixExceeds (k + 1) ((t : ℝ) + 2 - 2 * 1)) := measure_lt_diam_le (P n) k 1 _
        _ ≤ η / 2 + η / 2 := by
          apply add_le_add (hN₁ n (le_of_max_le_left hn))
          refine (measure_mono ?_).trans (hN₂ n (le_of_max_le_right hn)).le
          intro m hm
          exact matrixExceeds_subset_matrixAtLeast _ _ (by simpa using hm)
        _ = η := ENNReal.add_halves η
  · intro r hr η hη
    obtain ⟨k, N, hN⟩ := exists_annealedCoverRadius_le hleaf (half_pos hr) hη
    refine ⟨k + 1, N, fun n hn ↦ ?_⟩
    rw [show {p : GHSpace | ¬ Coverable p.Rep (k + 1) r} =
      {p : GHSpace | Coverable p.Rep (k + 1) r}ᶜ from rfl,
      hmap n (isOpen_setOf_coverable (k + 1) r).measurableSet.compl]
    have h := measure_not_coverable_le (P n) k (half_pos hr)
    rw [show 2 * (r / 2) = r by ring] at h
    exact h.trans (hN n hn)

end MeasuredGHSpace

end Freezing2
