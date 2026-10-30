module

public import Freezing2.Geometry.GHCovering
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A tightness criterion on the Gromov–Hausdorff space

If, for large indices, the diameters are bounded in probability and, at every
scale, the covering numbers are bounded in probability, then the whole sequence
of laws is tight. The finitely many early laws are controlled individually:
every compact space has finite diameter and finite covering numbers, and the
corresponding events are closed or open, so continuity from above applies.
This is the Gromov compactness step in the proof of Proposition `C.1`.
-/

@[expose] public section

open MeasureTheory Set Metric GromovHausdorff Filter Topology
open scoped ENNReal NNReal Cardinal

namespace Freezing2.GHCovering

variable [MeasurableSpace GHSpace] [BorelSpace GHSpace]

/-- One finite law has a small diameter tail. -/
theorem exists_diam_tail_le (μ : Measure GHSpace) [IsFiniteMeasure μ] {η : ℝ≥0∞}
    (hη : 0 < η) : ∃ D : ℕ, μ {p | (D : ℝ) < diam (univ : Set p.Rep)} ≤ η := by
  let s : ℕ → Set GHSpace := fun D ↦ {p | (D : ℝ) < diam (univ : Set p.Rep)}
  have hanti : Antitone s := fun a b hab p hp ↦ by
    simp only [s, mem_ofPred_eq] at hp ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hp
  have hmeas (D : ℕ) : NullMeasurableSet (s D) μ := by
    have h := (isClosed_setOf_diam_le (D : ℝ)).measurableSet.compl
    have he : s D = {p : GHSpace | diam (univ : Set p.Rep) ≤ D}ᶜ := by
      ext p
      simp [s, not_le]
    rw [he]
    exact h.nullMeasurableSet
  have hempty : ⋂ D, s D = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨D, hD⟩ := exists_nat_ge (diam (univ : Set p.Rep))
    exact (not_lt_of_ge hD) (mem_iInter.mp hp D)
  have ht := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at ht
  obtain ⟨D, hD⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨D, hD.le⟩

/-- One finite law has a small tail of large covering numbers at a fixed scale. -/
theorem exists_coverable_tail_le (μ : Measure GHSpace) [IsFiniteMeasure μ] {r : ℝ}
    (hr : 0 < r) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K : ℕ, μ {p | ¬ Coverable p.Rep K r} ≤ η := by
  let s : ℕ → Set GHSpace := fun K ↦ {p | ¬ Coverable p.Rep K r}
  have hanti : Antitone s := fun a b hab p hp ha ↦ hp (ha.mono hab le_rfl)
  have hmeas (K : ℕ) : NullMeasurableSet (s K) μ :=
    (isOpen_setOf_coverable K r).measurableSet.compl.nullMeasurableSet
  have hempty : ⋂ K, s K = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨K, hK⟩ := exists_coverable p.Rep hr
    exact (mem_iInter.mp hp K) hK
  have ht := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at ht
  obtain ⟨K, hK⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨K, hK.le⟩

/-- **GH tightness criterion.** Eventual uniform control of diameters and of
covering numbers at every scale gives tightness of the whole sequence. -/
theorem isTightMeasureSet_range_of_coverable (Q : ℕ → Measure GHSpace)
    [∀ n, IsFiniteMeasure (Q n)]
    (hdiam : ∀ η : ℝ≥0∞, 0 < η → ∃ D : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      Q n {p | D < diam (univ : Set p.Rep)} ≤ η)
    (hcov : ∀ r : ℝ, 0 < r → ∀ η : ℝ≥0∞, 0 < η → ∃ K N : ℕ, ∀ n ≥ N,
      Q n {p | ¬ Coverable p.Rep K r} ≤ η) :
    IsTightMeasureSet (range Q) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε2.ne' ℕ
  obtain ⟨D₀, N₀, hD₀⟩ := hdiam (ε / 2) hε2
  have hDn (n : ℕ) := exists_diam_tail_le (Q n) hε2
  choose Dn hDn using hDn
  let D : ℝ := max D₀ ((Finset.range N₀).sup Dn : ℕ)
  have hDall (n : ℕ) : Q n {p | D < diam (univ : Set p.Rep)} ≤ ε / 2 := by
    by_cases hn : N₀ ≤ n
    · exact (measure_mono (show {p : GHSpace | D < diam (univ : Set p.Rep)} ⊆
        {p | D₀ < diam (univ : Set p.Rep)} from fun p hp ↦ by
          simp only [mem_ofPred_eq] at hp ⊢
          exact lt_of_le_of_lt (le_max_left _ _) hp)).trans (hD₀ n hn)
    · have hle : (Dn n : ℝ) ≤ D := le_max_of_le_right (by
        exact_mod_cast Finset.le_sup (f := Dn) (Finset.mem_range.mpr (by omega)))
      exact (measure_mono (show {p : GHSpace | D < diam (univ : Set p.Rep)} ⊆
        {p | (Dn n : ℝ) < diam (univ : Set p.Rep)} from fun p hp ↦ by
          simp only [mem_ofPred_eq] at hp ⊢
          exact lt_of_le_of_lt hle hp)).trans (hDn n)
  let r : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hr (m : ℕ) : 0 < r m := by positivity
  have hK (m : ℕ) : ∃ K : ℕ, ∀ n, Q n {p | ¬ Coverable p.Rep K (r m)} ≤ ε' m := by
    obtain ⟨K₀, N, hK₀⟩ := hcov (r m) (hr m) (ε' m) (by exact_mod_cast hε'pos m)
    have hKn (n : ℕ) := exists_coverable_tail_le (Q n) (hr m)
      (show (0 : ℝ≥0∞) < ε' m by exact_mod_cast hε'pos m)
    choose Kn hKn using hKn
    refine ⟨max K₀ ((Finset.range N).sup Kn), fun n ↦ ?_⟩
    by_cases hn : N ≤ n
    · exact (measure_mono (show {p : GHSpace | ¬ Coverable p.Rep
        (max K₀ ((Finset.range N).sup Kn)) (r m)} ⊆ {p | ¬ Coverable p.Rep K₀ (r m)} from
          fun p hp hc ↦ hp (hc.mono (le_max_left _ _) le_rfl))).trans (hK₀ n hn)
    · have hle : Kn n ≤ max K₀ ((Finset.range N).sup Kn) :=
        le_max_of_le_right (Finset.le_sup (f := Kn) (Finset.mem_range.mpr (by omega)))
      exact (measure_mono (show {p : GHSpace | ¬ Coverable p.Rep
        (max K₀ ((Finset.range N).sup Kn)) (r m)} ⊆ {p | ¬ Coverable p.Rep (Kn n) (r m)} from
          fun p hp hc ↦ hp (hc.mono hle le_rfl))).trans (hKn n)
  choose K hK using hK
  let T : Set GHSpace := {p | diam (univ : Set p.Rep) ≤ D} ∩
    ⋂ m, {p | Coverable p.Rep (K m) (r m)}
  have hT : TotallyBounded T := by
    apply GromovHausdorff.totallyBounded (C := D) (u := r) (K := K)
    · simpa only [r] using tendsto_one_div_add_atTop_nhds_zero_nat
    · intro p hp
      exact hp.1
    · intro p hp m
      obtain ⟨s, hs, hcov⟩ := mem_iInter.mp hp.2 m
      refine ⟨(s : Set p.Rep), ?_, fun x _ ↦ ?_⟩
      · simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset]
        exact_mod_cast hs
      · obtain ⟨y, hy, hxy⟩ := hcov x
        exact mem_iUnion₂.mpr ⟨y, Finset.mem_coe.mpr hy, mem_ball.mpr hxy⟩
  refine ⟨closure T, hT.closure.isCompact_of_isClosed isClosed_closure, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hcompl : Tᶜ = {p : GHSpace | D < diam (univ : Set p.Rep)} ∪
      ⋃ m, {p : GHSpace | ¬ Coverable p.Rep (K m) (r m)} := by
    ext p
    simp only [T, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter, not_and_or, not_le,
      not_forall, mem_union, mem_iUnion]
  calc
    Q n (closure T)ᶜ ≤ Q n Tᶜ := measure_mono (compl_subset_compl.mpr subset_closure)
    _ ≤ Q n {p | D < diam (univ : Set p.Rep)} +
          ∑' m, Q n {p | ¬ Coverable p.Rep (K m) (r m)} := by
      rw [hcompl]
      exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ ε / 2 + ∑' m, (ε' m : ℝ≥0∞) :=
      add_le_add (hDall n) (ENNReal.tsum_le_tsum fun m ↦ hK m n)
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hε'sum.le
    _ = ε := ENNReal.add_halves ε

end Freezing2.GHCovering
