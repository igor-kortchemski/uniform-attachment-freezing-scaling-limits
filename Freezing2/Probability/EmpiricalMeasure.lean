module

public import Freezing2.Geometry.RowSpace
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Almost sure convergence of empirical measures

For an iid sequence with law `μ` on a separable metric space, the empirical
measure of the first `k + 1` points converges almost surely to `μ` in the
Lévy–Prokhorov distance. The proof uses the strong law of large numbers for
the cells of countably many measurable partitions of small diameter, and an
elementary partition bound for the Lévy–Prokhorov distance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Function
open scoped ENNReal

namespace Freezing2

/-- Empirical measure of the first `k + 1` terms of a sequence. -/
noncomputable def empiricalMeasure {Ω : Type*} [MeasurableSpace Ω] (k : ℕ) (ω : ℕ → Ω) :
    Measure Ω :=
  (uniformIndexLaw k : Measure (Fin (k + 1))).map (fun i : Fin (k + 1) ↦ ω i)

instance {Ω : Type*} [MeasurableSpace Ω] (k : ℕ) (ω : ℕ → Ω) :
    IsProbabilityMeasure (empiricalMeasure k ω) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance

theorem empiricalMeasure_real_apply {Ω : Type*} [MeasurableSpace Ω] (k : ℕ) (ω : ℕ → Ω)
    {A : Set Ω} (hA : MeasurableSet A) :
    (empiricalMeasure k ω).real A =
      (∑ i ∈ Finset.range (k + 1), A.indicator (fun _ ↦ (1 : ℝ)) (ω i)) / ((k + 1 : ℕ) : ℝ) := by
  classical
  rw [measureReal_def, empiricalMeasure, Measure.map_apply (measurable_of_countable _) hA]
  change (Measure.uniformOfFinset (Finset.univ : Finset (Fin (k + 1))) _).toReal = _
  rw [Measure.uniformOfFinset_apply, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_div]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun i ↦ A.indicator (fun _ ↦ (1 : ℝ)) (ω i)) (k + 1)]
    simp only [indicator, Finset.sum_boole, ENNReal.toReal_natCast]
    rfl

/-- Strong law of large numbers for the empirical frequency of a measurable set. -/
theorem ae_tendsto_empiricalMeasure_real {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun k ↦ (empiricalMeasure k ω).real A) atTop (𝓝 (μ.real A)) := by
  let f : Ω → ℝ := A.indicator fun _ ↦ 1
  have hf : Measurable f := measurable_const.indicator hA
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X : ℕ → (ℕ → Ω) → ℝ := fun i ω ↦ f (ω i)
  have hmapX (i : ℕ) : P.map (X i) = μ.map f := by
    rw [show X i = f ∘ fun ω ↦ ω i from rfl, ← Measure.map_map hf (measurable_pi_apply i),
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).map_eq]
  have hXm (i : ℕ) : Measurable (X i) := hf.comp (measurable_pi_apply i)
  have hint : Integrable (X 0) P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).integrable_comp_of_integrable
      ((integrable_const (1 : ℝ)).indicator hA)
  have hindep : Pairwise ((· ⟂ᵢ[P] ·) on X) := fun i j hij ↦
    (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ ↦ f) (fun _ ↦ hf)).indepFun hij
  have hident (i : ℕ) : IdentDistrib (X i) (X 0) P P :=
    ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hmapX i, hmapX 0]⟩
  have hmean : P[X 0] = μ.real A := by
    have h := integral_map (μ := P) (φ := fun ω : ℕ → Ω ↦ ω 0)
      (measurable_pi_apply 0).aemeasurable (f := f) hf.aestronglyMeasurable
    rw [(measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).map_eq] at h
    rw [show P[X 0] = ∫ ω, f (ω 0) ∂P from rfl, ← h]
    exact integral_indicator_one hA
  filter_upwards [strong_law_ae_real X hint hindep hident] with ω hω
  rw [hmean] at hω
  have h := (tendsto_add_atTop_iff_nat 1).mpr hω
  refine h.congr fun k ↦ ?_
  rw [empiricalMeasure_real_apply k ω hA]

/-- A partition into small cells bounds the Lévy–Prokhorov distance by the
cell diameter, the discrepancies of finitely many cells, and the mass of the
remaining cells. -/
theorem levyProkhorovDist_le_partition {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (ν μ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {As : ℕ → Set Ω} (hmeas : ∀ n, MeasurableSet (As n))
    (hbdd : ∀ n, Bornology.IsBounded (As n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdiam : ∀ n, diam (As n) ≤ ρ) (hcover : ⋃ n, As n = univ)
    (hdisj : Pairwise fun n m ↦ Disjoint (As n) (As m)) (N : ℕ) :
    levyProkhorovDist ν μ ≤ ρ + (∑ n ∈ Finset.range N, |ν.real (As n) - μ.real (As n)|) +
      ν.real (⋃ n, ⋃ (_ : N ≤ n), As n) := by
  classical
  set T := ⋃ n, ⋃ (_ : N ≤ n), As n
  set S := ∑ n ∈ Finset.range N, |ν.real (As n) - μ.real (As n)|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hT : 0 ≤ ν.real T := measureReal_nonneg
  apply levyProkhorovDist_le_of_forall_le _ _ (by positivity)
  intro ε B hε hB
  let J := (Finset.range N).filter fun n ↦ (As n ∩ B).Nonempty
  have hsub : B ⊆ (⋃ n ∈ J, As n) ∪ T := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (show x ∈ ⋃ n, As n by rw [hcover]; exact mem_univ x)
    by_cases hN : n < N
    · exact Or.inl (mem_iUnion₂.mpr
        ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hN, x, hn, hx⟩, hn⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨n, not_lt.mp hN, hn⟩)
  have hthick : (⋃ n ∈ J, As n) ⊆ thickening ε B := by
    intro y hy
    obtain ⟨n, hn, hyn⟩ := mem_iUnion₂.mp hy
    obtain ⟨z, hzn, hzB⟩ := (Finset.mem_filter.mp hn).2
    exact mem_thickening_iff.mpr ⟨z, hzB,
      (dist_le_diam_of_mem (hbdd n) hyn hzn).trans_lt (by linarith [hdiam n])⟩
  have hdisjJ : PairwiseDisjoint (↑J : Set ℕ) As := fun i _ j _ hij ↦ hdisj hij
  have h1 : ν.real B ≤ (∑ n ∈ J, ν.real (As n)) + ν.real T :=
    calc
      ν.real B ≤ ν.real ((⋃ n ∈ J, As n) ∪ T) := measureReal_mono hsub
      _ ≤ ν.real (⋃ n ∈ J, As n) + ν.real T := measureReal_union_le _ _
      _ ≤ _ := add_le_add (measureReal_biUnion_finset_le _ _) le_rfl
  have h2 : ∑ n ∈ J, ν.real (As n) ≤ ∑ n ∈ J, μ.real (As n) + S :=
    calc
      ∑ n ∈ J, ν.real (As n) ≤ ∑ n ∈ J, (μ.real (As n) + |ν.real (As n) - μ.real (As n)|) :=
        Finset.sum_le_sum fun n _ ↦ by
          linarith [le_abs_self (ν.real (As n) - μ.real (As n))]
      _ = ∑ n ∈ J, μ.real (As n) + ∑ n ∈ J, |ν.real (As n) - μ.real (As n)| :=
        Finset.sum_add_distrib
      _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun _ _ _ ↦ abs_nonneg _)
  have h3 : ∑ n ∈ J, μ.real (As n) ≤ μ.real (thickening ε B) := by
    rw [← measureReal_biUnion_finset hdisjJ fun n _ ↦ hmeas n]
    exact measureReal_mono hthick
  have hreal : ν.real B ≤ μ.real (thickening ε B) + ε := by linarith
  rw [← ofReal_measureReal (measure_ne_top ν B),
    ← ofReal_measureReal (measure_ne_top μ (thickening ε B)),
    ← ENNReal.ofReal_add measureReal_nonneg (by linarith)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Empirical measures of an iid sequence converge almost surely in the
Lévy–Prokhorov distance. -/
theorem ae_tendsto_levyProkhorovDist_empiricalMeasure {Ω : Type*} [PseudoMetricSpace Ω]
    [TopologicalSpace.SeparableSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun k ↦ levyProkhorovDist (empiricalMeasure k ω) μ) atTop (𝓝 0) := by
  have hpart (m : ℕ) := SeparableSpace.exists_measurable_partition_diam_le (Ω := Ω)
    (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
  choose As hmeas hbdd hdiam hcover hdisj using hpart
  let T : ℕ → ℕ → Set Ω := fun m N ↦ ⋃ n, ⋃ (_ : N ≤ n), As m n
  have hTmeas (m N : ℕ) : MeasurableSet (T m N) :=
    MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun _ ↦ hmeas m n
  have hcells : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ), ∀ m n : ℕ,
      Tendsto (fun k ↦ (empiricalMeasure k ω).real (As m n)) atTop (𝓝 (μ.real (As m n))) := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro n
    exact ae_tendsto_empiricalMeasure_real μ (hmeas m n)
  have htails : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ), ∀ m N : ℕ,
      Tendsto (fun k ↦ (empiricalMeasure k ω).real (T m N)) atTop (𝓝 (μ.real (T m N))) := by
    rw [ae_all_iff]; intro m; rw [ae_all_iff]; intro N
    exact ae_tendsto_empiricalMeasure_real μ (hTmeas m N)
  have hTlim (m : ℕ) : Tendsto (fun N ↦ μ.real (T m N)) atTop (𝓝 0) := by
    have hanti : Antitone (T m) := fun a b hab x hx ↦ by
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨hbn, hxn⟩ := mem_iUnion.mp hn
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hab.trans hbn, hxn⟩⟩
    have hempty : ⋂ N, T m N = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨n₀, hn₀⟩ := mem_iUnion.mp (show x ∈ ⋃ n, As m n by rw [hcover m]; exact mem_univ x)
      obtain ⟨n, hn⟩ := mem_iUnion.mp (mem_iInter.mp hx (n₀ + 1))
      obtain ⟨hbn, hxn⟩ := mem_iUnion.mp hn
      exact (hdisj m (show n₀ ≠ n by omega)).le_bot ⟨hn₀, hxn⟩
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := T m)
      (fun N ↦ (hTmeas m N).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hempty, measure_empty] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa only [Function.comp_def, ENNReal.toReal_zero, measureReal_def] using h'
  filter_upwards [hcells, htails] with ω hcell htail
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < η / 4 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hTlim m).eventually (gt_mem_nhds
    (show (0 : ℝ) < η / 8 by positivity)))
  have hsum : Tendsto (fun k ↦ ∑ n ∈ Finset.range N,
      |(empiricalMeasure k ω).real (As m n) - μ.real (As m n)|) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range N) fun n _ ↦
      ((hcell m n).sub_const (μ.real (As m n))).abs
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using h
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp (hsum.eventually (gt_mem_nhds
    (show (0 : ℝ) < η / 4 by positivity)))
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp ((htail m N).eventually (gt_mem_nhds
    (show μ.real (T m N) < η / 4 by linarith [hN N le_rfl])))
  refine ⟨max K₁ K₂, fun k hk ↦ ?_⟩
  have hb := levyProkhorovDist_le_partition (empiricalMeasure k ω) μ (hmeas m) (hbdd m)
    (by positivity : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1)) (hdiam m) (hcover m) (hdisj m) N
  have h1 := hK₁ k (le_of_max_le_left hk)
  have h2 := hK₂ k (le_of_max_le_right hk)
  have h0 : 0 ≤ levyProkhorovDist (empiricalMeasure k ω) μ := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  change levyProkhorovDist (empiricalMeasure k ω) μ ≤ 1 / ((m : ℝ) + 1) + _ + _ at hb
  linarith

end Freezing2
