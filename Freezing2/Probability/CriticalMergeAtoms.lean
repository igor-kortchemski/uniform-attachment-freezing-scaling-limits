module

public import Freezing2.Probability.CriticalRealTree

/-!
# Mergers do not happen at birth times in the critical limit (U38)

In the limiting genealogy of `k` uniform vertices, the coalescence time of two
distinct samples almost surely differs from their birth times. In the discrete
model, a merger within `δ n` phases below a birth at a macroscopic time has
probability at most the hazard sum over that window, which is uniformly close to
`∫ 1/f²` over an interval of length `δ`, hence small; repeated samples have
probability `O(1/n)`. The portmanteau theorem for open sets transfers the bound to
the limit. Scaled birth times of the limit are almost surely in `(0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2.CriticalGenealogy

open ReverseHistory ReverseCoalescence MeasuredGHSpace

/-- Integrals over short subintervals of a compact interval are uniformly small. -/
theorem exists_uniform_small_interval_integral {f : ℝ → ℝ} {A B : ℝ}
    (hf : IntegrableOn f (Icc A B) volume) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ u v : ℝ, A ≤ u → u ≤ v → v ≤ B → v - u ≤ δ → ∫ t in Icc u v, f t ≤ η := by
  set F : ℝ → ℝ := fun t ↦ ∫ s in Icc A t, f s
  have hcont : ContinuousOn F (Icc A B) := intervalIntegral.continuousOn_primitive_Icc hf
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  refine ⟨δ / 2, by positivity, fun u v hu huv hv hlen ↦ ?_⟩
  have heq : ∫ t in Icc u v, f t = F v - F u :=
    (setIntegral_Icc_sub_left hu huv (hf.mono_set fun _ ht ↦ ⟨ht.1, ht.2.trans hv⟩)).symm
  have hd : dist v u < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have := hδF v ⟨hu.trans huv, hv⟩ u ⟨hu, huv.trans hv⟩ hd
  rw [Real.dist_eq] at this
  rw [heq]
  exact (le_abs_self _).trans this.le

/-- Uniform smallness of the critical hazard sums over short interior windows. -/
theorem exists_critical_window_bound {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {ε η : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hη : 0 < η) :
    ∃ δ > 0, ∀ᶠ n in atTop, ∀ a b : ℕ, CoalescenceInterval ε n a b → (b : ℝ) - a ≤ δ * n →
      2 * coalescenceUpSum (xa n) (a - 1) (b + 1 - a) < η := by
  have hg2 := (h2 ε (1 - ε) hε (by linarith) (by linarith)).1
  obtain ⟨δ, hδ, hδint⟩ := exists_uniform_small_interval_integral hg2 (half_pos hη)
  refine ⟨δ, hδ, ?_⟩
  have herr := tendsto_coalescenceIntervalErrorMax hx (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε
  filter_upwards [herr.eventually (gt_mem_nhds (show (0 : ℝ) < η / 4 by positivity)),
    eventually_gt_atTop 0] with n hn hn0 a b hab hlen
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hle : coalescenceIntervalError xa (1 / 2) g n a b ≤
      coalescenceIntervalErrorMax xa (1 / 2) g ε n := by
    unfold coalescenceIntervalErrorMax
    have hmem : ((⟨a, by have := hab.2.1; have := hab.2.2.1; omega⟩ : Fin (n + 1)),
        (⟨b, by have := hab.2.2.1; omega⟩ : Fin (n + 1))) ∈ Finset.univ := Finset.mem_univ _
    refine le_trans ?_ (Finset.le_sup' _ hmem)
    simp only [hab, ↓reduceIte, le_refl]
  have hint : ∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), (g t) ^ 2 ≤ η / 2 := by
    apply hδint
    · rw [le_div_iff₀ hnr]; exact hab.2.2.2.1
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hab.2.1) hnr.le
    · rw [div_le_iff₀ hnr]; exact hab.2.2.2.2
    · rw [← sub_div, div_le_iff₀ hnr]; exact hlen
  have hscale : ((n : ℝ) ^ (2 * (1 / 2 : ℝ)) / n) = 1 := by
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one, div_self hnr.ne']
  have herr' := hle.trans_lt hn
  unfold coalescenceIntervalError at herr'
  rw [hscale, one_mul, abs_lt] at herr'
  linarith [herr'.2]

/-- A distinct pair merges within `δ n` phases below the first birth with probability
at most the window bound. -/
theorem pair_merge_near_birth_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ} (hs : SurvivesThrough x n)
    (hn : 0 < n) {ε δ η : ℝ} (hδ : 0 < δ) (hδε : δ < ε / 2) (hη : 0 ≤ η)
    (hbound : ∀ a b : ℕ, CoalescenceInterval (ε / 2) n a b → (b : ℝ) - a ≤ δ * n →
      2 * coalescenceUpSum x (a - 1) (b + 1 - a) < η)
    {u v : VertexLabel} (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (huv : u ≠ v)
    (hb1 : ε * n < (birthTime n u : ℝ)) (hb2 : (birthTime n u : ℝ) < (1 - ε) * n) :
    (jointLaw (companionSchedule x) n).real
      {ω | (birthTime n u : ℝ) / n - δ < (sourceCoalescenceTime n u v ω : ℝ) / n} ≤ η := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set B := birthTime n u
  set y : ℝ := (B : ℝ) - δ * n
  have hy : 0 ≤ y := by
    have : δ * n ≤ ε * n := mul_le_mul_of_nonneg_right (by linarith) hnr.le
    simp only [y]
    linarith
  set i₁ := ⌊y⌋₊ + 1
  set m := min B (birthTime n v)
  have hcoal (ω : History) : sourceCoalescenceTime n u v ω ≤ m := by
    simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime, m, B] using
      coalescenceTime_le_commonBirth n (toCompanionLabel u) (toCompanionLabel v) ω
  have hsub : {ω | (B : ℝ) / n - δ < (sourceCoalescenceTime n u v ω : ℝ) / n} ⊆
      {ω | i₁ ≤ sourceCoalescenceTime n u v ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have h1 : y < sourceCoalescenceTime n u v ω := by
      have := (mul_lt_mul_iff_of_pos_right hnr).mpr hω
      rw [sub_mul, div_mul_cancel₀ _ hnr.ne', div_mul_cancel₀ _ hnr.ne'] at this
      exact this
    have h2 : ⌊y⌋₊ < sourceCoalescenceTime n u v ω := by
      exact_mod_cast (Nat.floor_le hy).trans_lt h1
    omega
  by_cases hmi : m < i₁
  · have he : {ω | (B : ℝ) / n - δ < (sourceCoalescenceTime n u v ω : ℝ) / n} = ∅ := by
      ext ω
      simp only [mem_empty_iff_false, iff_false]
      intro hω
      have := hsub hω
      simp only [mem_ofPred_eq] at this
      have := hcoal ω
      omega
    rw [he, measureReal_empty]
    exact hη
  have him : i₁ ≤ m := not_lt.mp hmi
  refine (measureReal_mono hsub).trans ?_
  refine (source_coalescence_ge_probability_le_sum x hx hs hu hv huv him).trans ?_
  show 2 * coalescenceUpSum x i₁ (m - i₁) ≤ η
  rcases eq_or_lt_of_le him with heq | hlt
  · rw [← heq, Nat.sub_self]
    simp [coalescenceUpSum, hη]
  · have hbn : m ≤ n := (min_le_left _ _).trans (birthTime_le x hu)
    have hfl : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
    have hval : CoalescenceInterval (ε / 2) n (i₁ + 1) m := by
      refine ⟨by omega, by omega, hbn, ?_, ?_⟩
      · push_cast
        simp only [i₁, y] at hfl ⊢
        push_cast
        have : ε * n - δ * n ≥ ε / 2 * n := by nlinarith
        linarith
      · have hmB : (m : ℝ) ≤ B := by exact_mod_cast min_le_left B (birthTime n v)
        nlinarith
    have hlen : ((m : ℕ) : ℝ) - ((i₁ + 1 : ℕ) : ℝ) ≤ δ * n := by
      have hmB : (m : ℝ) ≤ B := by exact_mod_cast min_le_left B (birthTime n v)
      simp only [i₁, y] at hfl ⊢
      push_cast
      linarith
    have := hbound (i₁ + 1) m hval hlen
    simp only [Nat.add_sub_cancel, show m + 1 - (i₁ + 1) = m - i₁ by omega] at this
    exact this.le

/-- The two-sample event of a merger within `δ n` phases below the first birth. -/
def nearBirthMergeEvent (n : ℕ) (ε δ : ℝ) : Set (History × (VertexLabel × VertexLabel)) :=
  {q | ε * n < (birthTime n q.2.1 : ℝ) ∧ (birthTime n q.2.1 : ℝ) < (1 - ε) * n ∧
    (birthTime n q.2.1 : ℝ) / n - δ < (sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n}

theorem measurableSet_nearBirthMergeEvent (n : ℕ) (ε δ : ℝ) :
    MeasurableSet (nearBirthMergeEvent n ε δ) := by
  apply measurable_from_prod_countable_left (fun p ↦ ?_) |>.setOf
  show Measurable fun ω : History ↦ ε * n < (birthTime n p.1 : ℝ) ∧
    (birthTime n p.1 : ℝ) < (1 - ε) * n ∧
      (birthTime n p.1 : ℝ) / n - δ < (sourceCoalescenceTime n p.1 p.2 ω : ℝ) / n
  exact measurable_const.and (measurable_const.and (measurable_const.lt
    (((measurable_of_countable (fun c : ℕ ↦ (c : ℝ))).comp
      (measurable_sourceCoalescenceTime n p.1 p.2)).div_const _)))

theorem nearBirthMerge_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (hn : 0 < n) {ε δ η : ℝ} (hδ : 0 < δ) (hδε : δ < ε / 2)
    (hη : 0 ≤ η)
    (hbound : ∀ a b : ℕ, CoalescenceInterval (ε / 2) n a b → (b : ℝ) - a ≤ δ * n →
      2 * coalescenceUpSum x (a - 1) (b + 1 - a) < η) :
    (sampledReverseLaw x n).real (nearBirthMergeEvent n ε δ) ≤
      1 / (vertexLabels x n).card + η := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hmem : ∀ᵐ p ∂(uniformVertex x n).prod (uniformVertex x n),
      p.1 ∈ vertexLabels x n ∧ p.2 ∈ vertexLabels x n := by
    apply (Measure.ae_prod_iff_ae_ae (by exact (Set.to_countable _).measurableSet)).mpr
    filter_upwards [uniformVertex_mem x hx (hs n le_rfl).le] with u hu
    exact (uniformVertex_mem x hx (hs n le_rfl).le).mono fun v hv ↦ ⟨hu, hv⟩
  have hsections : ∀ᵐ p ∂(uniformVertex x n).prod (uniformVertex x n),
      p ∉ {p : VertexLabel × VertexLabel | p.1 = p.2} → (jointLaw (companionSchedule x) n).real
        {ω | (ω, p) ∈ nearBirthMergeEvent n ε δ} ≤ η := by
    filter_upwards [hmem] with p hp hnot
    have hne : p.1 ≠ p.2 := fun h ↦ hnot h
    by_cases hb : ε * n < (birthTime n p.1 : ℝ) ∧ (birthTime n p.1 : ℝ) < (1 - ε) * n
    · refine (measureReal_mono (s₂ := {ω | (birthTime n p.1 : ℝ) / n - δ <
          (sourceCoalescenceTime n p.1 p.2 ω : ℝ) / n}) (fun ω hω ↦ hω.2.2)).trans ?_
      exact pair_merge_near_birth_le x hx hs hn hδ hδε hη hbound hp.1 hp.2 hne hb.1 hb.2
    · have he : {ω | (ω, p) ∈ nearBirthMergeEvent n ε δ} = ∅ := by
        ext ω
        simp only [nearBirthMergeEvent, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h ↦ hb ⟨h.1, h.2.1⟩
      rw [he, measureReal_empty]
      exact hη
  have h := measureReal_prod_event_le_bad_add
    (μ := jointLaw (companionSchedule x) n)
    (ν := (uniformVertex x n).prod (uniformVertex x n))
    (E := nearBirthMergeEvent n ε δ) (B := {p : VertexLabel × VertexLabel | p.1 = p.2})
    (measurableSet_nearBirthMergeEvent n ε δ)
    (show MeasurableSet {p : VertexLabel × VertexLabel | p.1 = p.2} from
      (Set.to_countable _).measurableSet) hη hsections
  rw [uniformVertex_collision x hx (hs n le_rfl).le] at h
  exact h

section Limit

variable {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} {k : ℕ}

/-- Genealogy events about the pair `(i, j)` are two-sample events. -/
theorem genealogyLaw_real_pair (hx : AdmissibleArray xa) (n : ℕ) {i j : Fin k} (hij : i ≠ j)
    {O : Set (GenealogySpace k)} (hO : MeasurableSet O)
    {E : Set (History × (VertexLabel × VertexLabel))} (hE : MeasurableSet E)
    (hOE : genealogyVector n ⁻¹' O = (fun q ↦ (q.1, (q.2 i, q.2 j))) ⁻¹' E) :
    (genealogyLaw hx k n : Measure (GenealogySpace k)).real O =
      (sampledReverseLaw (xa n) n).real E := by
  have hm : Measurable (fun q : History × (Fin k → VertexLabel) ↦ (q.1, (q.2 i, q.2 j))) :=
    measurable_fst.prodMk (((measurable_pi_apply i).comp measurable_snd).prodMk
      ((measurable_pi_apply j).comp measurable_snd))
  simp only [genealogyLaw, ProbabilityMeasure.coe_mk, measureReal_def]
  rw [Measure.map_apply (measurable_genealogyVector n) hO, hOE,
    ← sampledReverseVectorLaw_map_pair (xa n) (hx n).1 (hx n).2 hij, Measure.map_apply hm hE]

/-- Two-sample events about the first label only reduce to the uniform vertex law. -/
theorem sampledReverseLaw_real_first (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (P : VertexLabel → Prop) :
    (sampledReverseLaw x n).real {q | P q.2.1} = (uniformVertex x n).real {v | P v} := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have he : {q : History × (VertexLabel × VertexLabel) | P q.2.1} =
      univ ×ˢ ({v | P v} ×ˢ univ) := by
    ext q
    simp
  rw [he, sampledReverseLaw, measureReal_prod_prod, measureReal_prod_prod]
  simp

/-- The limit law gives small mass to mergers within `δ` of the first birth. -/
theorem criticalGenealogyLimit_nearBirth_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j)
    {ε η : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4) (hη : 0 < η) :
    ∃ δ > 0, (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | ε < z.1 i ∧ z.1 i < 1 - ε ∧ z.1 i - δ < z.2 i j} ≤ ENNReal.ofReal (2 * η) := by
  obtain ⟨δ₀, hδ₀, hwin⟩ := exists_critical_window_bound hx hL1 hpos h2 (half_pos hε)
    (by linarith) hη
  set δ := min δ₀ (ε / 4)
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  refine ⟨δ, hδ, ?_⟩
  set O : Set (GenealogySpace k) := {z | ε < z.1 i ∧ z.1 i < 1 - ε ∧ z.1 i - δ < z.2 i j}
  have hO : IsOpen O := by
    have hb : Continuous fun z : GenealogySpace k ↦ z.1 i := (continuous_apply i).comp continuous_fst
    have hc : Continuous fun z : GenealogySpace k ↦ z.2 i j :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
    exact (isOpen_lt continuous_const hb).inter ((isOpen_lt hb continuous_const).inter
      (isOpen_lt (hb.sub continuous_const) hc))
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  refine hlim.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
  have hcoll := tendsto_uniformVertex_collision hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos
  filter_upwards [hwin, hcoll.eventually (gt_mem_nhds hη), eventually_gt_atTop 0]
    with n hn hcn hn0
  have hbound : ∀ a b : ℕ, CoalescenceInterval (ε / 2) n a b → (b : ℝ) - a ≤ δ * n →
      2 * coalescenceUpSum (xa n) (a - 1) (b + 1 - a) < η := fun a b hab hlen ↦
    hn a b hab (hlen.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)))
  have hpair := nearBirthMerge_probability_le (xa n) (hx n).1 (hx n).2 hn0 hδ
    (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hη.le hbound
  rw [uniformVertex_collision (xa n) (hx n).1 ((hx n).2 n le_rfl).le] at hcn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have heq := genealogyLaw_real_pair hx n hij hO.measurableSet
    (measurableSet_nearBirthMergeEvent n ε δ) (by
      ext q
      simp only [mem_preimage, genealogyVector, O, nearBirthMergeEvent, mem_ofPred_eq]
      rw [lt_div_iff₀ hnr, div_lt_iff₀ hnr])
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ O), ← measureReal_def, heq]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem criticalGenealogyLimit_merge_at_birth_window (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j)
    {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k))
      {z | z.2 i j = z.1 i ∧ ε < z.1 i ∧ z.1 i < 1 - ε} = 0 := by
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  obtain ⟨δ, hδ, hle⟩ := criticalGenealogyLimit_nearBirth_le hx hL1 hpos h2 hij hε hε4
    (show (0 : ℝ) < η / 2 by positivity)
  refine (measure_mono fun z hz ↦ ?_).trans (hle.trans ?_)
  · exact ⟨hz.2.1, hz.2.2, by rw [hz.1]; linarith⟩
  · rw [bot_eq_zero, zero_add, show 2 * ((η : ℝ) / 2) = η by ring, ENNReal.ofReal_coe_nnreal]

/-- Birth times of the limit are almost surely below any positive level with
probability at most that level. -/
theorem criticalGenealogyLimit_birth_lt_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | z.1 i < θ} ≤
      ENNReal.ofReal θ := by
  have hO : IsOpen {z : GenealogySpace k | z.1 i < θ} :=
    isOpen_lt ((continuous_apply i).comp continuous_fst) continuous_const
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  refine hlim.trans ?_
  have hlate := tendsto_lateBirthProbability hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos hθ0 hθ1
  have hupper : ∀ᶠ n in atTop, (genealogyLaw hx k n : Measure (GenealogySpace k))
      {z | z.1 i < θ} ≤ ENNReal.ofReal (1 - lateBirthProbability (xa n) n θ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    let := uniformVertex_isProbabilityMeasure (xa n) (hx n).1 ((hx n).2 n le_rfl).le
    have heq := genealogyLaw_real_pair hx n hij hO.measurableSet
      (E := {q | (birthTime n q.2.1 : ℝ) < θ * n})
      ((measurable_of_countable (fun v : VertexLabel ↦ (birthTime n v : ℝ) < θ * n)).comp
        (measurable_fst.comp measurable_snd) |>.setOf) (by
        ext q
        simp only [mem_preimage, genealogyVector, mem_ofPred_eq]
        rw [div_lt_iff₀ hnr])
    rw [sampledReverseLaw_real_first (xa n) (hx n).1 (hx n).2
      (fun v ↦ (birthTime n v : ℝ) < θ * n)] at heq
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def, heq]
    apply ENNReal.ofReal_le_ofReal
    unfold lateBirthProbability
    have hc : {v : VertexLabel | (birthTime n v : ℝ) < θ * n} ⊆
        {v | θ * n < (birthTime n v : ℝ)}ᶜ :=
      fun v (hv : (birthTime n v : ℝ) < θ * n) (h : θ * n < (birthTime n v : ℝ)) ↦ lt_asymm hv h
    rw [← probReal_compl_eq_one_sub (by exact (measurable_of_countable _).setOf)]
    exact measureReal_mono hc
  have hlim1 : Tendsto (fun n ↦ ENNReal.ofReal (1 - lateBirthProbability (xa n) n θ)) atTop
      (𝓝 (ENNReal.ofReal θ)) := by
    have h1 : Tendsto (fun n ↦ 1 - lateBirthProbability (xa n) n θ) atTop (𝓝 (1 - (1 - θ))) :=
      (tendsto_const_nhds (x := (1 : ℝ))).sub hlate
    rw [sub_sub_cancel] at h1
    exact (ENNReal.continuous_ofReal.tendsto θ).comp h1
  exact (liminf_le_liminf hupper).trans_eq hlim1.liminf_eq

theorem criticalGenealogyLimit_birth_gt_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | r < z.1 i} ≤
      ENNReal.ofReal (1 - r) := by
  have hO : IsOpen {z : GenealogySpace k | r < z.1 i} :=
    isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hO
  refine hlim.trans ?_
  have hlate := tendsto_lateBirthProbability hx (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos hr0 hr1
  have heqn : ∀ᶠ n in atTop, (genealogyLaw hx k n : Measure (GenealogySpace k))
      {z | r < z.1 i} = ENNReal.ofReal (lateBirthProbability (xa n) n r) := by
    filter_upwards [eventually_gt_atTop 0] with n hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have heq := genealogyLaw_real_pair hx n hij hO.measurableSet
      (E := {q | r * n < (birthTime n q.2.1 : ℝ)})
      ((measurable_of_countable (fun v : VertexLabel ↦ r * n < (birthTime n v : ℝ))).comp
        (measurable_fst.comp measurable_snd) |>.setOf) (by
        ext q
        simp only [mem_preimage, genealogyVector, mem_ofPred_eq]
        rw [lt_div_iff₀ hnr])
    rw [sampledReverseLaw_real_first (xa n) (hx n).1 (hx n).2
      (fun v ↦ r * n < (birthTime n v : ℝ))] at heq
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def, heq]
    rfl
  have hlim1 : Tendsto (fun n ↦ ENNReal.ofReal (lateBirthProbability (xa n) n r)) atTop
      (𝓝 (ENNReal.ofReal (1 - r))) := (ENNReal.continuous_ofReal.tendsto _).comp hlate
  rw [liminf_congr heqn, hlim1.liminf_eq]

/-- **Mergers never happen at a birth time (U38).** -/
theorem criticalGenealogyLimit_merge_ne_birth (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {i j : Fin k} (hij : i ≠ j) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | z.2 i j = z.1 i} = 0 := by
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  have hlow : μ {z | z.1 i ≤ 0} = 0 := by
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hθ : (0 : ℝ) < min (η : ℝ) (1 / 2) := lt_min (by exact_mod_cast hη) (by norm_num)
    have hsub : {z : GenealogySpace k | z.1 i ≤ 0} ⊆ {z | z.1 i < min (η : ℝ) (1 / 2)} :=
      fun z hz ↦ lt_of_le_of_lt hz hθ
    refine (measure_mono hsub).trans ((criticalGenealogyLimit_birth_lt_le hx hL1 hpos h2 hij
        hθ.le (by linarith [min_le_right (η : ℝ) (1 / 2)])).trans ?_)
    rw [bot_eq_zero, zero_add]
    exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq (ENNReal.ofReal_coe_nnreal)
  have hhigh : μ {z | 1 ≤ z.1 i} = 0 := by
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro η hη _
    have hθ : (0 : ℝ) < min (η : ℝ) (1 / 2) := lt_min (by exact_mod_cast hη) (by norm_num)
    have hr0 : (0 : ℝ) ≤ 1 - min (η : ℝ) (1 / 2) := by linarith [min_le_right (η : ℝ) (1 / 2)]
    have hsub : {z : GenealogySpace k | 1 ≤ z.1 i} ⊆ {z | 1 - min (η : ℝ) (1 / 2) < z.1 i} :=
      fun z (hz : 1 ≤ z.1 i) ↦ by show 1 - min (η : ℝ) (1 / 2) < z.1 i; linarith
    refine (measure_mono hsub).trans ((criticalGenealogyLimit_birth_gt_le hx hL1 hpos h2 hij hr0
        (by linarith)).trans ?_)
    rw [bot_eq_zero, zero_add, sub_sub_cancel]
    exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq (ENNReal.ofReal_coe_nnreal)
  have hmid : ∀ m : ℕ, μ {z | z.2 i j = z.1 i ∧ 1 / ((m : ℝ) + 5) < z.1 i ∧
      z.1 i < 1 - 1 / ((m : ℝ) + 5)} = 0 := fun m ↦
    criticalGenealogyLimit_merge_at_birth_window hx hL1 hpos h2 hij (by positivity)
      (by rw [div_lt_iff₀ (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  apply measure_mono_null (t := {z | z.1 i ≤ 0} ∪ {z | 1 ≤ z.1 i} ∪ ⋃ m : ℕ,
    {z | z.2 i j = z.1 i ∧ 1 / ((m : ℝ) + 5) < z.1 i ∧ z.1 i < 1 - 1 / ((m : ℝ) + 5)})
  · intro z hz
    by_cases h0 : z.1 i ≤ 0
    · exact Or.inl (Or.inl h0)
    by_cases h1 : 1 ≤ z.1 i
    · exact Or.inl (Or.inr h1)
    push Not at h0 h1
    have hp : 0 < min (z.1 i) (1 - z.1 i) := lt_min h0 (by linarith)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hp
    refine Or.inr (mem_iUnion.mpr ⟨m, hz, ?_, ?_⟩)
    · have : 1 / ((m : ℝ) + 5) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [min_le_left (z.1 i) (1 - z.1 i)]
    · have : 1 / ((m : ℝ) + 5) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith [min_le_right (z.1 i) (1 - z.1 i)]
  · exact measure_union_null (measure_union_null hlow hhigh) (measure_iUnion_null hmid)

end Limit

end Freezing2.CriticalGenealogy
