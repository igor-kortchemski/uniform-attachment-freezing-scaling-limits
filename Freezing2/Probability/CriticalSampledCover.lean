module

public import Freezing2.Probability.CriticalBlockCover
public import Freezing2.Probability.CriticalBlockOccupancy
public import Freezing2.Probability.ProductEventBound
public import Freezing2.Analysis.CriticalIsolationRate
public import Freezing2.Analysis.CriticalBlockRadius
public import Freezing2.Probability.OneStepTightnessAsymptotic
public import Freezing2.Analysis.CriticalPopulationBound

/-!
# Critical covering estimates with actual iid vertex samples

One query vertex and the covering tuple are independently uniform on the
actual deterministic label set. The reverse history has its constructed
joint law. The bad occupancy probability is retained before integrating the
uniform conditional block estimate; no conditioning changes the sampler.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- The distinct companion labels appearing in a source-labelled tuple. -/
noncomputable def sampledCompanionLabels {k : ℕ} (v : Fin k → VertexLabel) :
    Finset (ℕ ⊕ ℕ) := Finset.univ.image (fun i ↦ toCompanionLabel (v i))

theorem sampledCompanionLabels_nonempty {k : ℕ} (hk : 0 < k)
    (v : Fin k → VertexLabel) : (sampledCompanionLabels v).Nonempty :=
  ⟨toCompanionLabel (v ⟨0, hk⟩), Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩

theorem sampledCompanionLabels_subset (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    {v : Fin k → VertexLabel} (hv : ∀ i, v i ∈ vertexLabels x n) :
    sampledCompanionLabels v ⊆ Freezing1.vertexLabels (companionSchedule x) n := by
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
  exact toCompanionLabel_mem x hx (hv i)

/-- Distinct sampled birth times are no more numerous than the corresponding
distinct sampled vertices. The source minus-one convention is preserved. -/
theorem sampledBirthBlock_card_le_companionBlock (n a b : ℕ) {k : ℕ}
    (v : Fin k → VertexLabel) :
    (sampledBirthBlock n a b v).card ≤
      ((sampledCompanionLabels v).filter (fun w ↦
        a < Freezing1.birthTime n w ∧ Freezing1.birthTime n w ≤ b)).card := by
  let B := (sampledCompanionLabels v).filter (fun w ↦
    a < Freezing1.birthTime n w ∧ Freezing1.birthTime n w ≤ b)
  have hsub : sampledBirthBlock n a b v ⊆ B.image (Freezing1.birthTime n) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_image.mpr ⟨toCompanionLabel (v i), ?_, companion_birthTime n (v i)⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      by simpa only [companion_birthTime] using (Finset.mem_filter.mp hi).2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

/-- The fixed-mark conditional-block bound in the original vertex labels. -/
theorem source_probability_far_le_geometric_of_birth_occupancy
    (x : ℕ → ℤ) (hx : IsSigned x) {n k d p : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x))
    (hk : 0 < k) (hkn : k ≤ n) {M : ℝ} (hM : 0 < M)
    (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n)
    (hd : 0 < d) (hlength : tightnessBlockLength M n k ≤ d) (hp : 2 ≤ p)
    {u : VertexLabel} (hu : u ∈ vertexLabels x n) {v : Fin k → VertexLabel}
    (hv : ∀ i, v i ∈ vertexLabels x n)
    (hocc : ∀ i < n / d,
      M * Real.sqrt k < ((sampledBirthBlock n (i * d) ((i + 1) * d) v).card : ℝ)) :
    (jointLaw (companionSchedule x) n).real
      {ω | ∀ i, 2 * (p : ℝ) * d < sourceCoalescenceDistance n u (v i) ω} ≤
        (3 / 4 : ℝ) ^ ((p - 1) / 2) := by
  have hpop' : ∀ i ≤ n, (Freezing1.activeCount (companionSchedule x) i : ℝ) ≤
      M * Real.sqrt n := by simpa only [companion_activeCount x hx] using hpop
  have hocc' : ∀ i < n / d,
      M * Real.sqrt k < (((sampledCompanionLabels v).filter (fun w ↦
        i * d < Freezing1.birthTime n w ∧ Freezing1.birthTime n w ≤ (i + 1) * d)).card : ℝ) := by
    intro i hi
    exact (hocc i hi).trans_le (Nat.cast_le.mpr (sampledBirthBlock_card_le_companionBlock n _ _ v))
  have h := probability_far_le_geometric_of_birth_occupancy hn hk hkn hM hlarge hpop'
    hd hlength hp (toCompanionLabel_mem x hx hu) (sampledCompanionLabels_nonempty hk v)
    (sampledCompanionLabels_subset x hx hv) hocc'
  convert h using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sampledCompanionLabels, Finset.mem_image, Finset.mem_univ,
    true_and, forall_exists_index, forall_apply_eq_imp_iff, sourceCoalescenceDistance]

/-- One actual reverse history, one independent query vertex, and `k`
independent covering vertices. Repeated samples are allowed. -/
noncomputable def sampledCriticalCoverLaw (x : ℕ → ℤ) (n k : ℕ) :
    Measure (History × (VertexLabel × (Fin k → VertexLabel))) :=
  (jointLaw (companionSchedule x) n).prod
    ((uniformVertex x n).prod (uniformVertexVectorLaw x n k))

theorem sampledCriticalCoverLaw_probability (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : 0 ≤ activeCount x n) : IsProbabilityMeasure (sampledCriticalCoverLaw x n k) := by
  let := uniformVertex_isProbabilityMeasure x hx hs
  let := uniformVertexVectorLaw_probability x hx (k := k) hs
  unfold sampledCriticalCoverLaw
  infer_instance

def sampledCriticalCoverEvent (n k : ℕ) (R : ℝ) :
    Set (History × (VertexLabel × (Fin k → VertexLabel))) :=
  {q | ∀ i, R < sourceCoalescenceDistance n q.2.1 (q.2.2 i) q.1}

/-- The actual minimum distance to the nonempty sampled tuple, including
repeated labels. This is the source distance to the sampled set. -/
noncomputable def sampledCriticalCoverRadius (n k : ℕ) (hk : 0 < k)
    (q : History × (VertexLabel × (Fin k → VertexLabel))) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    (fun i ↦ sourceCoalescenceDistance n q.2.1 (q.2.2 i) q.1)

theorem sampledCriticalCoverRadius_eq_setDistance (n k : ℕ) (hk : 0 < k)
    (q : History × (VertexLabel × (Fin k → VertexLabel))) :
    sampledCriticalCoverRadius n k hk q = sourceCoalescenceSetDistance n q.2.1
      (Finset.univ.image q.2.2)
      ⟨q.2.2 ⟨0, hk⟩, Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩ q.1 := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.inf'_le _ hi
  · apply Finset.le_inf'
    intro i hi
    exact Finset.inf'_le _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem sampledCriticalCoverEvent_eq_radius (n k : ℕ) (hk : 0 < k) (R : ℝ) :
    sampledCriticalCoverEvent n k R = {q | R < sampledCriticalCoverRadius n k hk q} := by
  ext q
  change (∀ i, R < sourceCoalescenceDistance n q.2.1 (q.2.2 i) q.1) ↔
    R < sampledCriticalCoverRadius n k hk q
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
      (show (Finset.univ : Finset (Fin k)).Nonempty from ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
      (fun i ↦ sourceCoalescenceDistance n q.2.1 (q.2.2 i) q.1)
    change R < Finset.univ.inf' _ _
    rw [hi]
    exact h i
  · intro h i
    exact h.trans_le (Finset.inf'_le _ (Finset.mem_univ i))

theorem measurableSet_sampledCriticalCoverEvent (n k : ℕ) (R : ℝ) :
    MeasurableSet (sampledCriticalCoverEvent n k R) := by
  apply (measurable_from_prod_countable_left fun p ↦ ?_).setOf
  exact Measurable.forall fun i ↦ measurable_const.lt
    (measurable_sourceCoalescenceDistance n p.1 (p.2 i))

theorem uniformVertexVectorLaw_ae_legal (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : 0 ≤ activeCount x n) :
    ∀ᵐ v ∂uniformVertexVectorLaw x n k, ∀ i, v i ∈ vertexLabels x n := by
  let := uniformVertex_isProbabilityMeasure x hx hs
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) i).quasiMeasurePreserving.ae
    (uniformVertex_mem x hx hs)

/-- Occupancy failure plus the actual conditional block error bounds the
unconditioned iid covering failure. -/
theorem sampledCriticalCover_probability_le (x : ℕ → ℤ) (hx : IsSigned x)
    {n k p : ℕ} (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x))
    (hk : 6 ≤ k) (hkn : k ^ 3 ≤ n) {M : ℝ} (hM : 1 ≤ M)
    (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) (hp : 2 ≤ p) :
    (sampledCriticalCoverLaw x n k).real (sampledCriticalCoverEvent n k
      (2 * (p : ℝ) * criticalSamplingBlockLength M n k)) ≤
      criticalOccupancyError M k + (3 / 4 : ℝ) ^ ((p - 1) / 2) := by
  have hS (i : ℕ) (hi : i ≤ n) : 0 ≤ activeCount x i := by
    have h := Freezing1.activeCount_nonneg_of_le_extinctionTime
      ((show (i : ℕ∞) ≤ n by exact_mod_cast hi).trans hn)
    simpa only [companion_activeCount x hx] using h
  have hk0 : 0 < k := by omega
  have hkn' : k ≤ n := (le_self_pow (show 1 ≤ k by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hkn
  have hM0 : 0 < M := by linarith
  let := uniformVertex_isProbabilityMeasure x hx (hS n le_rfl)
  let := uniformVertexVectorLaw_probability x hx (k := k) (hS n le_rfl)
  let d := criticalSamplingBlockLength M n k
  have hd : 0 < d := by
    have h := criticalSamplingBlockLength_lower_bound M n k
    have hnR : (0 : ℝ) < n := by exact_mod_cast hk0.trans_le hkn'
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have : (0 : ℝ) < d := (by positivity : 0 < 16 * M * n / Real.sqrt k).trans_le h
    exact_mod_cast this
  have hlength : tightnessBlockLength M n k ≤ d := by
    unfold tightnessBlockLength d criticalSamplingBlockLength
    omega
  let ν := (uniformVertex x n).prod (uniformVertexVectorLaw x n k)
  let B : Set (VertexLabel × (Fin k → VertexLabel)) :=
    Set.univ ×ˢ criticalBirthOccupancyFailure M n k
  have hlegal : ∀ᵐ p ∂ν, p.1 ∈ vertexLabels x n ∧ ∀ i, p.2 i ∈ vertexLabels x n := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [uniformVertex_mem x hx (hS n le_rfl)] with u hu
    exact (uniformVertexVectorLaw_ae_legal x hx (hS n le_rfl)).mono fun _ hv ↦ ⟨hu, hv⟩
  have hbound : ∀ᵐ q ∂ν, q ∉ B → (jointLaw (companionSchedule x) n).real
      {ω | (ω, q) ∈ sampledCriticalCoverEvent n k (2 * (p : ℝ) * d)} ≤
        (3 / 4 : ℝ) ^ ((p - 1) / 2) := by
    filter_upwards [hlegal] with q hq hbad
    apply source_probability_far_le_geometric_of_birth_occupancy x hx hn hk0 hkn'
      hM0 hlarge hpop hd hlength hp hq.1 hq.2
    intro i hi
    by_contra h
    apply hbad
    exact ⟨Set.mem_univ _, ⟨i, hi, le_of_not_gt h⟩⟩
  have h := measureReal_prod_event_le_bad_add
    (measurableSet_sampledCriticalCoverEvent n k (2 * (p : ℝ) * d))
    (show MeasurableSet B from (Set.to_countable _).measurableSet)
    (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ ((p - 1) / 2)) hbound
  have hbad : ν.real B = (uniformVertexVectorLaw x n k).real (criticalBirthOccupancyFailure M n k) := by
    change ((uniformVertex x n).prod (uniformVertexVectorLaw x n k)
      (Set.univ ×ˢ criticalBirthOccupancyFailure M n k)).toReal = _
    rw [Measure.prod_prod, measure_univ, one_mul]
    rfl
  rw [hbad] at h
  exact h.trans (add_le_add ((measureReal_mono (criticalBirthOccupancyFailure_subset x M n k)).trans
    (criticalFrozenOccupancyFailure_probability_le x hx hk hkn hS hM hpop)) le_rfl)

/-- Both repaired failure terms are negligible at the source order. -/
theorem tendsto_scaled_criticalCoverError {M : ℝ} (hM : 0 < M) :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ 4 *
      (criticalOccupancyError M k + (3 / 4 : ℝ) ^ criticalIsolationTrials k))
      atTop (𝓝 0) := by
  simpa only [mul_add, zero_add] using
    (tendsto_scaled_criticalOccupancyError hM).add tendsto_scaled_criticalIsolationProbability

/-- N13's uniform finite estimate under the actual reverse-tree and iid
sampling law. The threshold is chosen from the fixed population constant
before the horizon, signed row, or sampled vertices. -/
theorem eventually_uniform_sampledCriticalCover_probability_le
    {M : ℝ} (hM : 1 ≤ M) :
    ∃ K : ℕ, 6 ≤ K ∧ ∀ k ≥ K, ∀ n, k ^ 3 ≤ n → ∀ x : ℕ → ℤ,
      IsSigned x → (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x) →
      (∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) →
      (sampledCriticalCoverLaw x n k).real
        (sampledCriticalCoverEvent n k ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k)) ≤
          1 / (k : ℝ) ^ 4 := by
  have hM0 : 0 < M := by linarith
  obtain ⟨K₁, _, hK₁⟩ := exists_tightness_sample_threshold hM0
  obtain ⟨K₂, hK₂⟩ := eventually_uniform_criticalBlockRadius hM0.le
  obtain ⟨K₃, hK₃⟩ := eventually_atTop.mp
    ((tendsto_scaled_criticalCoverError hM0).eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 6 (max K₁ (max K₂ K₃)), le_max_left _ _, ?_⟩
  intro k hk n hkn x hx hn hpop
  have hk6 : 6 ≤ k := (le_max_left _ _).trans hk
  have hkrest : max K₁ (max K₂ K₃) ≤ k := (le_max_right _ _).trans hk
  have hk₁ : K₁ ≤ k := (le_max_left _ _).trans hkrest
  have hk₂ : K₂ ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hkrest)
  have hk₃ : K₃ ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hkrest)
  obtain ⟨hk0, hlarge⟩ := hK₁ k hk₁
  have hkn' : k ≤ n := (le_self_pow (show 1 ≤ k by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hkn
  obtain ⟨hp, hrad⟩ := hK₂ k hk₂
  have hs : 0 ≤ activeCount x n := by
    simpa only [companion_activeCount x hx] using
      Freezing1.activeCount_nonneg_of_le_extinctionTime hn
  let := sampledCriticalCoverLaw_probability x hx (k := k) hs
  have hR : 2 * (criticalIsolationWindow k : ℝ) * criticalSamplingBlockLength M n k ≤
      (n : ℝ) * Real.log k ^ 2 / Real.sqrt k := by
    rw [show (n : ℝ) * Real.log k ^ 2 / Real.sqrt k = Real.log k ^ 2 / Real.sqrt k * n by ring]
    exact hrad n hkn'
  have hsub : sampledCriticalCoverEvent n k ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k) ⊆
      sampledCriticalCoverEvent n k
        (2 * (criticalIsolationWindow k : ℝ) * criticalSamplingBlockLength M n k) := by
    intro q hq i
    exact hR.trans_lt (hq i)
  have hprob := (measureReal_mono hsub).trans
    (sampledCriticalCover_probability_le x hx hn hk6 hkn hM hlarge hpop hp)
  apply hprob.trans
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  apply (le_div_iff₀ (pow_pos hkR 4)).mpr
  simpa only [criticalIsolationTrials, mul_comm] using (hK₃ k hk₃).le

/-- The source array formulation of N13, with its literal cube-root range.
Only positive horizons are constrained; the initial row is irrelevant.
The local profile hypotheses are not needed for this stronger finite estimate. -/
theorem critical_sampled_cover_probability_uniform_positive_horizons
    {x : ℕ → ℕ → ℤ} {M : ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hpop : ∀ n : ℕ, 0 < n → ∀ i ≤ n,
      (activeCount (x n) i : ℝ) ≤ M * Real.sqrt n) :
    ∃ K : ℕ, 6 ≤ K ∧ ∀ k ≥ K, ∀ n : ℕ,
      (k : ℝ) ≤ (n : ℝ) ^ (1 / (3 : ℝ)) →
      (sampledCriticalCoverLaw (x n) n k).real
        (sampledCriticalCoverEvent n k ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k)) ≤
          1 / (k : ℝ) ^ 4 := by
  obtain ⟨K, hK, hbound⟩ := eventually_uniform_sampledCriticalCover_probability_le
    (show 1 ≤ max 1 M from le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro k hk n hkn
  have hk6 := hK.trans hk
  have hkn' := (TrackedClusters.nat_le_cube_root_iff k n).mp hkn
  have hkn'' : k ≤ n := (le_self_pow (show 1 ≤ k by omega)
    (by norm_num : (3 : ℕ) ≠ 0)).trans hkn'
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < k) hkn''
  exact hbound k hk n hkn' (x n) (hx n hn).1
    (companion_before_extinction (x n) (hx n hn).1 (hx n hn).2).le
    (fun i hi ↦ (hpop n hn i hi).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 M) (Real.sqrt_nonneg n)))

/-- N13, `tightness time estimate`, under the source population hypothesis
`max_{1 ≤ k ≤ n} S^n_k = O(√n)` and survival `τ(Xⁿ) > n`. The query vertex and the
covering vertices are independent uniform vertices, collisions included. -/
theorem critical_sampled_cover_probability_of_isBigO {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt n)) :
    ∃ K : ℕ, 6 ≤ K ∧ ∀ k ≥ K, ∀ n : ℕ,
      (k : ℝ) ≤ (n : ℝ) ^ (1 / (3 : ℝ)) →
      (sampledCriticalCoverLaw (x n) n k).real
        (sampledCriticalCoverEvent n k ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k)) ≤
          1 / (k : ℝ) ^ 4 := by
  obtain ⟨M, -, hM⟩ := exists_uniform_population_bound (fun n hn ↦ (hx n hn).1) hpop
  exact critical_sampled_cover_probability_uniform_positive_horizons hx hM

end Freezing2
