module

public import Freezing2.Probability.CriticalSampledCover
public import Freezing2.Probability.IidSequence
public import Freezing2.Analysis.ChainingSeries

/-!
# Dyadic chaining for the critical sample net

Step 1 of the source's tightness proof (`eq:stepone`, inventory U31). The
actual reverse history is paired with an independent iid sequence of uniform
vertices. Fresh dyadic blocks are controlled by N13 with a random query vertex,
the last net by N13 with a fixed query vertex and a union bound over all
vertices, and chaining uses the almost-sure triangle inequality of `Δⁿ`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-! ### N13 for a fixed query vertex -/

/-- The covering failure event for a fixed query vertex and a sampled tuple. -/
def fixedCriticalCoverEvent (n k : ℕ) (u : VertexLabel) (R : ℝ) :
    Set (History × (Fin k → VertexLabel)) :=
  {q | ∀ i, R < sourceCoalescenceDistance n u (q.2 i) q.1}

theorem measurableSet_fixedCriticalCoverEvent (n k : ℕ) (u : VertexLabel) (R : ℝ) :
    MeasurableSet (fixedCriticalCoverEvent n k u R) := by
  apply (measurable_from_prod_countable_left fun v ↦ ?_).setOf
  exact Measurable.forall fun i ↦ measurable_const.lt
    (measurable_sourceCoalescenceDistance n u (v i))

/-- The fixed-query form of the finite N13 estimate: the conditional block
bound is uniform over legal query vertices, so no averaging over the query
vertex is needed. -/
theorem fixedCriticalCover_probability_le (x : ℕ → ℤ) (hx : IsSigned x)
    {n k p : ℕ} (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x))
    (hk : 6 ≤ k) (hkn : k ^ 3 ≤ n) {M : ℝ} (hM : 1 ≤ M)
    (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) (hp : 2 ≤ p)
    {u : VertexLabel} (hu : u ∈ vertexLabels x n) :
    ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n k)).real
      (fixedCriticalCoverEvent n k u (2 * (p : ℝ) * criticalSamplingBlockLength M n k)) ≤
      criticalOccupancyError M k + (3 / 4 : ℝ) ^ ((p - 1) / 2) := by
  have hS (i : ℕ) (hi : i ≤ n) : 0 ≤ activeCount x i := by
    have h := Freezing1.activeCount_nonneg_of_le_extinctionTime
      ((show (i : ℕ∞) ≤ n by exact_mod_cast hi).trans hn)
    simpa only [companion_activeCount x hx] using h
  have hk0 : 0 < k := by omega
  have hkn' : k ≤ n := (le_self_pow (show 1 ≤ k by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hkn
  have hM0 : 0 < M := by linarith
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
  have hbound : ∀ᵐ v ∂uniformVertexVectorLaw x n k,
      v ∉ criticalBirthOccupancyFailure M n k → (jointLaw (companionSchedule x) n).real
        {ω | (ω, v) ∈ fixedCriticalCoverEvent n k u (2 * (p : ℝ) * d)} ≤
          (3 / 4 : ℝ) ^ ((p - 1) / 2) := by
    filter_upwards [uniformVertexVectorLaw_ae_legal x hx (hS n le_rfl)] with v hv hbad
    apply source_probability_far_le_geometric_of_birth_occupancy x hx hn hk0 hkn'
      hM0 hlarge hpop hd hlength hp hu hv
    intro i hi
    by_contra h
    exact hbad ⟨i, hi, le_of_not_gt h⟩
  have h := measureReal_prod_event_le_bad_add
    (measurableSet_fixedCriticalCoverEvent n k u (2 * (p : ℝ) * d))
    (show MeasurableSet (criticalBirthOccupancyFailure M n k) from
      (Set.to_countable _).measurableSet)
    (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ ((p - 1) / 2)) hbound
  exact h.trans (add_le_add ((measureReal_mono
    (criticalBirthOccupancyFailure_subset x M n k)).trans
    (criticalFrozenOccupancyFailure_probability_le x hx hk hkn hS hM hpop)) le_rfl)

/-- N13 for a fixed query vertex, uniformly over legal query vertices. -/
theorem eventually_uniform_fixedCriticalCover_probability_le
    {M : ℝ} (hM : 1 ≤ M) :
    ∃ K : ℕ, 6 ≤ K ∧ ∀ k ≥ K, ∀ n, k ^ 3 ≤ n → ∀ x : ℕ → ℤ,
      IsSigned x → (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x) →
      (∀ i ≤ n, (activeCount x i : ℝ) ≤ M * Real.sqrt n) →
      ∀ u ∈ vertexLabels x n,
      ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n k)).real
        (fixedCriticalCoverEvent n k u ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k)) ≤
          1 / (k : ℝ) ^ 4 := by
  have hM0 : 0 < M := by linarith
  obtain ⟨K₁, _, hK₁⟩ := exists_tightness_sample_threshold hM0
  obtain ⟨K₂, hK₂⟩ := eventually_uniform_criticalBlockRadius hM0.le
  obtain ⟨K₃, hK₃⟩ := eventually_atTop.mp
    ((tendsto_scaled_criticalCoverError hM0).eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨max 6 (max K₁ (max K₂ K₃)), le_max_left _ _, ?_⟩
  intro k hk n hkn x hx hn hpop u hu
  have hk6 : 6 ≤ k := (le_max_left _ _).trans hk
  have hkrest : max K₁ (max K₂ K₃) ≤ k := (le_max_right _ _).trans hk
  have hk₁ : K₁ ≤ k := (le_max_left _ _).trans hkrest
  have hk₂ : K₂ ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hkrest)
  have hk₃ : K₃ ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hkrest)
  obtain ⟨hk0, hlarge⟩ := hK₁ k hk₁
  have hkn' : k ≤ n := (le_self_pow (show 1 ≤ k by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hkn
  obtain ⟨hp, hrad⟩ := hK₂ k hk₂
  have hR : 2 * (criticalIsolationWindow k : ℝ) * criticalSamplingBlockLength M n k ≤
      (n : ℝ) * Real.log k ^ 2 / Real.sqrt k := by
    rw [show (n : ℝ) * Real.log k ^ 2 / Real.sqrt k = Real.log k ^ 2 / Real.sqrt k * n by ring]
    exact hrad n hkn'
  have hsub : fixedCriticalCoverEvent n k u ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k) ⊆
      fixedCriticalCoverEvent n k u
        (2 * (criticalIsolationWindow k : ℝ) * criticalSamplingBlockLength M n k) := by
    intro q hq i
    exact hR.trans_lt (hq i)
  have hs : 0 ≤ activeCount x n := by
    simpa only [companion_activeCount x hx] using
      Freezing1.activeCount_nonneg_of_le_extinctionTime hn
  let := uniformVertexVectorLaw_probability x hx (k := k) hs
  have hprob := (measureReal_mono hsub).trans
    (fixedCriticalCover_probability_le x hx hn hk6 hkn hM hlarge hpop hp hu)
  apply hprob.trans
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  apply (le_div_iff₀ (pow_pos hkR 4)).mpr
  simpa only [criticalIsolationTrials, mul_comm] using (hK₃ k hk₃).le

/-! ### The actual reverse history with an iid vertex sequence -/

/-- The source's `V₁, V₂, …` (here indexed from zero), independent of the
actual reverse history. -/
noncomputable def criticalSequenceLaw (x : ℕ → ℤ) (n : ℕ) :
    Measure (History × (ℕ → VertexLabel)) :=
  (jointLaw (companionSchedule x) n).prod
    (Measure.infinitePi (fun _ : ℕ ↦ uniformVertex x n))

theorem criticalSequenceLaw_probability (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) : IsProbabilityMeasure (criticalSequenceLaw x n) := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  unfold criticalSequenceLaw
  infer_instance

theorem criticalSequenceLaw_map_prefix (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) (m : ℕ) :
    (criticalSequenceLaw x n).map (fun q ↦ (q.1, fun j : Fin m ↦ q.2 j)) =
      (jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n m) := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have h := Measure.map_prod_map (jointLaw (companionSchedule x) n)
    (Measure.infinitePi (fun _ : ℕ ↦ uniformVertex x n)) measurable_id
    (measurable_reindex (fun j : Fin m ↦ (j : ℕ)))
  rw [Measure.map_id, infinitePi_map_prefix] at h
  exact h.symm

theorem criticalSequenceLaw_map_fresh (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) {m i : ℕ} (hi : m ≤ i) :
    (criticalSequenceLaw x n).map (fun q ↦ (q.1, (q.2 i, fun j : Fin m ↦ q.2 j))) =
      sampledCriticalCoverLaw x n m := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have h := Measure.map_prod_map (jointLaw (companionSchedule x) n)
    (Measure.infinitePi (fun _ : ℕ ↦ uniformVertex x n)) measurable_id
    ((measurable_pi_apply i).prodMk (measurable_reindex (fun j : Fin m ↦ (j : ℕ))))
  rw [Measure.map_id, infinitePi_map_fresh_prefix _ hi] at h
  exact h.symm

/-- A fresh coordinate is an independent uniform query vertex for the prefix. -/
theorem criticalSequenceLaw_fresh_cover (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) {m i : ℕ} (hi : m ≤ i) (R : ℝ) :
    (criticalSequenceLaw x n).real
      {q | ∀ l < m, R < sourceCoalescenceDistance n (q.2 i) (q.2 l) q.1} =
      (sampledCriticalCoverLaw x n m).real (sampledCriticalCoverEvent n m R) := by
  have hf : Measurable (fun q : History × (ℕ → VertexLabel) ↦
      (q.1, (q.2 i, fun j : Fin m ↦ q.2 j))) :=
    measurable_fst.prodMk (((measurable_pi_apply i).comp measurable_snd).prodMk
      ((measurable_reindex (fun j : Fin m ↦ (j : ℕ))).comp measurable_snd))
  rw [← criticalSequenceLaw_map_fresh x hx hs hi,
    map_measureReal_apply hf (measurableSet_sampledCriticalCoverEvent n m R)]
  congr 1
  ext q
  simp only [sampledCriticalCoverEvent, Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_iff]

/-- The prefix with a fixed query vertex has the finite iid law. -/
theorem criticalSequenceLaw_prefix_fixed (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) (m : ℕ) (u : VertexLabel) (R : ℝ) :
    (criticalSequenceLaw x n).real
      {q | ∀ l < m, R < sourceCoalescenceDistance n u (q.2 l) q.1} =
      ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n m)).real
        (fixedCriticalCoverEvent n m u R) := by
  have hf : Measurable (fun q : History × (ℕ → VertexLabel) ↦
      (q.1, fun j : Fin m ↦ q.2 j)) :=
    measurable_fst.prodMk ((measurable_reindex (fun j : Fin m ↦ (j : ℕ))).comp measurable_snd)
  rw [← criticalSequenceLaw_map_prefix x hx hs m,
    map_measureReal_apply hf (measurableSet_fixedCriticalCoverEvent n m u R)]
  congr 1
  ext q
  simp only [fixedCriticalCoverEvent, Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_iff]

/-- The probability of a source event for `V₁, …, V_m` computed on the sequence. -/
theorem criticalSequenceLaw_prefix_event (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) (m : ℕ) {E : Set (History × (Fin m → VertexLabel))}
    (hE : MeasurableSet E) :
    ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n m)) E =
      criticalSequenceLaw x n {q | (q.1, fun j : Fin m ↦ q.2 j) ∈ E} := by
  have hf : Measurable (fun q : History × (ℕ → VertexLabel) ↦
      (q.1, fun j : Fin m ↦ q.2 j)) :=
    measurable_fst.prodMk ((measurable_reindex (fun j : Fin m ↦ (j : ℕ))).comp measurable_snd)
  rw [← criticalSequenceLaw_map_prefix x hx hs m, Measure.map_apply hf hE]
  rfl

/-! ### Union bounds for the dyadic blocks and the last net -/

/-- A new dyadic block `[m, 2m)` has a far point from the prefix of length `m`
with probability at most `m` times the N13 covering failure probability. -/
theorem criticalSequenceLaw_block_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) (m : ℕ) (R : ℝ) :
    (criticalSequenceLaw x n).real {q | ∃ i ∈ Finset.Ico m (2 * m), ∀ l < m,
      R < sourceCoalescenceDistance n (q.2 i) (q.2 l) q.1} ≤
      m * (sampledCriticalCoverLaw x n m).real (sampledCriticalCoverEvent n m R) := by
  have := criticalSequenceLaw_probability x hx hs
  have he : {q : History × (ℕ → VertexLabel) | ∃ i ∈ Finset.Ico m (2 * m), ∀ l < m,
      R < sourceCoalescenceDistance n (q.2 i) (q.2 l) q.1} =
      ⋃ i ∈ Finset.Ico m (2 * m),
        {q | ∀ l < m, R < sourceCoalescenceDistance n (q.2 i) (q.2 l) q.1} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [he]
  refine (measureReal_biUnion_finset_le _ _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun i hi ↦ criticalSequenceLaw_fresh_cover x hx hs
    (Finset.mem_Ico.mp hi).1 R), Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  congr 2
  omega

/-- The last net: a union bound over all actual vertices. -/
theorem criticalSequenceLaw_lastNet_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) (m : ℕ) (R c : ℝ)
    (hc : ∀ u ∈ vertexLabels x n,
      ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n m)).real
        (fixedCriticalCoverEvent n m u R) ≤ c) :
    (criticalSequenceLaw x n).real {q | ∃ u ∈ vertexLabels x n, ∀ l < m,
      R < sourceCoalescenceDistance n u (q.2 l) q.1} ≤ (vertexLabels x n).card * c := by
  have := criticalSequenceLaw_probability x hx hs
  have he : {q : History × (ℕ → VertexLabel) | ∃ u ∈ vertexLabels x n, ∀ l < m,
      R < sourceCoalescenceDistance n u (q.2 l) q.1} =
      ⋃ u ∈ vertexLabels x n, {q | ∀ l < m, R < sourceCoalescenceDistance n u (q.2 l) q.1} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [he]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _u ∈ vertexLabels x n, c := Finset.sum_le_sum fun u hu ↦
        (criticalSequenceLaw_prefix_fixed x hx hs m u R).le.trans (hc u hu)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Almost-sure metric facts -/

theorem criticalSequenceLaw_ae_legal (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) :
    ∀ᵐ q ∂criticalSequenceLaw x n, ∀ i, q.2 i ∈ vertexLabels x n := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have hseq : ∀ᵐ V ∂Measure.infinitePi (fun _ : ℕ ↦ uniformVertex x n),
      ∀ i, V i ∈ vertexLabels x n := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ uniformVertex x n) i
      ).quasiMeasurePreserving.ae (uniformVertex_mem x hx hs)
  exact (measurePreserving_snd (μ := jointLaw (companionSchedule x) n)).quasiMeasurePreserving.ae
    hseq

theorem criticalSequenceLaw_ae_triangle (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x))
    (hs : 0 ≤ activeCount x n) :
    ∀ᵐ q ∂criticalSequenceLaw x n, ∀ u ∈ vertexLabels x n, ∀ v ∈ vertexLabels x n,
      ∀ w ∈ vertexLabels x n, sourceCoalescenceDistance n u w q.1 ≤
        sourceCoalescenceDistance n u v q.1 + sourceCoalescenceDistance n v w q.1 := by
  have := uniformVertex_isProbabilityMeasure x hx hs
  have hJ : ∀ᵐ ω ∂jointLaw (companionSchedule x) n, ∀ u v w : VertexLabel,
      u ∈ vertexLabels x n → v ∈ vertexLabels x n → w ∈ vertexLabels x n →
      sourceCoalescenceDistance n u w ω ≤
        sourceCoalescenceDistance n u v ω + sourceCoalescenceDistance n v w ω := by
    refine ae_all_iff.mpr fun u ↦ ae_all_iff.mpr fun v ↦ ae_all_iff.mpr fun w ↦ ?_
    by_cases hu : u ∈ vertexLabels x n
    · by_cases hv : v ∈ vertexLabels x n
      · by_cases hw : w ∈ vertexLabels x n
        · filter_upwards [jointLaw_sourceCoalescenceDistance_triangle x hx hn hu hv hw] with ω h
          exact fun _ _ _ ↦ h
        · exact Eventually.of_forall fun _ _ _ h ↦ absurd h hw
      · exact Eventually.of_forall fun _ _ h _ ↦ absurd h hv
    · exact Eventually.of_forall fun _ h _ _ ↦ absurd h hu
  filter_upwards [(measurePreserving_fst (ν := Measure.infinitePi
    (fun _ : ℕ ↦ uniformVertex x n))).quasiMeasurePreserving.ae hJ] with q hq
  exact fun u hu v hv w hw ↦ hq u v w hu hv hw

end Freezing2
