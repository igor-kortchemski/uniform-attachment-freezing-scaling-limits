module

public import Freezing2.Probability.SupercriticalMatrixApproximation
public import Freezing2.Probability.ReversePaper

/-!
# Root-inclusive sampled matrices

The distinguished index `none` denotes the actual terminal tree root; `some i`
denotes the `i`-th independent uniform sample. The stored terminal depths are
proved to be distances from one common actual graph root before they are used
as the corresponding matrix entries.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- A deterministic choice of the common root on valid terminal histories. -/
def reverseTerminalRoot (n : ℕ) (ω : History) : ℕ ⊕ ℕ :=
  (forestAt n 0 ω).root (toCompanionLabel (Sum.inr 1))

theorem active_one_mem_vertexLabels (x : ℕ → ℤ) {n : ℕ} (hs : SurvivesThrough x n) :
    Sum.inr 1 ∈ vertexLabels x n := by
  have hp := hs n le_rfl
  simp only [vertexLabels, Finset.inr_mem_disjSum, Finset.mem_Ioc]
  constructor
  · omega
  · have hi : (1 : ℤ) ≤ activeCount x n := by omega
    exact (Int.le_toNat hp.le).mpr hi

/-- The terminal height of every legal label is its distance from the same
actual root, not merely its depth in an unspecified component. -/
theorem heightAt_zero_eq_terminalRoot_distance (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) {v : VertexLabel} (hv : v ∈ vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw (companionSchedule x) n,
      heightAt n 0 (toCompanionLabel v) ω =
        ((forestAt n 0 ω).graph.dist (reverseTerminalRoot n ω) (toCompanionLabel v) : ℝ) := by
  have hn := (companion_before_extinction x hx hs).le
  have hv' := toCompanionLabel_mem x hx hv
  have hroot := toCompanionLabel_mem x hx (active_one_mem_vertexLabels x hs)
  filter_upwards [jointLaw_connected_zero hn hroot hv', jointLaw_members hn hroot hv']
    with ω hconn hmem
  have hdepth := (forestAt n 0 ω).depth_eq_dist (hmem 0 (Nat.zero_le _)).2
  change (forestAt n 0 ω).root (toCompanionLabel (Sum.inr 1)) =
    (forestAt n 0 ω).root (toCompanionLabel v) at hconn
  change ((forestAt n 0 ω).depth (toCompanionLabel v) : ℝ) = _
  rw [hdepth, reverseTerminalRoot, hconn]

/-- The actual source root and all sampled vertex labels in one index type. -/
def rootAugmentedLabel {k : ℕ} (n : ℕ) (q : History × (Fin k → VertexLabel)) :
    Option (Fin k) → (ℕ ⊕ ℕ)
  | none => reverseTerminalRoot n q.1
  | some i => toCompanionLabel (q.2 i)

/-- The root-inclusive scaled distance matrix. The following theorem identifies
every entry with the graph-distance matrix of `rootAugmentedLabel`. -/
noncomputable def rootedSampledDistanceMatrix (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) : Option (Fin k) → Option (Fin k) → ℝ
  | none, none => 0
  | none, some j => (n : ℝ) ^ (α - 1) * heightAt n 0 (toCompanionLabel (q.2 j)) q.1
  | some i, none => (n : ℝ) ^ (α - 1) * heightAt n 0 (toCompanionLabel (q.2 i)) q.1
  | some i, some j => sampledDistanceMatrix α n k q i j

/-- The corrected star matrix, with a zero root branch and zero diagonal. -/
noncomputable def rootedSampledStarMatrix (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) : Option (Fin k) → Option (Fin k) → ℝ
  | none, none => 0
  | none, some j => normalizedHarmonicPrefix x α n (birthTime n (q.2 j))
  | some i, none => normalizedHarmonicPrefix x α n (birthTime n (q.2 i))
  | some i, some j => sampledStarMatrix x α n k q i j

theorem sampledReverseVectorLaw_ae_legal (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : SurvivesThrough x n) :
    ∀ᵐ q ∂sampledReverseVectorLaw x n k, ∀ i, q.2 i ∈ vertexLabels x n := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hi (i : Fin k) : ∀ᵐ v ∂Measure.pi (fun _ : Fin k ↦ uniformVertex x n),
      v i ∈ vertexLabels x n :=
    (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) i).quasiMeasurePreserving.ae
      (uniformVertex_mem x hx (hs n le_rfl).le)
  have h := ae_all_iff.mpr hi
  apply (Measure.ae_prod_iff_ae_ae
    ((show MeasurableSet {v : Fin k → VertexLabel | ∀ i, v i ∈ vertexLabels x n} from
      (Set.to_countable _).measurableSet).preimage measurable_snd)).mpr
  exact Eventually.of_forall fun _ ↦ h

theorem rootedSampledDistanceMatrix_eq_graphDistance
    (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ} (hs : SurvivesThrough x n) (α : ℝ) :
    ∀ᵐ q ∂sampledReverseVectorLaw x n k, ∀ i j,
      rootedSampledDistanceMatrix α n k q i j = (n : ℝ) ^ (α - 1) *
        ((forestAt n 0 q.1).graph.dist (rootAugmentedLabel n q i) (rootAugmentedLabel n q j) : ℝ) := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hh : ∀ᵐ ω ∂jointLaw (companionSchedule x) n,
      ∀ v, v ∈ vertexLabels x n → heightAt n 0 (toCompanionLabel v) ω =
        ((forestAt n 0 ω).graph.dist (reverseTerminalRoot n ω) (toCompanionLabel v) : ℝ) := by
    apply ae_all_iff.mpr
    intro v
    by_cases hv : v ∈ vertexLabels x n
    · exact (heightAt_zero_eq_terminalRoot_distance x hx hs hv).mono fun _ h _ ↦ h
    · exact Eventually.of_forall fun _ h ↦ (hv h).elim
  have hlift : ∀ᵐ q ∂sampledReverseVectorLaw x n k,
      ∀ v, v ∈ vertexLabels x n → heightAt n 0 (toCompanionLabel v) q.1 =
        ((forestAt n 0 q.1).graph.dist (reverseTerminalRoot n q.1) (toCompanionLabel v) : ℝ) := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := jointLaw (companionSchedule x) n)
      (ν := Measure.pi (fun _ : Fin k ↦ uniformVertex x n))).ae hh
  filter_upwards [hlift, sampledReverseVectorLaw_ae_legal x hx hs] with q hq hv
  intro i j
  cases i with
  | none =>
    cases j with
    | none => simp [rootedSampledDistanceMatrix, rootAugmentedLabel]
    | some j => simp only [rootedSampledDistanceMatrix, rootAugmentedLabel, hq (q.2 j) (hv j)]
  | some i =>
    cases j with
    | none =>
      simp only [rootedSampledDistanceMatrix, rootAugmentedLabel, hq (q.2 i) (hv i)]
      rw [SimpleGraph.dist_comm]
    | some j => rfl

theorem measurable_rootedSampledDistanceMatrix (α : ℝ) (n k : ℕ) :
    Measurable (rootedSampledDistanceMatrix α n k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  cases i <;> cases j
  · exact measurable_const
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_heightAt n 0 (toCompanionLabel (v _))).const_mul _
  · apply measurable_from_prod_countable_left
    intro v
    exact (measurable_heightAt n 0 (toCompanionLabel (v _))).const_mul _
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_sampledDistanceMatrix α n k))

theorem measurable_rootedSampledStarMatrix (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ) :
    Measurable (rootedSampledStarMatrix x α n k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  cases i <;> cases j
  · exact measurable_const
  · exact (measurable_of_countable (fun v : Fin k → VertexLabel ↦
      normalizedHarmonicPrefix x α n (birthTime n (v _)))).comp measurable_snd
  · exact (measurable_of_countable (fun v : Fin k → VertexLabel ↦
      normalizedHarmonicPrefix x α n (birthTime n (v _)))).comp measurable_snd
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_sampledStarMatrix x α n k))

/-- Root entries have the same branch centre, with half the inclusive endpoint. -/
theorem scaled_rootHeight_branch_error_le (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    {v : VertexLabel} (hv : v ∈ vertexLabels (x n) n) (ω : History) :
    |(n : ℝ) ^ (α - 1) * heightAt n 0 (toCompanionLabel v) ω -
      normalizedHarmonicPrefix x α n (birthTime n v)| ≤
      (n : ℝ) ^ (α - 1) * reverseHeightErrorMax x n ω + (n : ℝ) ^ (α - 1) / 2 := by
  have hs : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh := height_error_le_reverseHeightErrorMax x n 0 hv (Nat.zero_le _) ω
  have hm := mul_le_mul_of_nonneg_left hh hs
  have he : (n : ℝ) ^ (α - 1) * heightAt n 0 (toCompanionLabel v) ω -
      normalizedHarmonicPrefix x α n (birthTime n v) =
      (n : ℝ) ^ (α - 1) * (heightAt n 0 (toCompanionLabel v) ω -
        inclusiveHarmonic (x n) 0 (birthTime n v) / 2) + (n : ℝ) ^ (α - 1) / 2 := by
    rw [inclusiveHarmonic_eq _ (Nat.zero_le _)]
    simp only [activeCount_zero, Int.cast_one, inv_one, Nat.sub_zero, normalizedHarmonicPrefix]
    ring
  rw [he]
  have ht := abs_add_le
    ((n : ℝ) ^ (α - 1) * (heightAt n 0 (toCompanionLabel v) ω -
      inclusiveHarmonic (x n) 0 (birthTime n v) / 2)) ((n : ℝ) ^ (α - 1) / 2)
  rw [abs_mul, abs_of_nonneg hs, abs_of_nonneg (div_nonneg hs (by norm_num))] at ht
  linarith

theorem sampledReverseVectorLaw_history_event (x : ℕ → ℤ) (hx : IsSigned x) {n k : ℕ}
    (hs : SurvivesThrough x n) (E : Set History) :
    (sampledReverseVectorLaw x n k).real {q | q.1 ∈ E} =
      (jointLaw (companionSchedule x) n).real E := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have he : {q : History × (Fin k → VertexLabel) | q.1 ∈ E} = E ×ˢ univ := by
    ext q
    simp
  rw [he, sampledReverseVectorLaw]
  simp [measureReal_prod_prod]

theorem rootedSampledMatrix_error_le (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (q : History × (Fin k → VertexLabel)) (hq : ∀ i, q.2 i ∈ vertexLabels (x n) n) :
    dist (rootedSampledDistanceMatrix α n k q) (rootedSampledStarMatrix x α n k q) ≤
      max (dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q))
        ((n : ℝ) ^ (α - 1) * reverseHeightErrorMax x n q.1 + (n : ℝ) ^ (α - 1) / 2) := by
  have hnonneg : 0 ≤ max
      (dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q))
      ((n : ℝ) ^ (α - 1) * reverseHeightErrorMax x n q.1 + (n : ℝ) ^ (α - 1) / 2) :=
    dist_nonneg.trans (le_max_left _ _)
  apply (dist_pi_le_iff hnonneg).mpr
  intro i
  apply (dist_pi_le_iff hnonneg).mpr
  intro j
  cases i with
  | none =>
    cases j with
    | none => simpa only [rootedSampledDistanceMatrix, rootedSampledStarMatrix, dist_self] using hnonneg
    | some j =>
      simpa only [rootedSampledDistanceMatrix, rootedSampledStarMatrix, Real.dist_eq] using
        (scaled_rootHeight_branch_error_le x α n (hq j) q.1).trans
          (le_max_right
            (dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)) _)
  | some i =>
    cases j with
    | none =>
      simpa only [rootedSampledDistanceMatrix, rootedSampledStarMatrix, Real.dist_eq] using
        (scaled_rootHeight_branch_error_le x α n (hq i) q.1).trans
          (le_max_right
            (dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)) _)
    | some j =>
      have hi := dist_le_pi_dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q) i
      have hj := dist_le_pi_dist (sampledDistanceMatrix α n k q i)
        (sampledStarMatrix x α n k q i) j
      exact (hj.trans hi).trans (le_max_left _ _)

/-- The complete corrected M06 approximation includes the actual root row and
column, rather than only the iid nonroot block. -/
theorem tendsto_rootedSampledStarMatrix_error_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseVectorLaw (x n) n k).real
      {q | ε < dist (rootedSampledDistanceMatrix α n k q) (rootedSampledStarMatrix x α n k q)})
      atTop (𝓝 0) := by
  have hm := tendsto_sampledStarMatrix_error_probability hx hαhalf hα1 hL1 hpos h2 k hε
  have hh := tendsto_reverseHeightErrorMax hx (show 0 < α by linarith) hα1 hL1 hpos
    (show 0 < ε / 2 by positivity)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _
    (show Tendsto (fun n ↦
      (sampledReverseVectorLaw (x n) n k).real
        {q | ε < dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)} +
      (jointLaw (companionSchedule (x n)) n).real
        {ω | ε / 2 * (n : ℝ) ^ (1 - α) < reverseHeightErrorMax x n ω}) atTop (𝓝 0) from
      by simpa using hm.add hh)
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_height_inverse_scale hα1).eventually_lt_const hε] with n hn hscale
  let μ := sampledReverseVectorLaw (x n) n k
  let := sampledReverseVectorLaw_probability (x n) (hx n).1 (k := k) (hx n).2
  let A : Set (History × (Fin k → VertexLabel)) :=
    {q | ε < dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q)}
  let B : Set (History × (Fin k → VertexLabel)) :=
    {q | ε / 2 * (n : ℝ) ^ (1 - α) < reverseHeightErrorMax x n q.1}
  have hsub : {q | ε < dist (rootedSampledDistanceMatrix α n k q)
      (rootedSampledStarMatrix x α n k q)} ≤ᵐ[μ] A ∪ B := by
    filter_upwards [sampledReverseVectorLaw_ae_legal (x n) (hx n).1 (k := k) (hx n).2] with q hq
    intro he
    by_contra hbad
    have ha : dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q) ≤ ε :=
      le_of_not_gt fun h ↦ hbad (Or.inl h)
    have hb : reverseHeightErrorMax x n q.1 ≤ ε / 2 * (n : ℝ) ^ (1 - α) :=
      le_of_not_gt fun h ↦ hbad (Or.inr h)
    have hs : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hprod : (n : ℝ) ^ (α - 1) * (n : ℝ) ^ (1 - α) = 1 := by
      rw [← Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn)]
      simp
    have hb' : (n : ℝ) ^ (α - 1) * reverseHeightErrorMax x n q.1 ≤ ε / 2 := by
      calc
        _ ≤ (n : ℝ) ^ (α - 1) * (ε / 2 * (n : ℝ) ^ (1 - α)) :=
          mul_le_mul_of_nonneg_left hb hs
        _ = (ε / 2) * ((n : ℝ) ^ (α - 1) * (n : ℝ) ^ (1 - α)) := by ring
        _ = ε / 2 := by rw [hprod, mul_one]
    have herr := rootedSampledMatrix_error_le x α n k q hq
    have hle : max (dist (sampledDistanceMatrix α n k q) (sampledStarMatrix x α n k q))
        ((n : ℝ) ^ (α - 1) * reverseHeightErrorMax x n q.1 + (n : ℝ) ^ (α - 1) / 2) ≤ ε :=
      max_le ha (by linarith)
    exact (not_lt.mpr (herr.trans hle)) he
  have hmono : μ.real {q | ε < dist (rootedSampledDistanceMatrix α n k q)
      (rootedSampledStarMatrix x α n k q)} ≤ μ.real (A ∪ B) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := μ) A B
  have hB : μ.real B = (jointLaw (companionSchedule (x n)) n).real
      {ω | ε / 2 * (n : ℝ) ^ (1 - α) < reverseHeightErrorMax x n ω} :=
    sampledReverseVectorLaw_history_event (x n) (hx n).1 (hx n).2
      {ω : History | ε / 2 * (n : ℝ) ^ (1 - α) < reverseHeightErrorMax x n ω}
  exact hmono.trans (hu.trans_eq (congrArg (fun z : ℝ ↦ μ.real A + z) hB))

end Freezing2
