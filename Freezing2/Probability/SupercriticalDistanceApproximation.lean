module

public import Freezing2.Probability.DistanceApproximation
public import Freezing2.Probability.SupercriticalCoalescenceLaw
public import Freezing2.Analysis.ProfilePrimitive
public import Freezing2.Discrete.HarmonicDistances
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The supercritical star approximation under the actual reverse-tree law

The harmonic comparison retains its inclusive endpoint. Its difference from
the two branch prefixes is controlled by the prefix at the coalescence phase
and one vanishing endpoint term. Sampling is independent of the tree and is
with replacement, so the coalescence estimate includes possible collisions.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- The two source branch prefixes, with their exact height normalization. -/
noncomputable def sampledBranchSum (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    (u v : VertexLabel) : ℝ :=
  normalizedHarmonicPrefix x α n (birthTime n u) +
    normalizedHarmonicPrefix x α n (birthTime n v)

theorem profilePrimitive_zero (g : ℝ → ℝ) : profilePrimitive g 0 = 0 := by
  simp [profilePrimitive]

theorem harmonic_coalescence_branch_difference (x : ℕ → ℤ) {c a b : ℕ}
    (hca : c ≤ a) (hcb : c ≤ b) :
    inclusiveHarmonic x c a / 2 + inclusiveHarmonic x c b / 2 -
      (harmonicInterval x 0 a / 2 + harmonicInterval x 0 b / 2) =
        (activeCount x c : ℝ)⁻¹ - harmonicInterval x 0 c := by
  rw [inclusiveHarmonic_eq x hca, inclusiveHarmonic_eq x hcb,
    ← harmonicInterval_prefix_difference x hca,
    ← harmonicInterval_prefix_difference x hcb]
  ring

/-- Every reciprocal population endpoint is at most one while the row survives. -/
theorem reciprocal_activeCount_abs_le_one {x : ℕ → ℤ} {n c : ℕ}
    (hs : SurvivesThrough x n) (hc : c ≤ n) : |(activeCount x c : ℝ)⁻¹| ≤ 1 := by
  have hp : (0 : ℝ) < activeCount x c := by exact_mod_cast hs c hc
  have h1 : (1 : ℝ) ≤ activeCount x c := by
    have hi : (1 : ℤ) ≤ activeCount x c := by have := hs c hc; omega
    exact_mod_cast hi
  rw [abs_of_nonneg (inv_nonneg.mpr hp.le)]
  exact (inv_le_one₀ hp).mpr h1

/-- Exact endpoint accounting gives a uniform deterministic comparison with
the continuous primitive at the coalescence phase. -/
theorem scaled_coalescenceHarmonicDistance_branch_error_le
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n : ℕ}
    (hn : 0 < n) {u : VertexLabel} (hu : u ∈ vertexLabels (x n) n)
    (v : VertexLabel) (ω : History) :
    |(n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω -
      sampledBranchSum x α n u v| ≤
        (n : ℝ) ^ (α - 1) + 2 * branchPrimitiveError x α g n +
          2 * |profilePrimitive g ((sourceCoalescenceTime n u v ω : ℝ) / n)| := by
  let c := sourceCoalescenceTime n u v ω
  have hc : c ≤ n := (sourceCoalescenceTime_le_birth_left n u v ω).trans
    (birthTime_le (x n) hu)
  have hp := normalizedHarmonicPrefix_error_le (α := α) hx hg hn hc
  have hi := reciprocal_activeCount_abs_le_one (hx n).2 hc
  have hs : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he : (n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω -
      sampledBranchSum x α n u v =
      (n : ℝ) ^ (α - 1) * (activeCount (x n) c : ℝ)⁻¹ -
        2 * normalizedHarmonicPrefix x α n c := by
    have h := harmonic_coalescence_branch_difference (x n)
      (sourceCoalescenceTime_le_birth_left n u v ω)
      (sourceCoalescenceTime_le_birth_right n u v ω)
    unfold coalescenceHarmonicDistance sampledBranchSum normalizedHarmonicPrefix
    dsimp [c]
    nlinarith [h]
  rw [he]
  have ha := abs_sub_le ((n : ℝ) ^ (α - 1) * (activeCount (x n) c : ℝ)⁻¹)
    0 (2 * normalizedHarmonicPrefix x α n c)
  have hb := abs_sub_le (normalizedHarmonicPrefix x α n c)
    (profilePrimitive g ((c : ℝ) / n)) 0
  simp only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
  simp only [sub_zero] at hb
  have hmul := mul_le_mul_of_nonneg_left hi hs
  simp only [mul_one] at hmul
  dsimp [c] at *
  linarith

theorem scaled_reverseDistance_branch_error_le
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n : ℕ}
    (hn : 0 < n) {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n)
    (hv : v ∈ vertexLabels (x n) n) (ω : History) :
    |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω - sampledBranchSum x α n u v| ≤
      (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω +
        (n : ℝ) ^ (α - 1) + 2 * branchPrimitiveError x α g n +
          2 * |profilePrimitive g ((sourceCoalescenceTime n u v ω : ℝ) / n)| := by
  have hs : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb := scaled_coalescenceHarmonicDistance_branch_error_le (α := α) hx hg hn hu v ω
  have hm := mul_le_mul_of_nonneg_left (distance_error_le_reverseDistanceErrorMax x n hu hv ω) hs
  have ht := abs_sub_le ((n : ℝ) ^ (α - 1) * reverseDistance n u v ω)
    ((n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω)
    (sampledBranchSum x α n u v)
  rw [← mul_sub, abs_mul, abs_of_nonneg hs] at ht
  linarith

/-- The actual sampled distance error from the two harmonic branch lengths. -/
def sampledBranchErrorEvent (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (ε : ℝ) :
    Set (History × (VertexLabel × VertexLabel)) :=
  {q | ε < |(n : ℝ) ^ (α - 1) * reverseDistance n q.2.1 q.2.2 q.1 -
    sampledBranchSum x α n q.2.1 q.2.2|}

theorem measurableSet_sampledBranchErrorEvent (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (ε : ℝ) :
    MeasurableSet (sampledBranchErrorEvent x α n ε) := by
  have hm : Measurable (fun q : History × (VertexLabel × VertexLabel) ↦
    |(n : ℝ) ^ (α - 1) * reverseDistance n q.2.1 q.2.2 q.1 -
      sampledBranchSum x α n q.2.1 q.2.2|) := by
    apply measurable_from_prod_countable_left
    intro p
    simpa only [Real.norm_eq_abs] using
      ((measurable_reverseDistance n p.1 p.2).const_mul _ |>.sub_const _).norm
  exact measurableSet_Ioi.preimage hm

theorem sampledReverseLaw_ae_legal (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) :
    ∀ᵐ q ∂sampledReverseLaw x n,
      q.2.1 ∈ vertexLabels x n ∧ q.2.2 ∈ vertexLabels x n := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hp : ∀ᵐ p ∂(uniformVertex x n).prod (uniformVertex x n),
      p.1 ∈ vertexLabels x n ∧ p.2 ∈ vertexLabels x n := by
    apply (Measure.ae_prod_iff_ae_ae (by exact (Set.to_countable _).measurableSet)).mpr
    filter_upwards [uniformVertex_mem x hx (hs n le_rfl).le] with u hu
    exact (uniformVertex_mem x hx (hs n le_rfl).le).mono fun v hv ↦ ⟨hu, hv⟩
  exact (Measure.ae_prod_iff_ae_ae
    ((show MeasurableSet {p : VertexLabel × VertexLabel |
      p.1 ∈ vertexLabels x n ∧ p.2 ∈ vertexLabels x n} from
      (Set.to_countable _).measurableSet).preimage measurable_snd)).mpr
    (Eventually.of_forall fun _ ↦ hp)

theorem sampledReverseLaw_history_event (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (E : Set History) :
    (sampledReverseLaw x n).real {q | q.1 ∈ E} =
      (jointLaw (companionSchedule x) n).real E := by
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have he : {q : History × (VertexLabel × VertexLabel) | q.1 ∈ E} = E ×ˢ univ := by
    ext q
    simp
  rw [he, sampledReverseLaw]
  simp [measureReal_prod_prod]

theorem tendsto_height_inverse_scale {α : ℝ} (hα : α < 1) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
  simpa only [neg_sub, Function.comp_def] using
    (tendsto_rpow_neg_atTop (show 0 < 1 - α by linarith)).comp
      tendsto_natCast_atTop_atTop

/-- The deterministic good-event implication is separated from measure
elaboration, preserving all inclusive endpoint and normalization terms. -/
theorem scaled_branch_error_lt_of_good
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n : ℕ} (hn : 0 < n)
    {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n)
    (ω : History) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hcont : ∀ t : ℝ, |t| < δ → |profilePrimitive g t| < ε / 8)
    (hsmall : (n : ℝ) ^ (α - 1) + 2 * branchPrimitiveError x α g n < ε / 4)
    (hmax : reverseDistanceErrorMax x n ω ≤ ε / 4 * (n : ℝ) ^ (1 - α))
    (hcoal : |(sourceCoalescenceTime n u v ω : ℝ) / n| ≤ δ / 2) :
    |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω - sampledBranchSum x α n u v| < ε := by
  have hp := hcont _ (lt_of_le_of_lt hcoal (by linarith only [hδ]))
  have hs : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hprod : (n : ℝ) ^ (α - 1) * (n : ℝ) ^ (1 - α) = 1 := by
    rw [← Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn)]
    simp
  have hm : (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω ≤ ε / 4 := by
    calc
      _ ≤ (n : ℝ) ^ (α - 1) * (ε / 4 * (n : ℝ) ^ (1 - α)) :=
        mul_le_mul_of_nonneg_left hmax hs
      _ = (ε / 4) * ((n : ℝ) ^ (α - 1) * (n : ℝ) ^ (1 - α)) := by ring
      _ = ε / 4 := by rw [hprod, mul_one]
  have herr := scaled_reverseDistance_branch_error_le (α := α) hx hg hn hu hv ω
  linarith only [herr, hm, hsmall, hp, hε]

/-- A finite union bound separating the genuine N07 distance deviation from
the event that the coalescence phase is outside a small initial interval. -/
theorem sampledBranchError_probability_le
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hcont : ∀ t : ℝ, |t| < δ → |profilePrimitive g t| < ε / 8)
    (hsmallN : (n : ℝ) ^ (α - 1) + 2 * branchPrimitiveError x α g n < ε / 4) :
    (sampledReverseLaw (x n) n).real (sampledBranchErrorEvent x α n ε) ≤
      (jointLaw (companionSchedule (x n)) n).real
        {ω | ε / 4 * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω} +
      (sampledReverseLaw (x n) n).real
        {q | δ / 2 < |(sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n|} := by
  let μ := sampledReverseLaw (x n) n
  let := sampledReverseLaw_probability (x n) (hx n).1 (hx n).2
  let A : Set (History × (VertexLabel × VertexLabel)) :=
    {q | ε / 4 * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n q.1}
  let B : Set (History × (VertexLabel × VertexLabel)) :=
    {q | δ / 2 < |(sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n|}
  have hsub : sampledBranchErrorEvent x α n ε ≤ᵐ[μ] A ∪ B := by
    filter_upwards [sampledReverseLaw_ae_legal (x n) (hx n).1 (hx n).2] with q hq
    intro he
    by_contra hbad
    have ha : reverseDistanceErrorMax x n q.1 ≤ ε / 4 * (n : ℝ) ^ (1 - α) :=
      le_of_not_gt fun h ↦ hbad (Or.inl h)
    have hb : |(sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n| ≤ δ / 2 :=
      le_of_not_gt fun h ↦ hbad (Or.inr h)
    have herr := scaled_branch_error_lt_of_good hx hg hn hq.1 hq.2 q.1
      hε hδ hcont hsmallN ha hb
    exact (not_lt.mpr herr.le) he
  have hm : μ.real (sampledBranchErrorEvent x α n ε) ≤ μ.real (A ∪ B) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := μ) A B
  -- Give the event explicitly: inferring it from a probability value unfolds
  -- the concrete trajectory measure instead of solving a syntactic goal.
  have hA : μ.real A = (jointLaw (companionSchedule (x n)) n).real
      {ω | ε / 4 * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω} :=
    sampledReverseLaw_history_event (x n) (hx n).1 (hx n).2
      {ω : History | ε / 4 * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω}
  exact hm.trans (hu.trans_eq (congrArg (fun z : ℝ ↦ z + μ.real B) hA))


/-- N07 and N10 imply the source's off-diagonal star approximation for two
actual independent uniform samples. Repeated labels are retained by the law. -/
theorem tendsto_sampledBranchError_probability
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x α g) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real
      (sampledBranchErrorEvent x α n ε)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    ((continuous_profilePrimitive hL1.1).continuousAt (x := 0)) (ε / 8) (by positivity)
  have hcont' {t : ℝ} (ht : |t| < δ) : |profilePrimitive g t| < ε / 8 := by
    have hh := hcont (show dist t 0 < δ by simpa only [Real.dist_eq, sub_zero] using ht)
    simpa only [Real.dist_eq, profilePrimitive_zero, sub_zero] using hh
  have hsmall : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α - 1) +
      2 * branchPrimitiveError x α g n) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_height_inverse_scale hα1).add ((tendsto_branchPrimitiveError hα1 hL1).const_mul 2)
  have hmax := tendsto_reverseDistanceErrorMax hx (show 0 < α by linarith) hα1 hL1 hpos
    (show 0 < ε / 4 by positivity)
  have hcoal := tendsto_normalized_sampledCoalescence_probability hx hαhalf hα1 hL1 hpos h2
    (show 0 < δ / 2 by positivity)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _
    (show Tendsto (fun n ↦
      (jointLaw (companionSchedule (x n)) n).real
        {ω | ε / 4 * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω} +
      (sampledReverseLaw (x n) n).real
        {q | δ / 2 < |(sourceCoalescenceTime n q.2.1 q.2.2 q.1 : ℝ) / n|})
        atTop (𝓝 0) from by simpa using hmax.add hcoal)
  filter_upwards [eventually_gt_atTop 0,
    hsmall.eventually_lt_const (show 0 < ε / 4 by positivity)] with n hn hsmallN
  exact sampledBranchError_probability_le hx hL1.1 hn hε hδ
    (fun _ ht ↦ hcont' ht) hsmallN

/-- Source-profile specialization with admissibility only on positive rows. -/
theorem tendsto_sampledBranchError_probability_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (sampledReverseLaw (x n) n).real
      (sampledBranchErrorEvent x α n ε)) atTop (𝓝 0) := by
  apply (tendsto_sampledBranchError_probability (admissible_initialRowExtension hx)
    hαhalf hα1 (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) (hasLocalSquareMomentProfile_initialRowExtension h2) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  simp only [sampledBranchErrorEvent, sampledBranchSum, normalizedHarmonicPrefix, hn]

end Freezing2
