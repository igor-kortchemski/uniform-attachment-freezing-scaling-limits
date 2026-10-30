module

public import Freezing2.Probability.CriticalSampleNet
public import Freezing2.Probability.CoalescenceMetricApproximation

/-!
# Leaf-tightness in the critical regime

The source's leaf-tightness display `eq:GH`, with the graph distance `dⁿ`:
for every `ε > 0`,

  lim_{k→∞} limsup_{n→∞} P(max_{v ∈ 𝕍ₙ} min_{1 ≤ i ≤ k} dⁿ(v, V_i) / √n > ε) = 0.

Step 2 of the source reduces this, via `height=ok`, to the same display
`16/01/11h` for the harmonic surrogate `Dⁿ`, and bounds `Dⁿ/√n` by a truncated
harmonic sum plus `Δⁿ/(nδ)`. Here the surrogate display is bypassed: the proved
uniform modulus (U32) shows that, outside N07's all-pairs error event, small
`Δⁿ/n` forces small `dⁿ/√n`. Combined with `eq:stepone` this gives `eq:GH`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- The all-pairs error only depends on the current row. -/
theorem reverseDistanceErrorMax_congr {x y : ℕ → ℕ → ℤ} {n : ℕ} (h : x n = y n)
    (ω : History) : reverseDistanceErrorMax x n ω = reverseDistanceErrorMax y n ω :=
  congrArg (fun row : ℕ → ℤ ↦ reverseDistanceErrorMax (fun _ ↦ row) n ω) h

/-- For fixed `ε, η > 0`, eventually in `k` and then in `n`, the graph-distance
sample-net failure probability is at most `η`. -/
theorem eventually_criticalGraphNet_probability_le {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    {M : ℝ} (hM : 1 ≤ M)
    (hpop : ∀ n : ℕ, 0 < n → ∀ i ≤ n, (activeCount (x n) i : ℝ) ≤ M * Real.sqrt n)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
        {q | ∃ v ∈ vertexLabels (x n) n, ∀ i,
          ε < reverseDistance n v (q.2 i) q.1 / Real.sqrt n} ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, htransfer⟩ := eventually_graph_cover_of_coalescence_cover
    (admissible_initialRowExtension hx) (by norm_num : (1 / 2 : ℝ) < 1)
    (hasL1ReciprocalProfile_initialRowExtension hL1) hε
  have herr := tendsto_reverseDistanceErrorMax_positive_horizons hx (by norm_num)
    (by norm_num) hf hL1 (half_pos hε)
  have herrEv : ∀ᶠ n : ℕ in atTop, (jointLaw (companionSchedule (x n)) n).real
      {ω | ε / 2 * (n : ℝ) ^ (1 - (1 / 2 : ℝ)) < reverseDistanceErrorMax x n ω} ≤ η / 2 :=
    herr.eventually (ge_mem_nhds (half_pos hη))
  filter_upwards [eventually_criticalSampleNet_probability_le hx hM hpop hδ (half_pos hη),
    eventually_ge_atTop 1] with k hk hk1
  filter_upwards [hk, herrEv, htransfer, initialRowExtension_eventually_eq x,
    eventually_ge_atTop 1] with n hnet hnerr hmod hext hn1
  obtain ⟨hxn, hsurv⟩ := hx n hn1
  have hs : 0 ≤ activeCount (x n) n := (hsurv n le_rfl).le
  have := uniformVertexVectorLaw_probability (x n) hxn (k := k) hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hc : (n : ℝ) ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt n)⁻¹ := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg (Nat.cast_nonneg _),
      Real.sqrt_eq_rpow]
  have hc' : (n : ℝ) ^ (1 - (1 / 2 : ℝ)) = Real.sqrt n := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  let Enet : Set (History × (Fin k → VertexLabel)) := {q | ∃ v ∈ vertexLabels (x n) n, ∀ i,
    δ < sourceCoalescenceDistance n v (q.2 i) q.1 / n}
  let Eerr : Set History :=
    {ω | ε / 2 * (n : ℝ) ^ (1 - (1 / 2 : ℝ)) < reverseDistanceErrorMax x n ω}
  let Eill : Set (History × (Fin k → VertexLabel)) := {q | ¬ ∀ i, q.2 i ∈ vertexLabels (x n) n}
  have hsub : {q : History × (Fin k → VertexLabel) | ∃ v ∈ vertexLabels (x n) n, ∀ i,
      ε < reverseDistance n v (q.2 i) q.1 / Real.sqrt n} ⊆ (Enet ∪ Eerr ×ˢ univ) ∪ Eill := by
    rintro q ⟨v₀, hv₀, hfar⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, not_or] at hcon
    obtain ⟨⟨hnotnet, hnoterr⟩, hnotill⟩ := hcon
    have hlegal : ∀ i, q.2 i ∈ vertexLabels (x n) n := by
      simpa only [Eill, Set.mem_ofPred_eq, not_not] using hnotill
    have herrq : (n : ℝ) ^ ((1 / 2 : ℝ) - 1) *
        reverseDistanceErrorMax (initialRowExtension x) n q.1 ≤ ε / 2 := by
      rw [reverseDistanceErrorMax_congr hext, hc, inv_mul_le_iff₀ hsqrt, mul_comm, ← hc']
      simpa only [Eerr, Set.mem_ofPred_eq, not_lt] using hnoterr
    have hcov : ∀ u ∈ vertexLabels (x n) n, ∃ i,
        sourceCoalescenceDistance n u (q.2 i) q.1 ≤ δ * n := by
      intro u hu
      simp only [Enet, Set.mem_ofPred_eq, not_exists, not_and, not_forall, not_lt] at hnotnet
      obtain ⟨i, hi⟩ := hnotnet u hu
      exact ⟨i, (div_le_iff₀ hnR).mp hi⟩
    let B : Finset VertexLabel := Finset.univ.image q.2
    have hB : B.Nonempty := ⟨q.2 ⟨0, hk1⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
    have hBsub : B ⊆ vertexLabels (initialRowExtension x n) n := by
      rw [hext]
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
      exact hlegal i
    have hBcov : ∀ u ∈ vertexLabels (initialRowExtension x n) n,
        sourceCoalescenceSetDistance n u B hB q.1 ≤ δ * n := by
      rw [hext]
      intro u hu
      obtain ⟨i, hi⟩ := hcov u hu
      exact (sourceCoalescenceSetDistance_le n u B hB q.1
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).trans hi
    obtain ⟨w, hw, hclose⟩ := hmod q.1 herrq B hB hBsub hBcov v₀ (hext ▸ hv₀)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    rw [hc, inv_mul_eq_div] at hclose
    exact (lt_asymm hclose) (hfar i)
  have hnet' : ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
      Enet ≤ ENNReal.ofReal (η / 2) := hnet
  have herr' : ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
      (Eerr ×ˢ univ) ≤ ENNReal.ofReal (η / 2) := by
    rw [Measure.prod_prod, measure_univ, mul_one, ← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hnerr
  have hill : ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
      Eill = 0 := by
    apply ae_iff.mp
    exact (measurePreserving_snd (μ := jointLaw (companionSchedule (x n)) n)
      ).quasiMeasurePreserving.ae (uniformVertexVectorLaw_ae_legal (x n) hxn hs)
  calc
    _ ≤ ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
          ((Enet ∪ Eerr ×ˢ univ) ∪ Eill) := measure_mono hsub
    _ ≤ ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
          Enet + ((jointLaw (companionSchedule (x n)) n).prod
            (uniformVertexVectorLaw (x n) n k)) (Eerr ×ˢ univ) +
          ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
            Eill :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) + 0 := by
      rw [hill]
      exact add_le_add (add_le_add hnet' herr') le_rfl
    _ = ENNReal.ofReal η := by
      rw [add_zero, ← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le, add_halves]

/-- Leaf-tightness `eq:GH` in the critical regime: for every `ε > 0`,
`lim_k limsup_n P(max_{v ∈ 𝕍ₙ} min_{i ≤ k} dⁿ(v, V_i)/√n > ε) = 0`, with the
actual reverse-tree graph distance and independent uniform vertices, under the
hypotheses of `thm:critique` used here: survival, `Lim^{1/2}_{1/f}` with `f > 0`
a.e., and `max_{1 ≤ k ≤ n} S^n_k = O(√n)`. -/
theorem critical_graphSampleNet_tightness {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
        {q | ∃ v ∈ vertexLabels (x n) n, ∀ i,
          ε < reverseDistance n v (q.2 i) q.1 / Real.sqrt n}) atTop) atTop (𝓝 0) := by
  obtain ⟨M, hM, hM'⟩ := exists_uniform_population_bound (fun n hn ↦ (hx n hn).1) hpop
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases htop : η = ⊤
  · exact Eventually.of_forall fun _ ↦ htop ▸ le_top
  have hδ : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  filter_upwards [eventually_criticalGraphNet_probability_le hx hf hL1 hM hM' hε hδ] with k hk
  rw [ENNReal.ofReal_toReal htop] at hk
  exact limsup_le_of_le (by isBoundedDefault) hk

end Freezing2
