module

public import Freezing2.Probability.CriticalChaining

/-!
# Sample-net tightness in the critical regime

The source's display `eq:stepone` (inventory U31): for every `ε > 0`,

  lim_{k→∞} limsup_{n→∞} P(max_{v ∈ 𝕍ₙ} Δⁿ(v, {V₁, …, V_k}) / n > ε) = 0.

The proof follows the paper's dyadic chaining: the blocks `(2^j, 2^{j+1}]`
use N13 with a fresh query vertex, the last net of size `2^{Nₙ}` with
`8^{Nₙ} ≤ n` uses N13 for each fixed vertex and a union bound over the
at most `n + 1` vertices, and the geometric tail is summed with one constant.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical ENNReal

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- Dyadic chaining for a function with zero diagonal satisfying the triangle
inequality on a set containing the samples and the covered points. -/
theorem dyadic_cover_chaining_of_triangle {β : Type*} (d : β → β → ℝ) {S : Set β}
    (hself : ∀ a, d a a = 0)
    (htri : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, d a c ≤ d a b + d b c)
    (v : ℕ → β) (hv : ∀ i, v i ∈ S) (ε : ℕ → ℝ) (k m : ℕ)
    (hε : ∀ j < m, 0 ≤ ε (k + j))
    (hstep : ∀ j < m, ∀ i, 2 ^ (k + j) ≤ i → i < 2 ^ (k + j + 1) →
      ∃ l < 2 ^ (k + j), d (v i) (v l) ≤ ε (k + j)) {r : ℝ}
    (hcover : ∀ y ∈ S, ∃ i < 2 ^ (k + m), d y (v i) ≤ r) :
    ∀ y ∈ S, ∃ l < 2 ^ k, d y (v l) ≤ (∑ j ∈ Finset.range m, ε (k + j)) + r := by
  have hchain : ∀ m' ≤ m, ∀ i < 2 ^ (k + m'), ∃ l < 2 ^ k,
      d (v i) (v l) ≤ ∑ j ∈ Finset.range m', ε (k + j) := by
    intro m'
    induction m' with
    | zero =>
      intro _ i hi
      exact ⟨i, by simpa using hi, by simp [hself]⟩
    | succ m' ih =>
      intro hm' i hi
      have hprev : ∃ l < 2 ^ (k + m'), d (v i) (v l) ≤ ε (k + m') := by
        by_cases hold : i < 2 ^ (k + m')
        · exact ⟨i, hold, by rw [hself]; exact hε m' (by omega)⟩
        · exact hstep m' (by omega) i (Nat.le_of_not_gt hold)
            (by simpa only [Nat.add_assoc] using hi)
      obtain ⟨l, hl, hil⟩ := hprev
      obtain ⟨a, ha, hla⟩ := ih (by omega) l hl
      refine ⟨a, ha, ?_⟩
      rw [Finset.sum_range_succ]
      exact (htri _ (hv i) _ (hv l) _ (hv a)).trans (by linarith)
  intro y hy
  obtain ⟨i, hi, hyi⟩ := hcover y hy
  obtain ⟨l, hl, hil⟩ := hchain m le_rfl i hi
  exact ⟨l, hl, (htri _ hy _ (hv i) _ (hv l)).trans (by linarith)⟩

/-- A new dyadic block `[2^j, 2^{j+1})` contains a sample far from the prefix. -/
def criticalBlockBad (n j : ℕ) (r : ℝ) : Set (History × (ℕ → VertexLabel)) :=
  {q | ∃ i ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), ∀ l < 2 ^ j,
    r < sourceCoalescenceDistance n (q.2 i) (q.2 l) q.1}

/-- Some actual vertex is far from the first `m` samples. -/
def criticalNetBad (x : ℕ → ℤ) (n m : ℕ) (r : ℝ) : Set (History × (ℕ → VertexLabel)) :=
  {q | ∃ u ∈ vertexLabels x n, ∀ l < m, r < sourceCoalescenceDistance n u (q.2 l) q.1}

/-- The deterministic chaining step of `eq:stepone`, for one row: outside the
block failures and the last-net failure, every vertex is within the summed
radii of the first `2^J` samples. -/
theorem criticalNetBad_le_blocks (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x))
    {J N : ℕ} (hJN : J ≤ N) (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) {R : ℝ}
    (hsum : (∑ j ∈ Finset.range (N - J + 1), r (J + j)) ≤ R) :
    (criticalSequenceLaw x n).real (criticalNetBad x n (2 ^ J) R) ≤
      (∑ j ∈ Finset.Ico J N, (criticalSequenceLaw x n).real (criticalBlockBad n j (r j))) +
        (criticalSequenceLaw x n).real (criticalNetBad x n (2 ^ N) (r N)) := by
  have hs : 0 ≤ activeCount x n := by
    simpa only [companion_activeCount x hx] using
      Freezing1.activeCount_nonneg_of_le_extinctionTime hn
  have := criticalSequenceLaw_probability x hx hs
  let G : Set (History × (ℕ → VertexLabel)) := {q | (∀ i, q.2 i ∈ vertexLabels x n) ∧
    ∀ u ∈ vertexLabels x n, ∀ v ∈ vertexLabels x n, ∀ w ∈ vertexLabels x n,
      sourceCoalescenceDistance n u w q.1 ≤
        sourceCoalescenceDistance n u v q.1 + sourceCoalescenceDistance n v w q.1}
  have hG : criticalSequenceLaw x n Gᶜ = 0 := by
    rw [Set.compl_ofPred]
    exact ae_iff.mp ((criticalSequenceLaw_ae_legal x hx hs).and
      (criticalSequenceLaw_ae_triangle x hx hn hs))
  have hsub : criticalNetBad x n (2 ^ J) R ⊆
      ((⋃ j ∈ Finset.Ico J N, criticalBlockBad n j (r j)) ∪
        criticalNetBad x n (2 ^ N) (r N)) ∪ Gᶜ := by
    intro q hq
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_not,
      exists_prop, not_exists, not_and] at hcon
    obtain ⟨⟨hblocks, hnet⟩, hlegal, htri⟩ := hcon
    obtain ⟨u, hu, hfar⟩ := hq
    have hstep : ∀ j < N - J, ∀ i, 2 ^ (J + j) ≤ i → i < 2 ^ (J + j + 1) →
        ∃ l < 2 ^ (J + j), sourceCoalescenceDistance n (q.2 i) (q.2 l) q.1 ≤ r (J + j) := by
      intro j hj i hi1 hi2
      have hnot := hblocks (J + j) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      simp only [criticalBlockBad, Set.mem_ofPred_eq, not_exists, not_and, not_forall,
        not_lt] at hnot
      obtain ⟨l, hl, hle⟩ := hnot i (Finset.mem_Ico.mpr ⟨hi1, by rw [pow_succ] at hi2; omega⟩)
      exact ⟨l, hl, hle⟩
    have hcover : ∀ y ∈ (vertexLabels x n : Set VertexLabel), ∃ i < 2 ^ (J + (N - J)),
        sourceCoalescenceDistance n y (q.2 i) q.1 ≤ r N := by
      intro y hy
      simp only [criticalNetBad, Set.mem_ofPred_eq, not_exists, not_and, not_forall,
        not_lt] at hnet
      obtain ⟨l, hl, hle⟩ := hnet y hy
      exact ⟨l, by rwa [Nat.add_sub_cancel' hJN], hle⟩
    obtain ⟨l, hl, hle⟩ := dyadic_cover_chaining_of_triangle
      (fun a b ↦ sourceCoalescenceDistance n a b q.1)
      (fun a ↦ sourceCoalescenceDistance_self n a q.1)
      (fun a ha b hb c hc ↦ htri a ha b hb c hc) q.2 hlegal r J (N - J)
      (fun j _ ↦ hr _) hstep hcover u hu
    have hsplit : (∑ j ∈ Finset.range (N - J), r (J + j)) + r N =
        ∑ j ∈ Finset.range (N - J + 1), r (J + j) := by
      rw [Finset.sum_range_succ, Nat.add_sub_cancel' hJN]
    exact (not_lt.mpr (hle.trans (hsplit.le.trans hsum))) (hfar l hl)
  calc
    _ ≤ (criticalSequenceLaw x n).real (((⋃ j ∈ Finset.Ico J N, criticalBlockBad n j (r j)) ∪
          criticalNetBad x n (2 ^ N) (r N)) ∪ Gᶜ) := measureReal_mono hsub
    _ ≤ (criticalSequenceLaw x n).real ((⋃ j ∈ Finset.Ico J N, criticalBlockBad n j (r j)) ∪
          criticalNetBad x n (2 ^ N) (r N)) + (criticalSequenceLaw x n).real Gᶜ :=
      measureReal_union_le _ _
    _ = (criticalSequenceLaw x n).real ((⋃ j ∈ Finset.Ico J N, criticalBlockBad n j (r j)) ∪
          criticalNetBad x n (2 ^ N) (r N)) := by
      rw [show (criticalSequenceLaw x n).real Gᶜ = 0 by
        rw [measureReal_def, hG, ENNReal.toReal_zero], add_zero]
    _ ≤ (criticalSequenceLaw x n).real (⋃ j ∈ Finset.Ico J N, criticalBlockBad n j (r j)) +
          (criticalSequenceLaw x n).real (criticalNetBad x n (2 ^ N) (r N)) :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add (measureReal_biUnion_finset_le _ _) le_rfl

/-- The source radius at a dyadic sample size is below `j² 2^{-j/2} n`. -/
theorem dyadic_log_radius_le (j n : ℕ) :
    (n : ℝ) * Real.log ((2 ^ j : ℕ) : ℝ) ^ 2 / Real.sqrt ((2 ^ j : ℕ) : ℝ) ≤
      (j : ℝ) ^ 2 * (2 : ℝ) ^ (-(j : ℝ) / 2) * n := by
  have hlog : Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  have hsqrt : Real.sqrt ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ ((j : ℝ) / 2) := by
    push_cast
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hneg : (2 : ℝ) ^ (-(j : ℝ) / 2) = ((2 : ℝ) ^ ((j : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg (by norm_num)]
  have hl2 : Real.log 2 ^ 2 ≤ 1 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have h0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hpos : 0 < (2 : ℝ) ^ ((j : ℝ) / 2) := by positivity
  rw [hlog, hsqrt, hneg, div_le_iff₀ hpos]
  have he : (j : ℝ) ^ 2 * ((2 : ℝ) ^ ((j : ℝ) / 2))⁻¹ * n * (2 : ℝ) ^ ((j : ℝ) / 2) =
      (j : ℝ) ^ 2 * n := by
    field_simp
  rw [he]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hj2 : (0 : ℝ) ≤ (j : ℝ) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hl2 (mul_nonneg hn0 hj2)]

theorem vertexLabels_card_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : 0 ≤ activeCount x n) : (vertexLabels x n).card ≤ n + 1 := by
  rw [vertexLabels_card x hx hs]
  have h : (upSteps x 0 n).card ≤ (Finset.Ioc 0 n).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simp only [Nat.card_Ioc, Nat.sub_zero] at h
  omega

theorem tendsto_rpow_neg_div_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ (-(j : ℝ) / a)) atTop (𝓝 0) := by
  have he (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) / a) = ((2 : ℝ) ^ (-1 / a)) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp only [he]
  apply tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) _)
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    have : (0 : ℝ) < 1 / a := by positivity
    rw [neg_div]
    linarith)

/-- Quantitative form of `eq:stepone` for one row: the sample-net failure
probability is at most the geometric block error plus the last-net error. -/
theorem criticalSampleNet_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x))
    {K₁ K₂ : ℕ}
    (hK₁ : ∀ k ≥ K₁, k ^ 3 ≤ n →
      (sampledCriticalCoverLaw x n k).real
        (sampledCriticalCoverEvent n k ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k)) ≤
          1 / (k : ℝ) ^ 4)
    (hK₂ : ∀ k ≥ K₂, k ^ 3 ≤ n → ∀ u ∈ vertexLabels x n,
      ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n k)).real
        (fixedCriticalCoverEvent n k u ((n : ℝ) * Real.log k ^ 2 / Real.sqrt k)) ≤
          1 / (k : ℝ) ^ 4)
    {J N : ℕ} (hJN : J ≤ N) (hN : 8 ^ N ≤ n) (hJ₁ : K₁ ≤ 2 ^ J) (hJ₂ : K₂ ≤ 2 ^ J)
    {R : ℝ} (hsum : (∑ j ∈ Finset.range (N - J + 1),
      ((J + j : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-((J + j : ℕ) : ℝ) / 2) * n) ≤ R) :
    (criticalSequenceLaw x n).real (criticalNetBad x n (2 ^ J) R) ≤
      (∑ j ∈ Finset.Ico J N, ((1 : ℝ) / 8) ^ j) + (n + 1) / ((2 : ℝ) ^ N) ^ 4 := by
  have hs : 0 ≤ activeCount x n := by
    simpa only [companion_activeCount x hx] using
      Freezing1.activeCount_nonneg_of_le_extinctionTime hn
  have := criticalSequenceLaw_probability x hx hs
  let r : ℕ → ℝ := fun j ↦ (j : ℝ) ^ 2 * (2 : ℝ) ^ (-(j : ℝ) / 2) * n
  have hr : ∀ j, 0 ≤ r j := fun j ↦ by positivity
  refine (criticalNetBad_le_blocks x hx hn hJN r hr hsum).trans (add_le_add ?_ ?_)
  · apply Finset.sum_le_sum
    intro j hj
    obtain ⟨hJj, hjN⟩ := Finset.mem_Ico.mp hj
    have hk : K₁ ≤ 2 ^ j := hJ₁.trans (Nat.pow_le_pow_right (by norm_num) hJj)
    have hkn : (2 ^ j) ^ 3 ≤ n := by
      calc
        (2 ^ j) ^ 3 = 8 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 8 ^ N := Nat.pow_le_pow_right (by norm_num) hjN.le
        _ ≤ n := hN
    have := sampledCriticalCoverLaw_probability x hx (k := 2 ^ j) hs
    have hmono : sampledCriticalCoverEvent n (2 ^ j) (r j) ⊆
        sampledCriticalCoverEvent n (2 ^ j)
          ((n : ℝ) * Real.log ((2 ^ j : ℕ) : ℝ) ^ 2 / Real.sqrt ((2 ^ j : ℕ) : ℝ)) :=
      fun q hq i ↦ (dyadic_log_radius_le j n).trans_lt (hq i)
    have hcover := (measureReal_mono hmono).trans (hK₁ (2 ^ j) hk hkn)
    have hblock := criticalSequenceLaw_block_le x hx hs (2 ^ j) (r j)
    calc
      _ ≤ ((2 ^ j : ℕ) : ℝ) * (sampledCriticalCoverLaw x n (2 ^ j)).real
            (sampledCriticalCoverEvent n (2 ^ j) (r j)) := hblock
      _ ≤ ((2 ^ j : ℕ) : ℝ) * (1 / ((2 ^ j : ℕ) : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hcover (Nat.cast_nonneg _)
      _ = ((1 : ℝ) / 8) ^ j := by
        push_cast
        have h2 : (0 : ℝ) < 2 ^ j := by positivity
        rw [show ((1 : ℝ) / 8) ^ j = 1 / ((2 : ℝ) ^ j) ^ 3 by
          rw [← pow_mul, mul_comm, pow_mul, one_div, one_div, inv_pow]; norm_num]
        field_simp
  · have hk : K₂ ≤ 2 ^ N := hJ₂.trans (Nat.pow_le_pow_right (by norm_num) hJN)
    have hkn : (2 ^ N) ^ 3 ≤ n := by
      calc
        (2 ^ N) ^ 3 = 8 ^ N := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ n := hN
    have hc : ∀ u ∈ vertexLabels x n,
        ((jointLaw (companionSchedule x) n).prod (uniformVertexVectorLaw x n (2 ^ N))).real
          (fixedCriticalCoverEvent n (2 ^ N) u (r N)) ≤ 1 / ((2 ^ N : ℕ) : ℝ) ^ 4 := by
      intro u hu
      have := uniformVertexVectorLaw_probability x hx (k := 2 ^ N) hs
      have hmono : fixedCriticalCoverEvent n (2 ^ N) u (r N) ⊆
          fixedCriticalCoverEvent n (2 ^ N) u
            ((n : ℝ) * Real.log ((2 ^ N : ℕ) : ℝ) ^ 2 / Real.sqrt ((2 ^ N : ℕ) : ℝ)) :=
        fun q hq i ↦ (dyadic_log_radius_le N n).trans_lt (hq i)
      exact (measureReal_mono hmono).trans (hK₂ (2 ^ N) hk hkn u hu)
    have hnet := criticalSequenceLaw_lastNet_le x hx hs (2 ^ N) (r N) _ hc
    have hcard : ((vertexLabels x n).card : ℝ) ≤ n + 1 := by
      exact_mod_cast vertexLabels_card_le x hx hs
    calc
      _ ≤ ((vertexLabels x n).card : ℝ) * (1 / ((2 ^ N : ℕ) : ℝ) ^ 4) := hnet
      _ ≤ (n + 1) * (1 / ((2 ^ N : ℕ) : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by push_cast; ring

/-- The last-net error tends to zero along `Nₙ = log₈ n`. -/
theorem tendsto_lastNetError :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / ((2 : ℝ) ^ Nat.log 8 n) ^ 4) atTop (𝓝 0) := by
  have hb (n : ℕ) : ((n : ℝ) + 1) / ((2 : ℝ) ^ Nat.log 8 n) ^ 4 ≤
      8 * ((1 : ℝ) / 2) ^ Nat.log 8 n := by
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 8) n
    have hle : ((n : ℝ) + 1) ≤ (8 : ℝ) ^ (Nat.log 8 n + 1) := by exact_mod_cast hlt
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ Nat.log 8 n) ^ 4 := by positivity
    rw [div_le_iff₀ hpos]
    calc
      ((n : ℝ) + 1) ≤ (8 : ℝ) ^ (Nat.log 8 n + 1) := hle
      _ = 8 * ((1 : ℝ) / 2) ^ Nat.log 8 n * ((2 : ℝ) ^ Nat.log 8 n) ^ 4 := by
        rw [← pow_mul, pow_succ, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, div_pow,
          one_pow]
        field_simp
        ring
  have hlog : Tendsto (fun n : ℕ ↦ Nat.log 8 n) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro L
    exact ⟨8 ^ L, fun n hn ↦ Nat.le_log_of_pow_le (by norm_num) hn⟩
  have hg : Tendsto (fun n : ℕ ↦ 8 * ((1 : ℝ) / 2) ^ Nat.log 8 n) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num : (1 : ℝ) / 2 < 1)).comp hlog).const_mul 8
  exact squeeze_zero (fun n ↦ by positivity) hb hg

/-- For fixed `ε, δ > 0`, eventually in `k` and then eventually in `n`, the
sample-net failure probability for the first `k` samples is at most `δ`. -/
theorem eventually_criticalSampleNet_probability_le {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    {M : ℝ} (hM : 1 ≤ M)
    (hpop : ∀ n : ℕ, 0 < n → ∀ i ≤ n, (activeCount (x n) i : ℝ) ≤ M * Real.sqrt n)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ᶠ n in atTop,
      ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
        {q | ∃ v ∈ vertexLabels (x n) n, ∀ i,
          ε < sourceCoalescenceDistance n v (q.2 i) q.1 / n} ≤ ENNReal.ofReal δ := by
  obtain ⟨K₁, -, hK₁⟩ := eventually_uniform_sampledCriticalCover_probability_le hM
  obtain ⟨K₂, -, hK₂⟩ := eventually_uniform_fixedCriticalCover_probability_le hM
  obtain ⟨C, hC, hCbound⟩ := exists_dyadic_chaining_tail_bound
  have hJev : ∀ᶠ J : ℕ in atTop, K₁ ≤ 2 ^ J ∧ K₂ ≤ 2 ^ J ∧
      C * (2 : ℝ) ^ (-(J : ℝ) / 3) ≤ ε ∧ ∑' i : ℕ, ((1 : ℝ) / 8) ^ (J + i) ≤ δ / 2 := by
    have h1 : ∀ᶠ J : ℕ in atTop, K₁ ≤ 2 ^ J :=
      eventually_atTop.mpr ⟨K₁, fun J hJ ↦ hJ.trans Nat.lt_two_pow_self.le⟩
    have h2 : ∀ᶠ J : ℕ in atTop, K₂ ≤ 2 ^ J :=
      eventually_atTop.mpr ⟨K₂, fun J hJ ↦ hJ.trans Nat.lt_two_pow_self.le⟩
    have h3 : ∀ᶠ J : ℕ in atTop, C * (2 : ℝ) ^ (-(J : ℝ) / 3) ≤ ε := by
      have := ((tendsto_rpow_neg_div_atTop (by norm_num : (0 : ℝ) < 3)).const_mul C)
      rw [mul_zero] at this
      exact (this.eventually (ge_mem_nhds hε)).mono fun _ h ↦ h
    have h4 : ∀ᶠ J : ℕ in atTop, ∑' i : ℕ, ((1 : ℝ) / 8) ^ (J + i) ≤ δ / 2 := by
      have he (J : ℕ) : ∑' i : ℕ, ((1 : ℝ) / 8) ^ (J + i) = ((1 : ℝ) / 8) ^ J * (8 / 7) := by
        simp only [pow_add]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
      have ht : Tendsto (fun J : ℕ ↦ ((1 : ℝ) / 8) ^ J * (8 / 7)) atTop (𝓝 0) := by
        simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
          (by norm_num : (1 : ℝ) / 8 < 1)).mul_const (8 / 7 : ℝ)
      simp only [he]
      exact ht.eventually (ge_mem_nhds (by linarith))
    exact h1.and (h2.and (h3.and h4))
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp hJev
  have hNev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) / ((2 : ℝ) ^ Nat.log 8 n) ^ 4 ≤ δ / 2 :=
    tendsto_lastNetError.eventually (ge_mem_nhds (by linarith))
  filter_upwards [eventually_ge_atTop (2 ^ J₀)] with k hk
  have hk0 : k ≠ 0 := (Nat.pos_of_ne_zero (by positivity)).trans_le hk |>.ne'
  let J := Nat.log 2 k
  have hJJ₀ : J₀ ≤ J := Nat.le_log_of_pow_le (by norm_num) hk
  have hJk : 2 ^ J ≤ k := Nat.pow_log_le_self 2 hk0
  obtain ⟨hJ₁, hJ₂, hJε, hJδ⟩ := hJ₀ J hJJ₀
  filter_upwards [hNev, eventually_ge_atTop (8 ^ J), eventually_ge_atTop 1] with n hnδ hnJ hn1
  have hn0 : 0 < n := hn1
  obtain ⟨hxn, hsurv⟩ := hx n hn0
  have hext := (companion_before_extinction (x n) hxn hsurv).le
  have hs : 0 ≤ activeCount (x n) n := (hsurv n le_rfl).le
  have := criticalSequenceLaw_probability (x n) hxn hs
  let N := Nat.log 8 n
  have hN : 8 ^ N ≤ n := Nat.pow_log_le_self 8 (by omega)
  have hJN : J ≤ N := Nat.le_log_of_pow_le (by norm_num) hnJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsum : (∑ j ∈ Finset.range (N - J + 1),
      ((J + j : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-((J + j : ℕ) : ℝ) / 2) * n) ≤ ε * n := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right ((hCbound J (N - J + 1)).trans hJε) hnR.le
  have hbound := criticalSampleNet_probability_le (x n) hxn hext
    (fun k hk hkn ↦ hK₁ k hk n hkn (x n) hxn hext (hpop n hn0))
    (fun k hk hkn u hu ↦ hK₂ k hk n hkn (x n) hxn hext (hpop n hn0) u hu)
    hJN hN hJ₁ hJ₂ hsum
  have hgeom : (∑ j ∈ Finset.Ico J N, ((1 : ℝ) / 8) ^ j) ≤ δ / 2 := by
    refine le_trans ?_ hJδ
    rw [Finset.sum_Ico_eq_sum_range]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 : ℝ) / 8 < 1)).comp_injective
      (add_right_injective J) |>.sum_le_tsum _ (fun i _ ↦ by positivity)
  have hreal : (criticalSequenceLaw (x n) n).real (criticalNetBad (x n) n (2 ^ J) (ε * n)) ≤ δ :=
    hbound.trans (by linarith)
  have hE : MeasurableSet {q : History × (Fin k → VertexLabel) | ∃ v ∈ vertexLabels (x n) n,
      ∀ i, ε < sourceCoalescenceDistance n v (q.2 i) q.1 / n} := by
    apply (measurable_from_prod_countable_left fun w ↦ ?_).setOf
    exact Measurable.exists fun v ↦ measurable_const.and (Measurable.forall fun i ↦
      measurable_const.lt ((measurable_sourceCoalescenceDistance n v (w i)).div_const _))
  rw [criticalSequenceLaw_prefix_event (x n) hxn hs k hE]
  calc
    _ ≤ criticalSequenceLaw (x n) n (criticalNetBad (x n) n (2 ^ J) (ε * n)) := by
      apply measure_mono
      rintro q ⟨v, hv, hfar⟩
      refine ⟨v, hv, fun l hl ↦ ?_⟩
      have h := hfar ⟨l, hl.trans_le hJk⟩
      exact (lt_div_iff₀ hnR).mp h
    _ = ENNReal.ofReal ((criticalSequenceLaw (x n) n).real
          (criticalNetBad (x n) n (2 ^ J) (ε * n))) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal

/-- The source display `eq:stepone` in the critical regime: for every `ε > 0`,
`lim_k limsup_n P(max_{v ∈ 𝕍ₙ} Δⁿ(v, {V₁, …, V_k}) / n > ε) = 0`, for the actual
reverse tree and independent uniform vertices, under survival and the source
population hypothesis `max_{1 ≤ k ≤ n} S^n_k = O(√n)`. -/
theorem critical_sampleNet_tightness {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.sqrt n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      ((jointLaw (companionSchedule (x n)) n).prod (uniformVertexVectorLaw (x n) n k))
        {q | ∃ v ∈ vertexLabels (x n) n, ∀ i,
          ε < sourceCoalescenceDistance n v (q.2 i) q.1 / n}) atTop) atTop (𝓝 0) := by
  obtain ⟨M, hM, hM'⟩ := exists_uniform_population_bound (fun n hn ↦ (hx n hn).1) hpop
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases htop : η = ⊤
  · exact Eventually.of_forall fun _ ↦ htop ▸ le_top
  have hδ : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  filter_upwards [eventually_criticalSampleNet_probability_le hx hM hM' hε hδ] with k hk
  rw [ENNReal.ofReal_toReal htop] at hk
  exact limsup_le_of_le (by isBoundedDefault) hk

end Freezing2
