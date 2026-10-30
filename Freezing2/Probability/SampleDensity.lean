module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Density of iid samples from a fully supported law

On a compact metric space whose probability measure charges every nonempty
open set, an iid sequence is almost surely dense. Quantitatively, the
Hausdorff distance from the first `k + 1` samples to the whole space tends to
zero almost surely. Each ball of a finite cover is hit with probability one,
because missing it `n` times has probability `(1 - μ B)^n`.
-/

@[expose] public section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace Freezing2

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]

omit [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] in
/-- A set of positive mass is almost surely hit by an iid sequence. -/
theorem ae_exists_mem_of_measure_pos (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Set Ω}
    (hB : MeasurableSet B) (hpos : 0 < μ B) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ), ∃ i, ω i ∈ B := by
  rw [ae_iff]
  have hlt : μ Bᶜ < 1 := by
    rw [prob_compl_eq_one_sub hB]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'
  have hle (n : ℕ) : Measure.infinitePi (fun _ : ℕ ↦ μ) {ω | ¬ ∃ i, ω i ∈ B} ≤ μ Bᶜ ^ n := by
    calc
      _ ≤ Measure.infinitePi (fun _ : ℕ ↦ μ)
            (Set.pi (Finset.range n : Set ℕ) (fun _ ↦ Bᶜ)) :=
        measure_mono fun ω hω ↦ by
          simp only [mem_ofPred_eq, not_exists] at hω
          exact fun i _ ↦ hω i
      _ = ∏ _i ∈ Finset.range n, μ Bᶜ :=
        Measure.infinitePi_pi (fun _ : ℕ ↦ μ) fun _ _ ↦ hB.compl
      _ = μ Bᶜ ^ n := by rw [Finset.prod_const, Finset.card_range]
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hle)
    bot_le

/-- For a fully supported law, the first `k + 1` iid samples are almost surely
Hausdorff-close to the whole space for large `k`. -/
theorem ae_tendsto_hausdorffDist_samples (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun k : ℕ ↦ hausdorffDist (range fun i : Fin (k + 1) ↦ ω i) univ) atTop
        (𝓝 0) := by
  classical
  have hcov (m : ℕ) : ∃ t : Set Ω, t.Finite ∧ univ ⊆ ⋃ c ∈ t, ball c (1 / ((m : ℝ) + 1)) := by
    obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact
      (isCompact_univ : IsCompact (univ : Set Ω)) (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
    exact ⟨t, ht, hcov⟩
  choose t ht hcover using hcov
  have hhit : ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ), ∀ m : ℕ, ∀ c : t m,
      ∃ i, ω i ∈ ball (c : Ω) (1 / ((m : ℝ) + 1)) := by
    rw [ae_all_iff]
    intro m
    have : Countable (t m) := (ht m).countable.to_subtype
    rw [ae_all_iff]
    intro c
    exact ae_exists_mem_of_measure_pos μ measurableSet_ball
      (isOpen_ball.measure_pos μ (nonempty_ball.mpr (by positivity)))
  filter_upwards [hhit] with ω hω
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hη)
  have hfin : Finite (t m) := (ht m).to_subtype
  choose idx hidx using hω m
  obtain ⟨K, hK⟩ := (Set.finite_range idx).bddAbove
  refine ⟨K, fun k hk ↦ ?_⟩
  have hr : (0 : ℝ) ≤ 2 * (1 / ((m : ℝ) + 1)) := by positivity
  have hH : hausdorffDist (range fun i : Fin (k + 1) ↦ ω i) univ ≤ 2 * (1 / ((m : ℝ) + 1)) := by
    apply hausdorffDist_le_of_mem_dist hr
    · intro x _
      exact ⟨x, mem_univ x, by rw [dist_self]; exact hr⟩
    · intro x _
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover m (mem_univ x))
      have hi := hidx ⟨c, hc⟩
      have hik : idx ⟨c, hc⟩ < k + 1 :=
        Nat.lt_succ_of_le ((hK (mem_range_self ⟨c, hc⟩)).trans hk)
      refine ⟨ω (idx ⟨c, hc⟩), ⟨⟨idx ⟨c, hc⟩, hik⟩, rfl⟩, ?_⟩
      have h1 := mem_ball.mp hxc
      have h2 := mem_ball.mp hi
      calc
        dist x (ω (idx ⟨c, hc⟩)) ≤ dist x c + dist (ω (idx ⟨c, hc⟩)) c :=
          dist_triangle_right _ _ _
        _ ≤ 2 * (1 / ((m : ℝ) + 1)) := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  linarith

end Freezing2
