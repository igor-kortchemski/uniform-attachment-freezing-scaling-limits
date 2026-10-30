module

public import Freezing2.Discrete.Walk
public import Freezing2.Discrete.WeightedWalk

/-!
# Finite estimates for the paper's driving sequence

These specializations connect the potential identities to the integer signed
walk used in the paper. No asymptotic assumptions are hidden in their premises.
-/

@[expose] public section

namespace Freezing2

/-- The population never exceeds the initial vertex plus the number of steps. -/
theorem activeCount_le_time_add_one (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    activeCount x n ≤ (n : ℤ) + 1 := by
  have hs := upSteps_card_add_downSteps_card x hx (a := 0) (b := n)
  have hv := twice_vertex_count x hx n
  omega

theorem activeCount_toNat_le_time_add_one (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    (activeCount x n).toNat ≤ n + 1 := by
  have h := activeCount_le_time_add_one x hx n
  omega

/-- Monotonicity of the harmonic potential. -/
theorem harmonicPotential_mono : Monotone harmonicPotential := by
  intro a b hab
  unfold harmonicPotential walkPotential
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro i _ _
  positivity

/-- All endpoint harmonic corrections in a surviving path of length `N` share
one logarithmic bound. -/
theorem driver_harmonic_endpoint_bound (x : ℕ → ℤ) (hx : IsSigned x)
    {N i : ℕ} (hi : i ≤ N) :
    harmonicPotential (activeCount x i).toNat ≤ 1 + Real.log (N + 1) := by
  calc
    _ ≤ harmonicPotential (N + 1) := harmonicPotential_mono
      ((activeCount_toNat_le_time_add_one x hx i).trans (by omega))
    _ ≤ _ := by simpa using harmonicPotential_le_one_add_log (N + 1)

/-- Exact finite counterpart of the global pairing display in Lemma `hnalpha(iii)`.
The endpoint contribution is `H(Sₙ)−1 = ∑_{s=2}^{Sₙ} 1/s`.
The plus/down sums use the natural representation, whose signs are characterized
by `activeCount_nat_up_iff` and `activeCount_nat_down_iff`. -/
theorem driver_reciprocal_pairing (x : ℕ → ℤ) (hx : IsSigned x) {N : ℕ}
    (hs : SurvivesThrough x N) :
    reciprocalUpSum (fun i ↦ (activeCount x i).toNat) 0 N -
      reciprocalDownSum (fun i ↦ (activeCount x i).toNat) 0 N =
      harmonicPotential (activeCount x N).toNat - 1 -
      reciprocalErrorSum (fun i ↦ (activeCount x i).toNat) 0 N := by
  have h := reciprocal_up_sub_down (fun i ↦ (activeCount x i).toNat) 0 N
    (fun i hi ↦ by simpa using activeCount_nat_steps x hx hs hi)
    (fun i hi ↦ by simpa using activeCount_nat_pos x hs (by omega : i + 1 ≤ N))
  simpa [harmonicPotential, walkPotential] using h

/-- Correct interval version of the paper's weighted balance, with a bound
uniform in the starting time and interval length. The reciprocal correction
still needs an asymptotic estimate to obtain Lemma `hnalpha(iv)`. -/
theorem driver_reciprocal_balance_bound (x : ℕ → ℤ) (hx : IsSigned x) {N a n : ℕ}
    (hs : SurvivesThrough x N) (han : a + n ≤ N) :
    |reciprocalUpSum (fun i ↦ (activeCount x i).toNat) a n -
      reciprocalDownSum (fun i ↦ (activeCount x i).toNat) a n| ≤
      reciprocalErrorSum (fun i ↦ (activeCount x i).toNat) a n +
      2 * (1 + Real.log (N + 1)) := by
  have h := reciprocal_balance_bound (fun i ↦ (activeCount x i).toNat) a n
    (fun i hi ↦ activeCount_nat_steps x hx hs (by omega : a + i < N))
    (fun i hi ↦ activeCount_nat_pos x hs (by omega : a + i + 1 ≤ N))
  have hb := driver_harmonic_endpoint_bound x hx han
  have ha := driver_harmonic_endpoint_bound x hx (by omega : a ≤ N)
  linarith

end Freezing2
