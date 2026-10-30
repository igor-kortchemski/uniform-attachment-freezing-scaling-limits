module

public import Freezing2.Analysis.LocalSquareProfiles
public import Freezing2.Analysis.SmallSetL1

/-!
# Local population lower bounds from reciprocal-square convergence

A population of size `M` can grow by at most `M` in the next `M` steps.
Consequently its squared reciprocal profile has integral at least
`(N^α)^2 / (4 N M)` over those mesh cells. If `M/N → 0` and the starting
positions stay inside a fixed interior interval, local L¹ convergence of the
squares forces this integral to vanish.

This proves the analytic mechanism of equation `eq:cvminSinfini` by using
exactly `M` cells, in place of the manuscript's auxiliary sequence `ηₙ` and
asymptotic evaluation of a reciprocal-square sum.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- The closed real interval covered by `m` mesh cells starting at time `k`. -/
def populationWindow (n k m : ℕ) : Set ℝ := Icc ((k : ℝ) / n) (((k + m : ℕ) : ℝ) / n)

/-- Exact measure of the mesh interval, including the totalized zero horizon. -/
theorem volume_populationWindow (n k m : ℕ) :
    volume (populationWindow n k m) = ENNReal.ofReal ((m : ℝ) / n) := by
  rw [populationWindow, Real.volume_Icc]
  congr 1
  push_cast
  ring

/-- A population of size `M` cannot exceed `2M` in the next `M` steps,
so its squared reciprocal is uniformly bounded below on those mesh cells. -/
theorem reciprocal_sq_ge_on_populationWindow
    {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x) (α : ℝ) {N k M : ℕ}
    (hN : 0 < N) (hKM : k + M ≤ N) (hM : M = (activeCount (x N) k).toNat)
    {t : ℝ} (ht : t ∈ populationWindow N k M) :
    ((N : ℝ) ^ α / (2 * M)) ^ 2 ≤ (reciprocalProfile x α N t) ^ 2 := by
  have hk : k ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hMp : 0 < M := by
    rw [hM]
    exact activeCount_nat_pos (x N) (hx N).2 hk
  have hMc : (M : ℝ) = activeCount (x N) k := by
    rw [hM]
    exact_mod_cast activeCount_nat_cast (x N) (hx N).2 hk
  have hfloor1 : k ≤ ⌊(N : ℝ) * t⌋₊ := by
    apply Nat.le_floor
    have := (div_le_iff₀ hNp).mp ht.1
    nlinarith
  have hfloor2 : ⌊(N : ℝ) * t⌋₊ ≤ k + M := by
    apply Nat.floor_le_of_le
    have := (le_div_iff₀ hNp).mp ht.2
    nlinarith
  have hS : (activeCount (x N) ⌊(N : ℝ) * t⌋₊ : ℝ) ≤ 2 * M := by
    have hwalk := activeCount_real_sub_le (x N) (hx N).1 hfloor1
    have hidx : (⌊(N : ℝ) * t⌋₊ : ℝ) ≤ (k : ℝ) + M := by exact_mod_cast hfloor2
    nlinarith
  have hden := activeCount_real_pos hx N (hfloor2.trans hKM)
  have hbound : (N : ℝ) ^ α / (2 * M) ≤ reciprocalProfile x α N t :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg N) α) hden hS
  exact pow_le_pow_left₀ (by positivity) hbound 2

/-- Finite integral bound underlying the local minimum estimate. -/
theorem population_window_integral_lower_bound
    {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x) (α : ℝ) {N k M : ℕ}
    (hN : 0 < N) (hKM : k + M ≤ N) (hM : M = (activeCount (x N) k).toNat) :
    ((N : ℝ) ^ α) ^ 2 / ((N : ℝ) * M) ≤
      4 * ∫ t in populationWindow N k M, (reciprocalProfile x α N t) ^ 2 := by
  have hk : k ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hMp : 0 < M := by
    rw [hM]
    exact activeCount_nat_pos (x N) (hx N).2 hk
  have hMp' : (0 : ℝ) < M := by exact_mod_cast hMp
  have hb : ((k + M : ℕ) : ℝ) / N ≤ 1 :=
    (div_le_one hNp).mpr (by exact_mod_cast hKM)
  have hi : IntegrableOn (fun t ↦ (reciprocalProfile x α N t) ^ 2)
      (populationWindow N k M) volume :=
    integrableOn_sq_reciprocalProfile x α N (by positivity) hb
  have hc : IntegrableOn (fun _ : ℝ ↦ ((N : ℝ) ^ α / (2 * M)) ^ 2)
      (populationWindow N k M) volume := integrableOn_const (by simp [populationWindow])
  have h := setIntegral_mono_on hc hi measurableSet_Icc
    (fun t ht ↦ reciprocal_sq_ge_on_populationWindow hx α hN hKM hM ht)
  have hv : volume.real (populationWindow N k M) = (M : ℝ) / N := by
    rw [Measure.real, volume_populationWindow, ENNReal.toReal_ofReal (by positivity)]
  rw [setIntegral_const, hv, smul_eq_mul] at h
  have heq : 4 * ((M : ℝ) / N * ((N : ℝ) ^ α / (2 * M)) ^ 2) =
      ((N : ℝ) ^ α) ^ 2 / ((N : ℝ) * M) := by
    field_simp
    ring
  linarith

/-- Local square-profile convergence excludes a small population persisting
inside the interior. The sublinear-size premise will be supplied by selecting
an interior minimum and comparing it with a fixed-time population. -/
theorem tendsto_scaled_reciprocal_population_of_sublinear
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hL1 : HasL1ReciprocalProfile x α g)
    (h2 : HasLocalSquareMomentProfile x α g)
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hinterior : ∀ᶠ n : ℕ in atTop, a ≤ (k n : ℝ) / n ∧ (k n : ℝ) / n ≤ b)
    (hsmall : Tendsto (fun n : ℕ ↦ (activeCount (x n) (k n) : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α) ^ 2 /
      ((n : ℝ) * (activeCount (x n) (k n) : ℝ))) atTop (𝓝 0) := by
  let m : ℕ → ℕ := fun n ↦ (activeCount (x n) (k n)).toNat
  let A : ℝ := a / 2
  let B : ℝ := (b + 1) / 2
  let K : Set ℝ := Icc A B
  let J : ℕ → Set ℝ := fun n ↦ populationWindow n (k n) (m n)
  have hA : 0 < A := by dsimp [A]; positivity
  have hAB : A < B := by dsimp [A, B]; linarith
  have hB : B < 1 := by dsimp [B]; linarith
  have hm (n : ℕ) : (m n : ℝ) = activeCount (x n) (k n) := by
    dsimp [m]
    exact_mod_cast activeCount_nat_cast (x n) (hx n).2 (hk n)
  have hmSmall : Tendsto (fun n : ℕ ↦ (m n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [hm] using hsmall
  have hvol : Tendsto (fun n : ℕ ↦ volume (J n)) atTop (𝓝 0) := by
    simpa only [J, volume_populationWindow, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hmSmall
  have hrestricted : Tendsto ((volume.restrict K) ∘ J) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol
      (fun _ ↦ zero_le) (fun n ↦ Measure.restrict_apply_le K (J n))
  have hI : Tendsto (fun n : ℕ ↦ ∫ t in J n,
      (reciprocalProfile x α n t) ^ 2 ∂(volume.restrict K)) atTop (𝓝 0) :=
    tendsto_integral_on_small_sets_of_l1
      (fun n ↦ integrableOn_sq_reciprocalProfile x α n hA.le hB.le)
      (h2 A B hA hAB hB).1
      (tendsto_integral_abs_sq_profile_sub_local hL1 h2 hA hAB hB) hrestricted
  have hfit : ∀ᶠ n : ℕ in atTop, J n ⊆ K ∧ k n + m n ≤ n := by
    have hgap : 0 < (1 - b) / 2 := by linarith
    filter_upwards [hinterior, hmSmall.eventually_lt_const hgap, eventually_gt_atTop 0]
      with n hn hmn hn0
    have hNp : (0 : ℝ) < n := by exact_mod_cast hn0
    have hleft : A ≤ (k n : ℝ) / n := by dsimp [A]; linarith [hn.1]
    have hright : ((k n + m n : ℕ) : ℝ) / n ≤ B := by
      push_cast
      rw [add_div]
      dsimp [B]
      linarith [hn.2]
    constructor
    · intro t ht
      exact ⟨hleft.trans ht.1, ht.2.trans hright⟩
    · have hle : ((k n + m n : ℕ) : ℝ) ≤ n :=
        (div_le_one hNp).mp (hright.trans hB.le)
      exact_mod_cast hle
  have hI' : Tendsto (fun n : ℕ ↦ ∫ t in J n,
      (reciprocalProfile x α n t) ^ 2) atTop (𝓝 0) := by
    apply hI.congr'
    filter_upwards [hfit] with n hn
    rw [Measure.restrict_restrict_of_subset hn.1]
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by
    exact div_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg n)
      (activeCount_real_pos hx n (hk n)).le)) _ (by simpa using hI'.const_mul 4)
  filter_upwards [hfit, eventually_gt_atTop 0] with n hn hn0
  have h := population_window_integral_lower_bound hx α hn0 hn.2 (rfl : m n = _)
  simpa only [hm, J] using h

/-- The preceding conclusion in the exact power normalization of
`eq:cvminSinfini`. -/
theorem tendsto_rpow_reciprocal_population_of_sublinear
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hL1 : HasL1ReciprocalProfile x α g)
    (h2 : HasLocalSquareMomentProfile x α g)
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ n)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hinterior : ∀ᶠ n : ℕ in atTop, a ≤ (k n : ℝ) / n ∧ (k n : ℝ) / n ≤ b)
    (hsmall : Tendsto (fun n : ℕ ↦ (activeCount (x n) (k n) : ℝ) / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2 * α - 1) /
      (activeCount (x n) (k n) : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_scaled_reciprocal_population_of_sublinear hx hL1 h2 k hk
    ha hab hb hinterior hsmall).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hNp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub hNp, Real.rpow_one,
    show 2 * α = α * (2 : ℕ) by ring, Real.rpow_mul_natCast hNp.le]
  ring

end Freezing2
