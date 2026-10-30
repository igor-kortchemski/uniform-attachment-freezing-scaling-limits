module

public import Freezing2.Analysis.SignCounts

/-!
# A minimizing population in a fixed interior time window

The source's minimum runs over integer times satisfying `a n ≤ k ≤ b n`.
This module keeps those exact inequalities, proves eventual nonemptiness, and
shows that the minimum is sublinear by comparison with a fixed midpoint.
-/

@[expose] public section

open Filter
open scoped Topology Classical

namespace Freezing2

/-- Integer times in a closed macroscopic window, restricted to the horizon. -/
noncomputable def interiorTimes (n : ℕ) (a b : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i ↦ a * n ≤ (i : ℝ) ∧ (i : ℝ) ≤ b * n)

/-- A genuine minimizer on a nonempty window; zero is used only on empty windows. -/
noncomputable def interiorMinimizer (x : ℕ → ℕ → ℤ) (n : ℕ) (a b : ℝ) : ℕ :=
  if h : (interiorTimes n a b).Nonempty then
    (Finset.exists_min_image (interiorTimes n a b) (fun i ↦ activeCount (x n) i) h).choose
  else 0

theorem interiorMinimizer_mem (x : ℕ → ℕ → ℤ) (n : ℕ) (a b : ℝ)
    (h : (interiorTimes n a b).Nonempty) :
    interiorMinimizer x n a b ∈ interiorTimes n a b := by
  simp only [interiorMinimizer, dite_eq_left h]
  exact (Finset.exists_min_image (interiorTimes n a b) (fun i ↦ activeCount (x n) i) h).choose_spec.1

theorem interiorMinimizer_min (x : ℕ → ℕ → ℤ) (n : ℕ) (a b : ℝ)
    {i : ℕ} (hi : i ∈ interiorTimes n a b) :
    activeCount (x n) (interiorMinimizer x n a b) ≤ activeCount (x n) i := by
  have h : (interiorTimes n a b).Nonempty := ⟨i, hi⟩
  simp only [interiorMinimizer, dite_eq_left h]
  exact (Finset.exists_min_image (interiorTimes n a b) (fun j ↦ activeCount (x n) j) h).choose_spec.2 i hi

/-- The selected index is always a valid time, including before the window is nonempty. -/
theorem interiorMinimizer_le (x : ℕ → ℕ → ℤ) (n : ℕ) (a b : ℝ) :
    interiorMinimizer x n a b ≤ n := by
  by_cases h : (interiorTimes n a b).Nonempty
  · have hm := interiorMinimizer_mem x n a b h
    have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    omega
  · simp [interiorMinimizer, h]

/-- A fixed interior real time eventually provides an integer time in the window. -/
theorem eventually_floor_mem_interiorTimes {a b c : ℝ}
    (ha : 0 ≤ a) (hac : a < c) (hcb : c < b) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ⌊(n : ℝ) * c⌋₊ ∈ interiorTimes n a b := by
  have hc := tendsto_floor_time_div (ha.trans hac.le)
  filter_upwards [hc.eventually_const_lt hac, hc.eventually_lt_const hcb,
    eventually_gt_atTop 0] with n hlow hupp hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : ⌊(n : ℝ) * c⌋₊ ≤ n := by
    apply Nat.floor_le_of_le
    simpa using mul_le_mul_of_nonneg_left (hcb.le.trans hb) hn'.le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega),
    (le_div_iff₀ hn').mp hlow.le, (div_le_iff₀ hn').mp hupp.le⟩

theorem eventually_interiorTimes_nonempty {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop, (interiorTimes n a b).Nonempty := by
  have h := eventually_floor_mem_interiorTimes ha
    (show a < (a + b) / 2 by linarith) (show (a + b) / 2 < b by linarith) hb
  exact h.mono fun n hn ↦ ⟨_, hn⟩

/-- The selected minimizer lies in the original macroscopic window eventually. -/
theorem eventually_interiorMinimizer_window (x : ℕ → ℕ → ℤ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      a ≤ (interiorMinimizer x n a b : ℝ) / n ∧
      (interiorMinimizer x n a b : ℝ) / n ≤ b := by
  filter_upwards [eventually_interiorTimes_nonempty ha hab hb,
    eventually_gt_atTop 0] with n hne hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := (Finset.mem_filter.mp (interiorMinimizer_mem x n a b hne)).2
  exact ⟨(le_div_iff₀ hn').mpr hi.1, (div_le_iff₀ hn').mpr hi.2⟩

/-- The minimum population in a nondegenerate interior window is sublinear. -/
theorem interiorMinimizer_population_sublinear {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Tendsto (fun n : ℕ ↦
      (activeCount (x n) (interiorMinimizer x n a b) : ℝ) / n) atTop (𝓝 0) := by
  let c : ℝ := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hl := population_sublinear_at hx hα hL1 hpos (ha.trans_lt hac) (hcb.le.trans hb)
  have hnonneg (n : ℕ) :
      0 ≤ (activeCount (x n) (interiorMinimizer x n a b) : ℝ) / n :=
    div_nonneg (activeCount_real_pos hx n (interiorMinimizer_le x n a b)).le (Nat.cast_nonneg n)
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hl
  filter_upwards [eventually_floor_mem_interiorTimes ha hac hcb hb] with n hn
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast interiorMinimizer_min x n a b hn

end Freezing2
