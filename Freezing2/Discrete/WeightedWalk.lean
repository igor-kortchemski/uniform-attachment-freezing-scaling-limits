module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

/-!
# Weighted up/down identities

These are the finite deterministic identities underlying Lemma `lem:hnalpha`
in the source paper. A path takes values in the natural numbers and moves by
one at each step. The weighted crossing balance telescopes in a potential.
This gives an interval identity with the correct starting height, including
intervals consisting of a single upward step.
-/

@[expose] public section

namespace Freezing2

/-- Potential whose increment across the edge from `k` to `k+1` is `w (k+1)`. -/
def walkPotential (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, w (j + 1)

@[simp] theorem walkPotential_zero (w : ℕ → ℝ) : walkPotential w 0 = 0 := by
  simp [walkPotential]

@[simp] theorem walkPotential_succ (w : ℕ → ℝ) (k : ℕ) :
    walkPotential w (k + 1) = walkPotential w k + w (k + 1) := by
  simp [walkPotential, Finset.sum_range_succ]

/-- A unit step crosses exactly one edge, with its orientation. -/
theorem weighted_step_balance (w : ℕ → ℝ) (p q : ℕ)
    (h : q = p + 1 ∨ p = q + 1) :
    (if q = p + 1 then w q else 0) -
      (if p = q + 1 then w p else 0) =
      walkPotential w q - walkPotential w p := by
  rcases h with h | h
  · have hn : p ≠ q + 1 := by omega
    rw [ite_eq_left h, ite_eq_right hn, sub_zero, h, walkPotential_succ]
    ring
  · have hn : q ≠ p + 1 := by omega
    rw [ite_eq_right hn, ite_eq_left h, zero_sub, h, walkPotential_succ]
    ring

/-- Exact weighted balance on an interval of `n` steps starting at time `a`.
The endpoint potential uses `S a`, i.e. the height *before* the first step. -/
theorem weighted_crossing_balance (S : ℕ → ℕ) (w : ℕ → ℝ) (a n : ℕ)
    (h : ∀ i < n, S (a + i + 1) = S (a + i) + 1 ∨
      S (a + i) = S (a + i + 1) + 1) :
    (∑ i ∈ Finset.range n,
      if S (a + i + 1) = S (a + i) + 1 then w (S (a + i + 1)) else 0) -
    (∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then w (S (a + i)) else 0) =
    walkPotential w (S (a + n)) - walkPotential w (S a) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i ∈ Finset.range n,
        (walkPotential w (S (a + (i + 1))) - walkPotential w (S (a + i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [Nat.add_assoc] using weighted_step_balance w
        (S (a + i)) (S (a + i + 1)) (h i (Finset.mem_range.mp hi))
    _ = _ := by simpa using Finset.sum_range_sub (fun i ↦ walkPotential w (S (a + i))) n

/-- Real harmonic potential, with no division by zero in its defining sum. -/
noncomputable def harmonicPotential (k : ℕ) : ℝ := walkPotential (fun j ↦ (j : ℝ)⁻¹) k

/-- The harmonic balance used in the pairing argument for Lemma `lem:hnalpha`.
This is finite algebra; the asymptotic assumptions and conclusions are separate. -/
theorem harmonic_crossing_balance (S : ℕ → ℕ) (a n : ℕ)
    (h : ∀ i < n, S (a + i + 1) = S (a + i) + 1 ∨
      S (a + i) = S (a + i + 1) + 1) :
    (∑ i ∈ Finset.range n,
      if S (a + i + 1) = S (a + i) + 1 then (S (a + i + 1) : ℝ)⁻¹ else 0) =
    (∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then (S (a + i + 1) + 1 : ℝ)⁻¹ else 0) +
    harmonicPotential (S (a + n)) - harmonicPotential (S a) := by
  have hb := weighted_crossing_balance S (fun j ↦ (j : ℝ)⁻¹) a n h
  have he : (∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then (S (a + i) : ℝ)⁻¹ else 0) =
      ∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then (S (a + i + 1) + 1 : ℝ)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hd
    · rw [hd, Nat.cast_add, Nat.cast_one]
    · rfl
  rw [he] at hb
  unfold harmonicPotential
  linarith

/-- Harmonic potential agrees with Mathlib's rational harmonic numbers. -/
theorem harmonicPotential_eq_harmonic (k : ℕ) :
    harmonicPotential k = (harmonic k : ℝ) := by
  simp [harmonicPotential, walkPotential, harmonic]

/-- The endpoint correction is logarithmic. -/
theorem harmonicPotential_le_one_add_log (k : ℕ) :
    harmonicPotential k ≤ 1 + Real.log k := by
  rw [harmonicPotential_eq_harmonic]
  exact harmonic_le_one_add_log k

/-- Harmonic potentials are nonnegative, including at zero. -/
theorem harmonicPotential_nonneg (k : ℕ) : 0 ≤ harmonicPotential k := by
  unfold harmonicPotential walkPotential
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Reciprocal weights of the upward steps in `(a,a+n]`. -/
noncomputable def reciprocalUpSum (S : ℕ → ℕ) (a n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    if S (a + i + 1) = S (a + i) + 1 then (S (a + i + 1) : ℝ)⁻¹ else 0

/-- Reciprocal weights of the downward steps in `(a,a+n]`. -/
noncomputable def reciprocalDownSum (S : ℕ → ℕ) (a n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    if S (a + i) = S (a + i + 1) + 1 then (S (a + i + 1) : ℝ)⁻¹ else 0

/-- Positive correction from replacing `1/(S+1)` by `1/S` on down steps. -/
noncomputable def reciprocalErrorSum (S : ℕ → ℕ) (a n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    if S (a + i) = S (a + i + 1) + 1 then
      ((S (a + i + 1) : ℝ) * (S (a + i + 1) + 1))⁻¹ else 0

theorem reciprocalErrorSum_nonneg (S : ℕ → ℕ) (a n : ℕ) :
    0 ≤ reciprocalErrorSum S a n := by
  unfold reciprocalErrorSum
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

/-- The exact interval identity behind the uniform estimate in Lemma `hnalpha(iv)`.
The paper's printed minimum-height formula has an off-by-one boundary error;
the endpoint potential identity avoids that error. -/
theorem reciprocal_up_sub_down (S : ℕ → ℕ) (a n : ℕ)
    (h : ∀ i < n, S (a + i + 1) = S (a + i) + 1 ∨
      S (a + i) = S (a + i + 1) + 1)
    (hpos : ∀ i < n, 0 < S (a + i + 1)) :
    reciprocalUpSum S a n - reciprocalDownSum S a n =
      harmonicPotential (S (a + n)) - harmonicPotential (S a) -
      reciprocalErrorSum S a n := by
  have hb := harmonic_crossing_balance S a n h
  have he : (∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then
        (S (a + i + 1) + 1 : ℝ)⁻¹ else 0) =
      reciprocalDownSum S a n - reciprocalErrorSum S a n := by
    unfold reciprocalDownSum reciprocalErrorSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hd
    · have hs : (S (a + i + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hpos i (Finset.mem_range.mp hi)))
      have hs1 : (S (a + i + 1) : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · simp
  rw [he] at hb
  change reciprocalUpSum S a n = _ at hb
  linarith

/-- A bound uniform over intervals once endpoint heights and the correction sum
are bounded. This is a finite estimate, not an assumed scaling limit. -/
theorem reciprocal_balance_bound (S : ℕ → ℕ) (a n : ℕ)
    (h : ∀ i < n, S (a + i + 1) = S (a + i) + 1 ∨
      S (a + i) = S (a + i + 1) + 1)
    (hpos : ∀ i < n, 0 < S (a + i + 1)) :
    |reciprocalUpSum S a n - reciprocalDownSum S a n| ≤
      reciprocalErrorSum S a n + harmonicPotential (S (a + n)) +
      harmonicPotential (S a) := by
  rw [reciprocal_up_sub_down S a n h hpos]
  have h₁ := harmonicPotential_nonneg (S (a + n))
  have h₂ := harmonicPotential_nonneg (S a)
  have h₃ := reciprocalErrorSum_nonneg S a n
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Edge weight in the coalescence hazard. At a genuine upward step from a
positive height, its denominator is strictly positive. -/
noncomputable def coalescenceWeight (k : ℕ) : ℝ :=
  ((k : ℝ) * ((k : ℝ) - 1))⁻¹

/-- The potential for the coalescence edge weight telescopes explicitly. -/
theorem coalescencePotential_succ (k : ℕ) :
    walkPotential coalescenceWeight (k + 1) = 1 - ((k : ℝ) + 1)⁻¹ := by
  induction k with
  | zero => simp [walkPotential, coalescenceWeight]
  | succ k ih =>
    rw [walkPotential_succ, ih]
    simp only [coalescenceWeight, Nat.cast_add, Nat.cast_one]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have hk2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
    have he : (k : ℝ) + 1 + 1 - 1 = (k : ℝ) + 1 := by ring
    rw [he]
    field_simp
    ring

theorem coalescencePotential_eq (k : ℕ) (hk : 0 < k) :
    walkPotential coalescenceWeight k = 1 - (k : ℝ)⁻¹ := by
  cases k with
  | zero => omega
  | succ k => simpa using coalescencePotential_succ k

/-- Exact form of the weighted pairing used in `eq:lemme h point cinq1`.
The boundary is `1/S_a - 1/S_b`; no hidden uniformity assumption is needed. -/
theorem coalescence_crossing_balance (S : ℕ → ℕ) (a n : ℕ)
    (h : ∀ i < n, S (a + i + 1) = S (a + i) + 1 ∨
      S (a + i) = S (a + i + 1) + 1)
    (ha : 0 < S a) (hb : 0 < S (a + n)) :
    (∑ i ∈ Finset.range n,
      if S (a + i + 1) = S (a + i) + 1 then
        ((S (a + i + 1) : ℝ) * ((S (a + i + 1) : ℝ) - 1))⁻¹ else 0) -
    (∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then
        ((S (a + i + 1) : ℝ) * ((S (a + i + 1) : ℝ) + 1))⁻¹ else 0) =
    (S a : ℝ)⁻¹ - (S (a + n) : ℝ)⁻¹ := by
  have hw := weighted_crossing_balance S coalescenceWeight a n h
  rw [coalescencePotential_eq _ hb, coalescencePotential_eq _ ha] at hw
  have hd : (∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then coalescenceWeight (S (a + i)) else 0) =
      ∑ i ∈ Finset.range n,
      if S (a + i) = S (a + i + 1) + 1 then
        ((S (a + i + 1) : ℝ) * ((S (a + i + 1) : ℝ) + 1))⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · simp only [coalescenceWeight, hi, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      rw [mul_comm]
    · rfl
  rw [hd] at hw
  unfold coalescenceWeight at hw
  linarith

end Freezing2
