module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Products of near-identity factors and the matrix exponential

For a square real matrix `G` and small nonnegative weights `h i`, the ordered product
`(1 + h 0 • G) ⋯ (1 + h (d - 1) • G)` is within `exp (T ‖G‖) ‖G‖² ∑ h i²` of
`exp (T • G)` in the `L∞` operator norm, where `T = ∑ h i`. Consequently, if the
total weight converges and the maximal weight tends to zero, the products converge
to the matrix exponential. This is the discrete-to-continuous step for
time-inhomogeneous coalescence chains whose one-step matrices are `1 + h G`.
-/

@[expose] public section

open NormedSpace Filter Topology

namespace Freezing2

/-- The ordered product `A 0 * A 1 * ⋯ * A (d - 1)`. -/
def orderedProd {𝔸 : Type*} [Monoid 𝔸] (A : ℕ → 𝔸) : ℕ → 𝔸
  | 0 => 1
  | d + 1 => orderedProd A d * A d

theorem orderedProd_add {𝔸 : Type*} [Monoid 𝔸] (A : ℕ → 𝔸) (d e : ℕ) :
    orderedProd A (d + e) = orderedProd A d * orderedProd (fun i ↦ A (d + i)) e := by
  induction e with
  | zero => simp [orderedProd]
  | succ e ih => rw [← add_assoc, orderedProd, ih, orderedProd, mul_assoc]

theorem orderedProd_congr {𝔸 : Type*} [Monoid 𝔸] {A B : ℕ → 𝔸} {d : ℕ}
    (h : ∀ i < d, A i = B i) : orderedProd A d = orderedProd B d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [orderedProd, orderedProd, ih fun i hi ↦ h i (by omega), h d (by omega)]

section Bounds

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem matrix_norm_exp_le (x : Matrix ι ι ℝ) : ‖exp x‖ ≤ Real.exp ‖x‖ := by
  have h1 := exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun m : ℕ ↦ ((m.factorial : ℝ)⁻¹) • ‖x‖ ^ m) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  refine h1.norm_le_of_bounded h2 fun m ↦ ?_
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x m) (by positivity)

theorem matrix_norm_exp_sub_one_sub_le (x : Matrix ι ι ℝ) (hx : ‖x‖ ≤ 1) :
    ‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  have h1 := (hasSum_nat_add_iff' 2).mpr (exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have h2 : HasSum (fun m : ℕ ↦ ((m.factorial : ℝ)⁻¹) • ‖x‖ ^ m) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h2' := (hasSum_nat_add_iff' 2).mpr h2
  have hle := h1.norm_le_of_bounded h2' fun m ↦ by
    rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le x (m + 2)) (by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, zero_add,
    smul_eq_mul, one_mul] at hle
  rw [sub_sub]
  refine hle.trans ?_
  have := Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg _)])
  rw [← sub_sub]
  exact (le_abs_self _).trans this

/-- **Telescoping bound.** Ordered products of `1 + h i • G` against the exponential
of the total weight. -/
theorem norm_orderedProd_sub_exp_le (G : Matrix ι ι ℝ) (h : ℕ → ℝ) (d : ℕ)
    (hh : ∀ i < d, 0 ≤ h i) (hsmall : ∀ i < d, h i * ‖G‖ ≤ 1) :
    ‖orderedProd (fun i ↦ 1 + h i • G) d - exp ((∑ i ∈ Finset.range d, h i) • G)‖ ≤
      Real.exp ((∑ i ∈ Finset.range d, h i) * ‖G‖) *
        (‖G‖ ^ 2 * ∑ i ∈ Finset.range d, h i ^ 2) := by
  induction d with
  | zero => simp [orderedProd]
  | succ d ih =>
    have ih := ih (fun i hi ↦ hh i (by omega)) (fun i hi ↦ hsmall i (by omega))
    set T := ∑ i ∈ Finset.range d, h i
    have hT : 0 ≤ T := Finset.sum_nonneg fun i hi ↦ hh i (by simp at hi; omega)
    have hd : 0 ≤ h d := hh d (by omega)
    set P := orderedProd (fun i ↦ 1 + h i • G) d
    set Q := exp (T • G)
    set A : Matrix ι ι ℝ := 1 + h d • G
    set B := exp (h d • G)
    have hsplit : exp ((T + h d) • G) = Q * B := by
      rw [add_smul]
      exact exp_add_of_commute (((Commute.refl G).smul_left T).smul_right (h d))
    have hnA : ‖A‖ ≤ Real.exp (h d * ‖G‖) := by
      calc ‖A‖ ≤ ‖(1 : Matrix ι ι ℝ)‖ + ‖h d • G‖ := norm_add_le _ _
        _ = h d * ‖G‖ + 1 := by
          rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, add_comm]
        _ ≤ Real.exp (h d * ‖G‖) := Real.add_one_le_exp _
    have hnQ : ‖Q‖ ≤ Real.exp (T * ‖G‖) := by
      refine (matrix_norm_exp_le _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]
    have hnAB : ‖A - B‖ ≤ ‖G‖ ^ 2 * h d ^ 2 := by
      have hy : ‖h d • G‖ = h d * ‖G‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]
      have := matrix_norm_exp_sub_one_sub_le (h d • G) (by rw [hy]; exact hsmall d (by omega))
      rw [norm_sub_rev, show B - A = exp (h d • G) - 1 - h d • G by
        simp only [B, A, sub_sub]]
      calc _ ≤ ‖h d • G‖ ^ 2 := this
        _ = ‖G‖ ^ 2 * h d ^ 2 := by rw [hy]; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, orderedProd, hsplit]
    have hdiff : P * A - Q * B = (P - Q) * A + Q * (A - B) := by noncomm_ring
    rw [hdiff]
    have hexp : Real.exp ((T + h d) * ‖G‖) = Real.exp (T * ‖G‖) * Real.exp (h d * ‖G‖) := by
      rw [add_mul, Real.exp_add]
    have hmono : Real.exp (T * ‖G‖) ≤ Real.exp ((T + h d) * ‖G‖) :=
      Real.exp_le_exp.mpr (by nlinarith [norm_nonneg G])
    calc ‖(P - Q) * A + Q * (A - B)‖ ≤ ‖P - Q‖ * ‖A‖ + ‖Q‖ * ‖A - B‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ Real.exp (T * ‖G‖) * (‖G‖ ^ 2 * ∑ i ∈ Finset.range d, h i ^ 2) *
            Real.exp (h d * ‖G‖) + Real.exp (T * ‖G‖) * (‖G‖ ^ 2 * h d ^ 2) := by
          gcongr
      _ ≤ Real.exp ((T + h d) * ‖G‖) *
            (‖G‖ ^ 2 * (∑ i ∈ Finset.range d, h i ^ 2 + h d ^ 2)) := by
          rw [hexp]
          have h1 : 0 ≤ ‖G‖ ^ 2 * h d ^ 2 := by positivity
          have h2 : 1 ≤ Real.exp (h d * ‖G‖) := Real.one_le_exp (by positivity)
          have h3 : 0 ≤ Real.exp (T * ‖G‖) := (Real.exp_pos _).le
          nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 h1)]

theorem tendsto_orderedProd_exp_norm {G : Matrix ι ι ℝ} {h : ℕ → ℕ → ℝ} {d : ℕ → ℕ} {T : ℝ}
    (hh : ∀ᶠ n in atTop, ∀ i < d n, 0 ≤ h n i)
    (hsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range (d n), h n i) atTop (𝓝 T))
    (hmax : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i < d n, h n i ≤ ε) :
    Tendsto (fun n ↦ ‖orderedProd (fun i ↦ 1 + h n i • G) (d n) - exp (T • G)‖)
      atTop (𝓝 0) := by
  set S := fun n ↦ ∑ i ∈ Finset.range (d n), h n i
  have hexpS : Tendsto (fun n ↦ exp (S n • G)) atTop (𝓝 (exp (T • G))) :=
    (hsum.smul_const G).exp
  have hdist : Tendsto (fun n ↦ ‖exp (S n • G) - exp (T • G)‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hexpS
  -- the telescoping error tends to zero
  have herr : Tendsto (fun n ↦ Real.exp (S n * ‖G‖) * (‖G‖ ^ 2 * ∑ i ∈ Finset.range (d n),
      h n i ^ 2)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n ↦ Real.exp (S n * ‖G‖)) atTop (𝓝 (Real.exp (T * ‖G‖))) :=
      (hsum.mul_const _).rexp
    have hsq : Tendsto (fun n ↦ ∑ i ∈ Finset.range (d n), h n i ^ 2) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hsum) 1 one_pos
      set δ := ε / (2 * (|T| + 1))
      have hδ : 0 < δ := by positivity
      obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((hmax δ hδ).and hh)
      refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
      have h1 := hN₁ n (le_of_max_le_left hn)
      have h2 := (hN₂ n (le_of_max_le_right hn)).1
      have h3 := (hN₂ n (le_of_max_le_right hn)).2
      have hnn : 0 ≤ ∑ i ∈ Finset.range (d n), h n i ^ 2 :=
        Finset.sum_nonneg fun i _ ↦ sq_nonneg _
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
      have hle : ∑ i ∈ Finset.range (d n), h n i ^ 2 ≤ δ * S n := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i < d n := Finset.mem_range.mp hi
        rw [sq]
        exact mul_le_mul_of_nonneg_right (h2 i hi') (h3 i hi')
      have hS : S n ≤ |T| + 1 := by
        rw [Real.dist_eq] at h1
        have := (abs_lt.mp h1).2
        linarith [le_abs_self T]
      calc _ ≤ δ * S n := hle
        _ ≤ δ * (|T| + 1) := mul_le_mul_of_nonneg_left hS hδ.le
        _ = ε / 2 := by
          simp only [δ]
          field_simp
        _ < ε := by linarith
    simpa using hbound.mul (hsq.const_mul (‖G‖ ^ 2))
  have hmain : ∀ᶠ n in atTop, ‖orderedProd (fun i ↦ 1 + h n i • G) (d n) - exp (T • G)‖ ≤
      Real.exp (S n * ‖G‖) * (‖G‖ ^ 2 * ∑ i ∈ Finset.range (d n), h n i ^ 2) +
        ‖exp (S n • G) - exp (T • G)‖ := by
    have hG : 0 < ‖G‖ + 1 := by positivity
    filter_upwards [hmax (1 / (‖G‖ + 1)) (by positivity), hh] with n hn hhn
    have hsmall : ∀ i < d n, h n i * ‖G‖ ≤ 1 := by
      intro i hi
      have := hn i hi
      calc h n i * ‖G‖ ≤ 1 / (‖G‖ + 1) * ‖G‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one hG]
          linarith
    calc _ = ‖(orderedProd (fun i ↦ 1 + h n i • G) (d n) - exp (S n • G)) +
          (exp (S n • G) - exp (T • G))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans
          (add_le_add_left (norm_orderedProd_sub_exp_le G (h n) (d n) hhn hsmall) _)
  have hlim := herr.add hdist
  rw [add_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hmain hlim

end Bounds

/-- **Matrix products converge to the exponential.** If the total weight of the
factors `1 + h n i • G` converges to `T` and their maximal weight tends to zero, the
ordered products converge entrywise to `exp (T • G)`. -/
theorem tendsto_orderedProd_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} {h : ℕ → ℕ → ℝ} {d : ℕ → ℕ} {T : ℝ}
    (hh : ∀ᶠ n in atTop, ∀ i < d n, 0 ≤ h n i)
    (hsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range (d n), h n i) atTop (𝓝 T))
    (hmax : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i < d n, h n i ≤ ε) :
    Tendsto (fun n ↦ orderedProd (fun i ↦ 1 + h n i • G) (d n)) atTop (𝓝 (exp (T • G))) := by
  cases isEmpty_or_nonempty ι with
  | inl hι => exact tendsto_const_nhds.congr fun _ ↦ Subsingleton.elim _ _
  | inr hι =>
    let := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_orderedProd_exp_norm hh hsum hmax)

end Freezing2
