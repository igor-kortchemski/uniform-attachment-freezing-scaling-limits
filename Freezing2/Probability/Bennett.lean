module

public import Freezing2.Analysis.BennettFunction
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Basic

/-!
# Bennett's inequality for independent Bernoulli variables

The Bernoulli law `bernoulliMeasure 1 0 p` gives mass `p` to `1` and mass
`1-p` to `0`. Thus parameters in `unitInterval` encode exactly the source's
assumptions `pᵢ ∈ [0,1]`, including both endpoints. Independence is not identical
distribution. The proofs use the product of moment generating functions and
Chernoff's inequality.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace Freezing2

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Exact moment generating function of a real Bernoulli variable. -/
theorem mgf_of_hasLaw_bernoulli {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (s : ℝ) :
    mgf Y μ s = 1 + (p : ℝ) * (Real.exp s - 1) := by
  unfold mgf
  calc
    (∫ ω, Real.exp (s * Y ω) ∂μ) =
        ∫ y, Real.exp (s * y) ∂bernoulliMeasure (1 : ℝ) 0 p :=
      hY.integral_comp (f := fun y : ℝ ↦ Real.exp (s * y)) (by fun_prop)
    _ = 1 + (p : ℝ) * (Real.exp s - 1) := by
      rw [integral_bernoulliMeasure]
      simp only [mul_one, mul_zero, Real.exp_zero, smul_eq_mul]
      ring

omit [IsProbabilityMeasure μ] in
/-- Bernoulli exponential moments are finite for every real parameter. -/
theorem integrable_exp_mul_of_hasLaw_bernoulli {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (s : ℝ) :
    Integrable (fun ω ↦ Real.exp (s * Y ω)) μ :=
  hY.integrable_comp (integrable_bernoulliMeasure 1 0 p (fun y : ℝ ↦ Real.exp (s * y)))

omit [IsProbabilityMeasure μ] in
theorem mgf_bernoulli_le_exp {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (s : ℝ) :
    mgf Y μ s ≤ Real.exp ((p : ℝ) * (Real.exp s - 1)) := by
  rw [mgf_of_hasLaw_bernoulli hY]
  simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ) * (Real.exp s - 1))

/-- An almost-everywhere measurable version of the standard independent-sum
exponential-integrability lemma, suitable for `HasLaw` hypotheses. -/
theorem integrable_exp_mul_sum_of_independent {Y : ι → Ω → ℝ}
    (h_indep : iIndepFun Y μ) (h_meas : ∀ i, AEMeasurable (Y i) μ)
    (s : ℝ) (a : Finset ι)
    (h_int : ∀ i ∈ a, Integrable (fun ω ↦ Real.exp (s * Y i ω)) μ) :
    Integrable (fun ω ↦ Real.exp (s * (∑ i ∈ a, Y i) ω)) μ := by
  classical
  induction a using Finset.induction_on with
  | empty => simp
  | insert i a hi ih =>
    rw [Finset.sum_insert hi]
    apply IndepFun.integrable_exp_mul_add
      (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi).symm
      (h_int i (Finset.mem_insert_self i a))
    exact ih (fun j hj ↦ h_int j (Finset.mem_insert_of_mem hj))

omit [IsProbabilityMeasure μ] in
/-- The Poisson MGF bound for a finite sum of independent Bernoulli variables. -/
theorem mgf_sum_bernoulli_le_exp {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (h_indep : iIndepFun Y μ)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (a : Finset ι) (s : ℝ) :
    mgf (∑ i ∈ a, Y i) μ s ≤
      Real.exp ((∑ i ∈ a, (p i : ℝ)) * (Real.exp s - 1)) := by
  rw [h_indep.mgf_sum₀ (fun i ↦ (hY i).aemeasurable)]
  calc
    (∏ i ∈ a, mgf (Y i) μ s) ≤
        ∏ i ∈ a, Real.exp ((p i : ℝ) * (Real.exp s - 1)) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) (fun i _ ↦ mgf_bernoulli_le_exp (hY i) s)
    _ = Real.exp ((∑ i ∈ a, (p i : ℝ)) * (Real.exp s - 1)) := by
      rw [← Real.exp_sum, Finset.sum_mul]

/-- The centered negative exponential is bounded by its positive counterpart.
This gives a common Bennett bound for both tails. -/
theorem exp_neg_add_two_mul_le_exp {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s) + 2 * s ≤ Real.exp s := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun x : ℝ ↦ Real.exp x - Real.exp (-x) - 2 * x)
        (Real.exp x + Real.exp (-x) - 2) x := by
    convert ((Real.hasDerivAt_exp x).sub
      ((hasDerivAt_id x).neg.exp)).sub ((hasDerivAt_id x).const_mul 2) using 1
    · rfl
    · simp
  have hmono : Monotone (fun x : ℝ ↦ Real.exp x - Real.exp (-x) - 2 * x) := by
    apply monotone_of_hasDerivAt_nonneg hderiv
    intro x
    change 0 ≤ Real.exp x + Real.exp (-x) - 2
    linarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x)]
  have h := hmono hs
  simp only [neg_zero, Real.exp_zero, sub_self, mul_zero] at h
  linarith

/-- Evaluation of the Chernoff exponent at its positive optimizer. -/
theorem bennett_chernoff_exponent {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    -Real.log (1 + t / m) * (m + t) +
        m * (Real.exp (Real.log (1 + t / m)) - 1) =
      -m * bennettFunction (t / m) := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hbase : 0 < 1 + t / m := by positivity
  rw [Real.exp_log hbase]
  unfold bennettFunction
  field_simp
  ring

/-- Upper-tail half of Proposition `prop:bennett`, for an arbitrary finite
index set. The source's strict inequality is retained. -/
theorem bennett_upper_tail {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (h_indep : iIndepFun Y μ)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (a : Finset ι) {t : ℝ} (hm : 0 < ∑ i ∈ a, (p i : ℝ)) (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ a, (p i : ℝ)) + t < (∑ i ∈ a, Y i) ω} ≤
      Real.exp (-(∑ i ∈ a, (p i : ℝ)) *
        bennettFunction (t / (∑ i ∈ a, (p i : ℝ)))) := by
  let m : ℝ := ∑ i ∈ a, (p i : ℝ)
  let q : ℝ := Real.log (1 + t / m)
  have hm' : 0 < m := hm
  have hq : 0 ≤ q := by
    apply Real.log_nonneg
    have htm : 0 < t / m := div_pos ht hm'
    linarith
  have hint : Integrable (fun ω ↦ Real.exp (q * (∑ i ∈ a, Y i) ω)) μ :=
    integrable_exp_mul_sum_of_independent h_indep (fun i ↦ (hY i).aemeasurable) q a
      (fun i _ ↦ integrable_exp_mul_of_hasLaw_bernoulli (hY i) q)
  change μ.real {ω | m + t < (∑ i ∈ a, Y i) ω} ≤ Real.exp (-m * bennettFunction (t / m))
  calc
    _ ≤ μ.real {ω | m + t ≤ (∑ i ∈ a, Y i) ω} :=
      measureReal_mono (fun ω (h : m + t < (∑ i ∈ a, Y i) ω) ↦ h.le)
    _ ≤ Real.exp (-q * (m + t)) * mgf (∑ i ∈ a, Y i) μ q :=
      measure_ge_le_exp_mul_mgf (m + t) hq hint
    _ ≤ Real.exp (-q * (m + t)) * Real.exp (m * (Real.exp q - 1)) :=
      mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le_exp h_indep hY a q)
        (Real.exp_pos _).le
    _ = Real.exp (-m * bennettFunction (t / m)) := by
      rw [← Real.exp_add]
      congr 1
      exact bennett_chernoff_exponent hm' ht.le

/-- Lower-tail half of Proposition `prop:bennett`. The same rate function is
valid even when the threshold is negative; no additional restriction `t < m`
is introduced. -/
theorem bennett_lower_tail {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (h_indep : iIndepFun Y μ)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (a : Finset ι) {t : ℝ} (hm : 0 < ∑ i ∈ a, (p i : ℝ)) (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ a, Y i) ω < (∑ i ∈ a, (p i : ℝ)) - t} ≤
      Real.exp (-(∑ i ∈ a, (p i : ℝ)) *
        bennettFunction (t / (∑ i ∈ a, (p i : ℝ)))) := by
  let m : ℝ := ∑ i ∈ a, (p i : ℝ)
  let q : ℝ := Real.log (1 + t / m)
  have hm' : 0 < m := hm
  have hq : 0 ≤ q := by
    apply Real.log_nonneg
    have htm : 0 < t / m := div_pos ht hm'
    linarith
  have hint : Integrable (fun ω ↦ Real.exp (-q * (∑ i ∈ a, Y i) ω)) μ :=
    integrable_exp_mul_sum_of_independent h_indep (fun i ↦ (hY i).aemeasurable) (-q) a
      (fun i _ ↦ integrable_exp_mul_of_hasLaw_bernoulli (hY i) (-q))
  change μ.real {ω | (∑ i ∈ a, Y i) ω < m - t} ≤ Real.exp (-m * bennettFunction (t / m))
  calc
    _ ≤ μ.real {ω | (∑ i ∈ a, Y i) ω ≤ m - t} :=
      measureReal_mono (fun ω (h : (∑ i ∈ a, Y i) ω < m - t) ↦ h.le)
    _ ≤ Real.exp (-(-q) * (m - t)) * mgf (∑ i ∈ a, Y i) μ (-q) :=
      measure_le_le_exp_mul_mgf (m - t) (neg_nonpos.mpr hq) hint
    _ ≤ Real.exp (-(-q) * (m - t)) * Real.exp (m * (Real.exp (-q) - 1)) :=
      mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le_exp h_indep hY a (-q))
        (Real.exp_pos _).le
    _ ≤ Real.exp (-q * (m + t)) * Real.exp (m * (Real.exp q - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcomparison := mul_le_mul_of_nonneg_left (exp_neg_add_two_mul_le_exp hq) hm'.le
      nlinarith
    _ = Real.exp (-m * bennettFunction (t / m)) := by
      rw [← Real.exp_add]
      congr 1
      exact bennett_chernoff_exponent hm' ht.le

/-- **Bennett's inequality**, Proposition `prop:bennett` in the paper.
Indexing by `Fin n` is a relabelling of the source's indices `1,…,n`.
Both displayed tail estimates hold simultaneously with exactly the same mean
and deviation parameter. -/
theorem bennett_inequality {n : ℕ} {Y : Fin n → Ω → ℝ} {p : Fin n → unitInterval}
    (h_indep : iIndepFun Y μ)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    {t : ℝ} (hm : 0 < ∑ i, (p i : ℝ)) (ht : 0 < t) :
    μ.real {ω | (∑ i, (p i : ℝ)) + t < ∑ i, Y i ω} ≤
        Real.exp (-(∑ i, (p i : ℝ)) * bennettFunction (t / (∑ i, (p i : ℝ)))) ∧
      μ.real {ω | (∑ i, Y i ω) < (∑ i, (p i : ℝ)) - t} ≤
        Real.exp (-(∑ i, (p i : ℝ)) * bennettFunction (t / (∑ i, (p i : ℝ)))) := by
  constructor
  · simpa only [Finset.sum_apply] using bennett_upper_tail h_indep hY Finset.univ hm ht
  · simpa only [Finset.sum_apply] using bennett_lower_tail h_indep hY Finset.univ hm ht

/-- The absolute-deviation form used in the proof of Proposition `height=ok`.
Its application to the tree heights still requires their Bernoulli-sum law. -/
theorem bennett_abs_deviation {n : ℕ} {Y : Fin n → Ω → ℝ} {p : Fin n → unitInterval}
    (h_indep : iIndepFun Y μ)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    {t : ℝ} (hm : 0 < ∑ i, (p i : ℝ)) (ht : 0 < t) :
    μ.real {ω | t < |(∑ i, Y i ω) - (∑ i, (p i : ℝ))|} ≤
      2 * Real.exp (-(∑ i, (p i : ℝ)) * bennettFunction (t / (∑ i, (p i : ℝ)))) := by
  have htails := bennett_inequality h_indep hY hm ht
  have hsub : {ω | t < |(∑ i, Y i ω) - (∑ i, (p i : ℝ))|} ⊆
      {ω | (∑ i, (p i : ℝ)) + t < ∑ i, Y i ω} ∪
        {ω | (∑ i, Y i ω) < (∑ i, (p i : ℝ)) - t} := by
    intro ω hω
    change t < |(∑ i, Y i ω) - (∑ i, (p i : ℝ))| at hω
    by_cases h : 0 ≤ (∑ i, Y i ω) - (∑ i, (p i : ℝ))
    · left
      change (∑ i, (p i : ℝ)) + t < ∑ i, Y i ω
      rw [abs_of_nonneg h] at hω
      linarith
    · right
      change (∑ i, Y i ω) < (∑ i, (p i : ℝ)) - t
      rw [abs_of_neg (lt_of_not_ge h)] at hω
      linarith
  calc
    _ ≤ μ.real ({ω | (∑ i, (p i : ℝ)) + t < ∑ i, Y i ω} ∪
        {ω | (∑ i, Y i ω) < (∑ i, (p i : ℝ)) - t}) := measureReal_mono hsub
    _ ≤ μ.real {ω | (∑ i, (p i : ℝ)) + t < ∑ i, Y i ω} +
        μ.real {ω | (∑ i, Y i ω) < (∑ i, (p i : ℝ)) - t} := measureReal_union_le _ _
    _ ≤ _ := by linarith [htails.1, htails.2]

end Freezing2
