module

public import Freezing2.Probability.UniformHeightConcentration

/-!
# Recentring height concentration at the source's inclusive harmonic sum

The Bernoulli mean sums over `(a,b]`, while the distance surrogate uses `[a,b]`.
The missing left endpoint contributes at most `1/2`, uniformly also when
`a = 0`, `a = b`, or `a = b = 0`. This makes the final centring step in
Proposition `height=ok` explicit. The probabilistic conclusion remains
conditional on the actual height marginal laws.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ProbabilityTheory

namespace Freezing2

/-- The paper's inclusive harmonic sum `h_n(a,b)`, including time zero. -/
noncomputable def inclusiveHarmonic (x : ℕ → ℤ) (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc a b, (activeCount x i : ℝ)⁻¹

/-- Conversion of the discrete half-open interval to the offset encoding. -/
theorem sum_Ioc_eq_sum_range_offset (f : ℕ → ℝ) (a b : ℕ) :
    ∑ i ∈ Finset.Ioc a b, f i = ∑ i ∈ Finset.range (b - a), f (a + i + 1) := by
  have hset : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_add_right]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- Exact endpoint accounting, valid for singleton and time-zero intervals. -/
theorem inclusiveHarmonic_eq (x : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    inclusiveHarmonic x a b = (activeCount x a : ℝ)⁻¹ +
      harmonicInterval x a (b - a) := by
  unfold inclusiveHarmonic harmonicInterval
  rw [Finset.Icc_eq_cons_Ioc hab, Finset.sum_cons, sum_Ioc_eq_sum_range_offset]

/-- Every interval's Bernoulli mean is bounded by the complete up-step sum. -/
theorem harmonicUpInterval_le_total {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    {n a b : ℕ} (_hab : a ≤ b) (hbn : b ≤ n) :
    harmonicUpInterval (x n) a (b - a) ≤ harmonicUpTotal x n := by
  have he (a b : ℕ) : harmonicUpInterval (x n) a (b - a) =
      ∑ i ∈ Finset.Ioc a b,
        if x n i = 1 then (activeCount (x n) i : ℝ)⁻¹ else 0 := by
    simpa only [harmonicUpInterval] using
      (sum_Ioc_eq_sum_range_offset
        (fun i ↦ if x n i = 1 then (activeCount (x n) i : ℝ)⁻¹ else 0) a b).symm
  rw [he]
  have he0 : harmonicUpTotal x n = harmonicUpInterval (x n) 0 (n - 0) := by
    simp only [harmonicUpTotal, Nat.sub_zero]
  rw [he0, he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hi' := Finset.mem_Ioc.mp hi
    exact Finset.mem_Ioc.mpr ⟨by omega, hi'.2.trans hbn⟩
  · intro i hi _
    split_ifs
    · exact inv_nonneg.mpr (activeCount_real_pos hx n (Finset.mem_Ioc.mp hi).2).le
    · exact le_rfl

/-- The source's inclusive centre differs from the Bernoulli mean by the
harmonic balance error and at most one half of a unit endpoint. -/
theorem harmonic_height_center_error_bound {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) {n a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    |harmonicUpInterval (x n) a (b - a) - inclusiveHarmonic (x n) a b / 2| ≤
      reciprocalErrorTotal x n / 2 + (1 + Real.log (n + 1)) + 1 / 2 := by
  have hbal := harmonicInterval_deviation_bound hx (show a + (b - a) ≤ n by omega)
  have hS : (1 : ℝ) ≤ (activeCount (x n) a : ℝ) := by
    have hInt : (1 : ℤ) ≤ activeCount (x n) a := by
      have := (hx n).2 a (hab.trans hbn)
      omega
    exact_mod_cast hInt
  have hinv0 : 0 ≤ (activeCount (x n) a : ℝ)⁻¹ := by positivity
  have hinv1 : (activeCount (x n) a : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num) hS
  rw [inclusiveHarmonic_eq _ hab]
  calc
    _ = |(harmonicUpInterval (x n) a (b - a) - harmonicInterval (x n) a (b - a) / 2) -
        (activeCount (x n) a : ℝ)⁻¹ / 2| := by congr 1; ring
    _ ≤ |harmonicUpInterval (x n) a (b - a) - harmonicInterval (x n) a (b - a) / 2| +
        |(activeCount (x n) a : ℝ)⁻¹ / 2| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (div_nonneg hinv0 (by norm_num))]
      linarith

/-- The uniform centring error vanishes at the original height scale. -/
theorem tendsto_harmonic_height_center_error_bound
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦
      (reciprocalErrorTotal x n / 2 + (1 + Real.log (n + 1)) + 1 / 2) /
        (n : ℝ) ^ (1 - α)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α / n) atTop (𝓝 0) := by
    simpa using tendsto_profile_spike_bound hα1 (by norm_num : (0 : ℝ) < 2)
  have h := (tendsto_harmonicDeviation_bound hx hα0 hα1 hL1 hg).add (hc.mul_const (1 / 2))
  simp only [zero_mul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one,
    div_div_eq_mul_div]
  ring

/-- Uniformity includes all `0 ≤ a ≤ b ≤ n`, not just nonempty positive-time
height ranges. -/
theorem eventually_uniform_harmonic_height_center_error
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : ℕ, a ≤ b → b ≤ n →
      |harmonicUpInterval (x n) a (b - a) - inclusiveHarmonic (x n) a b / 2| <
        ε * (n : ℝ) ^ (1 - α) := by
  filter_upwards [(tendsto_harmonic_height_center_error_bound hx hα0 hα1 hL1 hg).eventually_lt_const hε,
    eventually_gt_atTop 0] with n hn hn0
  intro a b hab hbn
  exact (harmonic_height_center_error_bound hx hab hbn).trans_lt
    ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hn0) _)).mp hn)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform concentration is preserved under a uniformly negligible change
of deterministic centres; no relation between different random variables is
required. -/
theorem tendsto_finiteHeightDeviationMax_recenter
    {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (Z : (n : ℕ) → κ n → Ω → ℝ) (m c : (n : ℕ) → κ n → ℝ) (s : ℕ → ℝ)
    (hs : ∀ᶠ n : ℕ in atTop, 0 < s n)
    (hconc : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ ↦ (μ n).real {ω | ε * s n < finiteHeightDeviationMax (Z n) (m n) ω})
      atTop (𝓝 0))
    (hcenter : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ j : κ n, |m n j - c n j| ≤ ε * s n)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (μ n).real
      {ω | ε * s n < finiteHeightDeviationMax (Z n) (c n) ω}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) ?_
    (hconc (ε / 2) (by positivity))
  filter_upwards [hs, hcenter (ε / 2) (by positivity)] with n hsn hcn
  apply measureReal_mono ?_ (measure_ne_top (μ n) _)
  intro ω hω
  obtain ⟨j, hj⟩ := (lt_finiteHeightDeviationMax_iff _ _ _ (by positivity)).mp hω
  apply (lt_finiteHeightDeviationMax_iff _ _ _ (by positivity)).mpr
  refine ⟨j, ?_⟩
  by_contra! hnot
  have htri : |Z n j ω - c n j| ≤ |Z n j ω - m n j| + |m n j - c n j| :=
    abs_sub_le _ _ _
  have := hcn j
  nlinarith

/-- The last centring step of Proposition `height=ok`, conditional on verified
Bernoulli-sum laws for the actual heights. The source centre is the inclusive
sum `[a,b]`, while the prescribed Bernoulli mean is the up-step sum `(a,b]`.
All endpoint cases are retained. -/
theorem tendsto_uniform_height_inclusive_harmonic_deviation
    {Ω' : Type*} [MeasurableSpace Ω']
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : (n : ℕ) → κ n → Measure Ω') [∀ n j, IsProbabilityMeasure (ν n j)]
    (a b : (n : ℕ) → κ n → ℕ)
    (d : (n : ℕ) → κ n → ℕ) (Z : (n : ℕ) → κ n → Ω → ℝ)
    (Y : (n : ℕ) → (j : κ n) → Fin (d n j) → Ω' → ℝ)
    (p : (n : ℕ) → (j : κ n) → Fin (d n j) → unitInterval)
    (hab : ∀ n j, a n j ≤ b n j) (hbn : ∀ n j, b n j ≤ n)
    (hLaw : ∀ n j, IdentDistrib (Z n j) (fun ω ↦ ∑ i, Y n j i ω) (μ n) (ν n j))
    (hInd : ∀ n j, iIndepFun (Y n j) (ν n j))
    (hY : ∀ n j i, HasLaw (Y n j i) (bernoulliMeasure (1 : ℝ) 0 (p n j i)) (ν n j))
    (hmean : ∀ n j, ∑ i, (p n j i : ℝ) =
      harmonicUpInterval (x n) (a n j) (b n j - a n j))
    (hcard : ∀ n, Fintype.card (κ n) ≤ (n + 1) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (μ n).real {ω |
      ε * (n : ℝ) ^ (1 - α) < finiteHeightDeviationMax (Z n)
        (fun j ↦ inclusiveHarmonic (x n) (a n j) (b n j) / 2) ω})
      atTop (𝓝 0) := by
  apply tendsto_finiteHeightDeviationMax_recenter μ Z
    (fun n j ↦ ∑ i, (p n j i : ℝ))
    (fun n j ↦ inclusiveHarmonic (x n) (a n j) (b n j) / 2)
    (fun n ↦ (n : ℝ) ^ (1 - α)) ?_ ?_ ?_ hε
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  · intro η hη
    apply tendsto_uniform_height_deviation_of_bernoulli_laws hx hα0 hα1 hL1 hpos
      μ ν d Z Y p hLaw hInd hY ?_ hcard hη
    intro n j
    rw [hmean]
    exact harmonicUpInterval_le_total hx (hab n j) (hbn n j)
  · intro η hη
    filter_upwards [eventually_uniform_harmonic_height_center_error hx hα0 hα1 hL1
      (hpos.mono fun _ ht ↦ ht.le) hη] with n hn
    intro j
    rw [hmean]
    exact (hn (a n j) (b n j) (hab n j) (hbn n j)).le

end Freezing2
