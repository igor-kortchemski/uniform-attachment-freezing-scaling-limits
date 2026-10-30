module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.BernoulliConcentration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite maximum-height tails from Bernoulli marginal laws

These helpers prove the reductions used in Proposition `prop:bounds` with the
correct union factor: the number of vertices, rather than the step number.
The hypotheses describe individual laws of truncated Bernoulli sums; they do
not assume an upper bound for the maximum. Their identification with the actual
random-tree heights remains a separate construction theorem.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {V Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'}

/-- The largest height in a nonempty finite vertex set. -/
noncomputable def finiteHeightMax (vertices : Finset V) (hne : vertices.Nonempty)
    (H : V → Ω → ℝ) (ω : Ω) : ℝ := vertices.sup' hne (fun v => H v ω)

/-- A union bound over the actual finite family, without an independence
assumption on its members. -/
theorem finiteHeightMax_upper_tail_le [IsFiniteMeasure μ]
    (vertices : Finset V) (hne : vertices.Nonempty) (H : V → Ω → ℝ)
    {a B : ℝ} (hbound : ∀ v ∈ vertices, μ.real {ω | a < H v ω} ≤ B) :
    μ.real {ω | a < finiteHeightMax vertices hne H ω} ≤ (vertices.card : ℝ) * B := by
  have hevent : {ω | a < finiteHeightMax vertices hne H ω} =
      ⋃ v ∈ vertices, {ω | a < H v ω} := by
    ext ω
    simp [finiteHeightMax, Finset.lt_sup'_iff]
  rw [hevent]
  calc
    μ.real (⋃ v ∈ vertices, {ω | a < H v ω}) ≤
        ∑ v ∈ vertices, μ.real {ω | a < H v ω} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ vertices, B := Finset.sum_le_sum hbound
    _ = (vertices.card : ℝ) * B := by simp

/-- For a lower tail, any one vertex is a lower bound for the maximum. -/
theorem finiteHeightMax_lower_tail_le [IsFiniteMeasure μ]
    (vertices : Finset V) (hne : vertices.Nonempty) (H : V → Ω → ℝ)
    {v : V} (hv : v ∈ vertices) (a : ℝ) :
    μ.real {ω | finiteHeightMax vertices hne H ω < a} ≤ μ.real {ω | H v ω < a} := by
  apply measureReal_mono _ (measure_ne_top μ _)
  intro ω hω
  exact (Finset.le_sup' (fun v => H v ω) hv).trans_lt hω

/-- Bernoulli random variables are nonnegative almost surely. -/
theorem bernoulli_ae_nonneg {Y : Ω' → ℝ} {p : unitInterval}
    (hLaw : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) ν) :
    ∀ᵐ ω ∂ν, 0 ≤ Y ω := by
  apply (hLaw.ae_iff (measurableSet_setOfPred.mp measurableSet_Ici)).mpr
  rw [ae_iff]
  simpa only [not_le, Set.Iio_def] using
    bernoulliMeasure_apply_of_notMem_of_notMem (x := (1 : ℝ)) (y := 0)
      p (s := Iio 0) measurableSet_Iio (by norm_num) (by simp)

/-- Truncating a family of Bernoulli summands gives almost-sure domination by
the full sum, on the same reference probability space. -/
theorem bernoulli_subset_sum_le_ae
    {Y : ι → Ω' → ℝ} {p : ι → unitInterval}
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) ν)
    {s t : Finset ι} (hts : t ⊆ s) :
    ∀ᵐ ω ∂ν, (∑ i ∈ t, Y i ω) ≤ ∑ i ∈ s, Y i ω := by
  have hnonneg : ∀ᵐ ω ∂ν, ∀ i ∈ s, 0 ≤ Y i ω := by
    exact (Filter.eventually_all_finset s).mpr (fun i _ => bernoulli_ae_nonneg (hLaw i))
  filter_upwards [hnonneg] with ω hω
  exact Finset.sum_le_sum_of_subset_of_nonneg hts (fun i hi _ => hω i hi)

/-- An individual truncated-height law obeys the full-sum upper tail. The
tree and Bernoulli reference spaces need not coincide. -/
theorem height_upper_tail_of_identDistrib_bernoulli [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {H : Ω → ℝ} {Y : ι → Ω' → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y ν)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) ν)
    {s u : Finset ι} (hus : u ⊆ s)
    (hIdent : IdentDistrib H (fun ω => ∑ i ∈ u, Y i ω) μ ν)
    (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ s, (p i : ℝ)) + t < H ω} ≤
      Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  have hlaw := congrArg ENNReal.toReal (hIdent.measure_mem_eq
    (s := Ioi ((∑ i ∈ s, (p i : ℝ)) + t)) measurableSet_Ioi)
  change μ.real {ω | (∑ i ∈ s, (p i : ℝ)) + t < H ω} =
    ν.real {ω | (∑ i ∈ s, (p i : ℝ)) + t < ∑ i ∈ u, Y i ω} at hlaw
  rw [hlaw]
  refine le_trans ?_ (bernoulli_sum_upper_tail hY hindep hLaw s hm ht)
  apply ENNReal.toReal_mono (measure_ne_top ν _)
  apply measure_mono_ae
  filter_upwards [bernoulli_subset_sum_le_ae hLaw hus] with ω hω
  exact fun ht => ht.trans_le hω

/-- Corrected upper maximum-height estimate: the union factor is the number
of vertices. No independence between vertex heights is required. -/
theorem finiteHeightMax_bernoulli_upper_tail [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (vertices : Finset V) (hne : vertices.Nonempty)
    {H : V → Ω → ℝ} {Y : ι → Ω' → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y ν)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) ν)
    {s : Finset ι} (u : V → Finset ι) (hus : ∀ v ∈ vertices, u v ⊆ s)
    (hIdent : ∀ v ∈ vertices, IdentDistrib (H v) (fun ω => ∑ i ∈ u v, Y i ω) μ ν)
    (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ s, (p i : ℝ)) + t < finiteHeightMax vertices hne H ω} ≤
      (vertices.card : ℝ) *
        Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  apply finiteHeightMax_upper_tail_le
  intro v hv
  exact height_upper_tail_of_identDistrib_bernoulli hY hindep hLaw (hus v hv)
    (hIdent v hv) hm ht

/-- The active-vertex lower-tail reduction, assuming its full Bernoulli-sum law. -/
theorem finiteHeightMax_bernoulli_lower_tail [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (vertices : Finset V) (hne : vertices.Nonempty)
    {H : V → Ω → ℝ} {Y : ι → Ω' → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y ν)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) ν)
    (s : Finset ι) {v : V} (hv : v ∈ vertices)
    (hIdent : IdentDistrib (H v) (fun ω => ∑ i ∈ s, Y i ω) μ ν)
    (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | finiteHeightMax vertices hne H ω < (∑ i ∈ s, (p i : ℝ)) - t} ≤
      Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  refine (finiteHeightMax_lower_tail_le vertices hne H hv _).trans ?_
  have hlaw := congrArg ENNReal.toReal (hIdent.measure_mem_eq
    (s := Iio ((∑ i ∈ s, (p i : ℝ)) - t)) measurableSet_Iio)
  change μ.real {ω | H v ω < (∑ i ∈ s, (p i : ℝ)) - t} =
    ν.real {ω | (∑ i ∈ s, Y i ω) < (∑ i ∈ s, (p i : ℝ)) - t} at hlaw
  rw [hlaw]
  exact bernoulli_sum_lower_tail hY hindep hLaw s hm ht

/-- The union factor `n + 1` still tends to zero against any exponential rate
strictly larger than one, under the paper's logarithmic scale lower bound. -/
theorem tendsto_nat_succ_mul_exp_neg_of_log_lower {h : ℕ → ℝ}
    (hlower : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) / 4) ≤ h n)
    {a : ℝ} (ha : 1 < a) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-a * h n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => Real.exp ((1 - a) * Real.log (n : ℝ)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hfn : (fun n : ℕ => (1 - a) * Real.log (n : ℝ)) =
        fun n : ℕ => -(Real.log (n : ℝ) * (a - 1)) := by funext n; ring
    rw [hfn]
    exact tendsto_neg_atTop_atBot.comp (hlog.atTop_mul_const (sub_pos.mpr ha))
  have hboundlim := he.const_mul (2 * Real.exp (a * Real.log 4))
  simp only [mul_zero] at hboundlim
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hboundlim
  filter_upwards [hlower, eventually_ge_atTop 1] with n hn hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  rw [Real.log_div hnpos.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hn
  have hexp : -a * h n ≤ -a * (Real.log (n : ℝ) - Real.log 4) := by nlinarith
  calc
    ((n : ℝ) + 1) * Real.exp (-a * h n) ≤
        (2 * (n : ℝ)) * Real.exp (-a * (Real.log (n : ℝ) - Real.log 4)) := by
      apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr hexp) (by positivity)
      positivity
    _ = 2 * (Real.exp (Real.log (n : ℝ)) *
        Real.exp (-a * (Real.log (n : ℝ) - Real.log 4))) := by
      rw [Real.exp_log hnpos]
      ring
    _ = 2 * Real.exp (Real.log (n : ℝ) +
        -a * (Real.log (n : ℝ) - Real.log 4)) := by rw [Real.exp_add]
    _ = (2 * Real.exp (a * Real.log 4)) *
        Real.exp ((1 - a) * Real.log (n : ℝ)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The logarithmic lower bound also gives divergence of the scale itself. -/
theorem tendsto_atTop_of_log_quarter_lower {h : ℕ → ℝ}
    (hlower : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) / 4) ≤ h n) :
    Tendsto h atTop atTop := by
  apply tendsto_atTop_mono' atTop hlower
  exact Real.tendsto_log_atTop.comp
    (Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 4) tendsto_natCast_atTop_atTop)

/-- A fixed one-edge shift in a vertex-height bound does not affect the
universal `e + ε` upper window. The half-margin absorbs `1 / h_n`. -/
theorem tendsto_shifted_bennett_upper_bound {h : ℕ → ℝ}
    (hlower : ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) / 4) ≤ h n)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      Real.exp (-h n * bennettRate (Real.exp 1 - 1 + ε - 1 / h n)))
      atTop (𝓝 0) := by
  have hdiv := tendsto_atTop_of_log_quarter_lower hlower
  have ha := one_lt_bennettRate_exp_one_sub_one_add (half_pos hε)
  have hboundlim := tendsto_nat_succ_mul_exp_neg_of_log_lower hlower ha
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hboundlim
  filter_upwards [hdiv.eventually_gt_atTop 0, hdiv.eventually_ge_atTop (2 / ε)] with n hn hnε
  have hsmall : 1 / h n ≤ ε / 2 := by
    apply (div_le_iff₀ hn).mpr
    have hm := (div_le_iff₀ hε).mp hnε
    nlinarith
  have hx : 0 ≤ Real.exp 1 - 1 + ε / 2 := by
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    linarith
  have hxy : Real.exp 1 - 1 + ε / 2 ≤ Real.exp 1 - 1 + ε - 1 / h n := by linarith
  have hg := strictMonoOn_bennettRate.monotoneOn hx (hx.trans hxy) hxy
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

end Freezing1
