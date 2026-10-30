module

public import Freezing2.Analysis.FiniteSurvivalProducts
public import Freezing2.Probability.SupercriticalCoalescenceLaw

/-!
# Critical survival products on compact interior intervals

At exponent one half, the exact pairwise hazard sums converge to the integral
of the squared reciprocal profile. The interior population minimum tends to
infinity, so every individual hazard vanishes uniformly. The logarithmic
product theorem then gives the exponential survival factor used in the local
critical genealogy calculation. This does not construct that genealogy or
assume its joint density formula.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical BigOperators

namespace Freezing2

open ReverseCoalescence

/-- Moving closed-interval integrals are continuous when the endpoints remain
in one compact interval on which the integrand is integrable. -/
theorem tendsto_setIntegral_Icc_endpoints {f : ℝ → ℝ} {A B a b : ℝ}
    {u v : ℕ → ℝ} (hf : IntegrableOn f (Icc A B) volume)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (hwindow : ∀ᶠ n in atTop, A ≤ u n ∧ u n ≤ v n ∧ v n ≤ B) :
    Tendsto (fun n ↦ ∫ t in Icc (u n) (v n), f t) atTop
      (𝓝 (∫ t in Icc a b, f t)) := by
  have hua : a ∈ Icc A B := isClosed_Icc.mem_of_tendsto hu
    (hwindow.mono fun _ h ↦ ⟨h.1, h.2.1.trans h.2.2⟩)
  have hvb : b ∈ Icc A B := isClosed_Icc.mem_of_tendsto hv
    (hwindow.mono fun _ h ↦ ⟨h.1.trans h.2.1, h.2.2⟩)
  have hab : a ≤ b := le_of_tendsto_of_tendsto hu hv (hwindow.mono fun _ h ↦ h.2.1)
  have hcont := intervalIntegral.continuousOn_primitive_Icc hf
  have hpu := (hcont a hua).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu, hwindow.mono fun _ h ↦ ⟨h.1, h.2.1.trans h.2.2⟩⟩)
  have hpv := (hcont b hvb).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hv, hwindow.mono fun _ h ↦ ⟨h.1.trans h.2.1, h.2.2⟩⟩)
  have heq := setIntegral_Icc_sub_left hua.1 hab
    (hf.mono_set (fun _ ht ↦ ⟨ht.1, ht.2.trans hvb.2⟩))
  rw [← heq]
  apply (hpv.sub hpu).congr'
  filter_upwards [hwindow] with n hn
  exact setIntegral_Icc_sub_left hn.1 hn.2.1
    (hf.mono_set (fun _ ht ↦ ⟨ht.1, ht.2.trans hn.2.2⟩))

/-- Exact inclusive-interval sum of the actual merger hazards. -/
theorem sum_Icc_companion_coalescenceHazard (x : ℕ → ℤ) (hx : IsSigned x)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, coalescenceHazard (companionSchedule x) i) =
      2 * coalescenceUpSum x (a - 1) (b + 1 - a) := by
  have hend : a - 1 + (b + 1 - a) = b := by omega
  have hset : Finset.Ioc (a - 1) b = Finset.Icc a b := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simpa only [hend, hset] using
    sum_companion_coalescenceHazard x hx (a - 1) (b + 1 - a)

/-- At the critical exponent the cumulative actual pair hazard has exactly
the squared reciprocal-profile integral as limit, for any converging interior
integer endpoints. -/
theorem tendsto_critical_coalescence_hazard_sum
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g)
    {ε a b : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {u v : ℕ → ℕ} (hu : Tendsto (fun n ↦ (u n : ℝ) / n) atTop (𝓝 a))
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 b))
    (hwindow : ∀ᶠ n in atTop, CoalescenceInterval ε n (u n) (v n)) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.Icc (u n) (v n),
      coalescenceHazard (companionSchedule (x n)) i) atTop
      (𝓝 (∫ t in Icc a b, (g t) ^ 2)) := by
  have hg := (h2 ε (1 - ε) hε (by linarith) (by linarith)).1
  have hscaled : ∀ᶠ n in atTop,
      ε ≤ (u n : ℝ) / n ∧ (u n : ℝ) / n ≤ (v n : ℝ) / n ∧
        (v n : ℝ) / n ≤ 1 - ε := by
    filter_upwards [hwindow, eventually_gt_atTop 0] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    exact ⟨(le_div_iff₀ hnpos).mpr hn.2.2.2.1,
      div_le_div_of_nonneg_right (by exact_mod_cast hn.2.1) hnpos.le,
      (div_le_iff₀ hnpos).mpr hn.2.2.2.2⟩
  have hint := tendsto_setIntegral_Icc_endpoints hg hu hv hscaled
  have herr : Tendsto (fun n ↦ coalescenceIntervalError x (1 / 2) g n (u n) (v n))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hwindow,
      eventually_coalescenceIntervalError_lt hx (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε hη] with n hn he
    simpa only [Real.dist_eq, sub_zero, coalescenceIntervalError, abs_abs] using he (u n) (v n) hn
  have hdiff : Tendsto (fun n ↦ coalescenceUpSum (x n) (u n - 1) (v n + 1 - u n) -
      (∫ t in Icc ((u n : ℝ) / n) ((v n : ℝ) / n), (g t) ^ 2) / 2)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ herr
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [Real.norm_eq_abs, coalescenceIntervalError,
      show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one, div_self hn0, one_mul]
    exact le_rfl
  have hsum := (hdiff.add (hint.div_const 2)).const_mul 2
  have hlim : 2 * ((0 : ℝ) + (∫ t in Icc a b, (g t) ^ 2) / 2) =
      ∫ t in Icc a b, (g t) ^ 2 := by ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [hwindow] with n hn
  rw [sum_Icc_companion_coalescenceHazard (x n) (hx n).1 hn.1 hn.2.1]
  ring


/-- On an interior window, a lower population bound controls every concrete
pair hazard quadratically. -/
theorem companion_coalescenceHazard_le_four_inv_sq (x : ℕ → ℤ) (hx : IsSigned x)
    (i : ℕ) {M : ℝ} (hM : 2 ≤ M) (hmin : M ≤ (activeCount x i : ℝ)) :
    coalescenceHazard (companionSchedule x) i ≤ 4 * (M⁻¹) ^ 2 := by
  simp only [coalescenceHazard, companionSchedule, companion_activeCount x hx,
    decide_eq_true_eq]
  split_ifs
  · have hMp : 0 < M := by linarith
    have hS : (2 : ℝ) ≤ activeCount x i := hM.trans hmin
    have hsq : M ^ 2 ≤ (activeCount x i : ℝ) ^ 2 :=
      (sq_le_sq₀ hMp.le (by linarith)).mpr hmin
    have hden : M ^ 2 / 2 ≤ (activeCount x i : ℝ) * ((activeCount x i : ℝ) - 1) := by
      nlinarith
    calc
      _ ≤ 2 / (M ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by field_simp; ring
  · positivity

/-- Exact critical survival factor for any fixed nonnegative number of pairs.
Its maximal-hazard premise is derived from the source profile assumptions. -/
theorem tendsto_critical_survival_product
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g)
    {ε a b c : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hc : 0 ≤ c)
    {u v : ℕ → ℕ} (hu : Tendsto (fun n ↦ (u n : ℝ) / n) atTop (𝓝 a))
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 b))
    (hwindow : ∀ᶠ n in atTop, CoalescenceInterval ε n (u n) (v n)) :
    Tendsto (fun n ↦ ∏ i ∈ Finset.Icc (u n) (v n),
      (1 - c * coalescenceHazard (companionSchedule (x n)) i)) atTop
      (𝓝 (Real.exp (-c * ∫ t in Icc a b, (g t) ^ 2))) := by
  let M : ℕ → ℝ := fun n ↦ activeCount (x n) (interiorMinimizer x n ε (1 - ε))
  have hM : Tendsto M atTop atTop :=
    tendsto_interiorMinimum_atTop hx (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos h2 hε (by linarith) (by linarith)
  have hinv : Tendsto (fun n ↦ (M n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hM
  let δ : ℕ → ℝ := fun n ↦ c * (4 * ((M n)⁻¹) ^ 2)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using ((hinv.pow 2).const_mul 4).const_mul c
  have hbound : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (u n) (v n),
      0 ≤ c * coalescenceHazard (companionSchedule (x n)) i ∧
        c * coalescenceHazard (companionSchedule (x n)) i ≤ δ n := by
    filter_upwards [hwindow, hM.eventually (eventually_ge_atTop 2)] with n hn hMn
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨hui, hiv⟩
    rcases hn with ⟨hu1, huv, hvn, hlo, hhi⟩
    have hin : i ≤ n := hiv.trans hvn
    have himem : i ∈ interiorTimes n ε (1 - ε) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
      · exact hlo.trans (by exact_mod_cast hui)
      · exact le_trans (by exact_mod_cast hiv) hhi
    have hmin : M n ≤ (activeCount (x n) i : ℝ) := by
      dsimp only [M]
      exact_mod_cast interiorMinimizer_min x n ε (1 - ε) himem
    exact ⟨mul_nonneg hc (companion_coalescenceHazard_nonneg (x n) (hx n).1 (hx n).2 hin),
      mul_le_mul_of_nonneg_left
        (companion_coalescenceHazard_le_four_inv_sq (x n) (hx n).1 i hMn hmin) hc⟩
  have hsum := (tendsto_critical_coalescence_hazard_sum hx hL1 hpos h2
    hε hεhalf hu hv hwindow).const_mul c
  have hsum' : Tendsto (fun n ↦ ∑ i ∈ Finset.Icc (u n) (v n),
      c * coalescenceHazard (companionSchedule (x n)) i) atTop
      (𝓝 (c * ∫ t in Icc a b, (g t) ^ 2)) := by
    simpa only [Finset.mul_sum] using hsum
  simpa only [neg_mul] using tendsto_finite_survival_product hδ hbound hsum'

/-- The source binomial-hazard notation, with a fixed number `r` of clusters.
The product runs only over attachment times, exactly as in the paper. -/
theorem tendsto_critical_survival_choose
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g)
    {ε a b : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {u v : ℕ → ℕ} (hu : Tendsto (fun n ↦ (u n : ℝ) / n) atTop (𝓝 a))
    (hv : Tendsto (fun n ↦ (v n : ℝ) / n) atTop (𝓝 b))
    (hwindow : ∀ᶠ n in atTop, CoalescenceInterval ε n (u n) (v n)) (r : ℕ) :
    Tendsto (fun n ↦ ∏ i ∈ (Finset.Icc (u n) (v n)).filter (fun i ↦ x n i = 1),
      (1 - (r.choose 2 : ℝ) / ((activeCount (x n) i).toNat.choose 2 : ℝ))) atTop
      (𝓝 (Real.exp (-(r.choose 2 : ℝ) * ∫ t in Icc a b, (g t) ^ 2))) := by
  apply (tendsto_critical_survival_product hx hL1 hpos h2 hε hεhalf
    (Nat.cast_nonneg (r.choose 2)) hu hv hwindow).congr'
  filter_upwards [hwindow] with n hn
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  have hin : i ≤ n := (Finset.mem_Icc.mp hi).2.trans hn.2.2.1
  by_cases hup : x n i = 1
  · have hup' : companionSchedule (x n) i = true := by simp [companionSchedule, hup]
    rw [ite_eq_left hup, coalescenceHazard_eq_inv_choose
      (companion_before_extinction (x n) (hx n).1 (hx n).2).le hin hup',
      companion_activeCount (x n) (hx n).1]
    simp only [div_eq_mul_inv, one_mul]
  · simp [coalescenceHazard, companionSchedule, hup]


/-- A fixed finite collection of intervals and cluster counts gives the
piecewise-constant survival factor needed between successive genealogical events. -/
theorem tendsto_critical_survival_choose_finite {ι : Type*} (s : Finset ι)
    {x : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray x)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile x (1 / 2) g)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {a b : ι → ℝ} {u v : ι → ℕ → ℕ} (r : ι → ℕ)
    (hu : ∀ j ∈ s, Tendsto (fun n ↦ (u j n : ℝ) / n) atTop (𝓝 (a j)))
    (hv : ∀ j ∈ s, Tendsto (fun n ↦ (v j n : ℝ) / n) atTop (𝓝 (b j)))
    (hwindow : ∀ j ∈ s, ∀ᶠ n in atTop, CoalescenceInterval ε n (u j n) (v j n)) :
    Tendsto (fun n ↦ ∏ j ∈ s,
      ∏ i ∈ (Finset.Icc (u j n) (v j n)).filter (fun i ↦ x n i = 1),
        (1 - ((r j).choose 2 : ℝ) / ((activeCount (x n) i).toNat.choose 2 : ℝ))) atTop
      (𝓝 (Real.exp (-∑ j ∈ s, ((r j).choose 2 : ℝ) *
        ∫ t in Icc (a j) (b j), (g t) ^ 2))) := by
  have h := tendsto_finsetProd s (fun j hj ↦ tendsto_critical_survival_choose hx hL1 hpos h2
    hε hεhalf (hu j hj) (hv j hj) (hwindow j hj) (r j))
  simpa only [neg_mul, ← Real.exp_sum, ← Finset.sum_neg_distrib] using h

end Freezing2
