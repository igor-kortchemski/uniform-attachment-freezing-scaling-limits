module

public import Freezing2.Analysis.ProfilePrimitive
public import Freezing2.Analysis.SourceHypotheses
public import Freezing2.Probability.BirthTimeLimit
public import Freezing2.Probability.VertexSampling
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Laws of the normalized harmonic branch lengths

Actual uniform vertex labels retain frozen births at `i-1` and active births at
`n`. Their harmonic prefixes approximate a continuous reciprocal primitive
uniformly. The resulting weak limit is derived from the actual birth-time law;
finite product laws retain independent sampling and possible repeated labels.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal Classical BoundedContinuousFunction

namespace Freezing2

/-- A uniform almost-everywhere perturbation preserves weak convergence, even
when the underlying probability spaces vary with the index. -/
theorem tendsto_probabilityMap_of_uniform_ae_error
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    {F G : (n : ℕ) → Ω n → ℝ} {ν : ProbabilityMeasure ℝ} {e : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ᵐ ω ∂(μ n : Measure (Ω n)), |F n ω - G n ω| ≤ e n)
    (hlim : Tendsto (fun n ↦ (μ n).map (G n)) atTop (𝓝 ν)) :
    Tendsto (fun n ↦ (μ n).map (F n)) atTop (𝓝 ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hbounded hlipschitz
  obtain ⟨L, hL⟩ := hlipschitz
  let Φ : ℝ →ᵇ ℝ :=
    { toFun := φ, continuous_toFun := hL.continuous, map_bounded' := hbounded }
  have hIntF (n : ℕ) : Integrable (fun ω ↦ φ (F n ω)) (μ n : Measure (Ω n)) :=
    (Φ.integrable ((μ n : Measure (Ω n)).map (F n))).comp_measurable (hF n)
  have hIntG (n : ℕ) : Integrable (fun ω ↦ φ (G n ω)) (μ n : Measure (Ω n)) :=
    (Φ.integrable ((μ n : Measure (Ω n)).map (G n))).comp_measurable (hG n)
  have hb : ∀ᶠ n in atTop,
      |(∫ t, φ t ∂((μ n).map (F n))) - ∫ t, φ t ∂((μ n).map (G n))| ≤ (L : ℝ) * e n := by
    filter_upwards [hbound] with n hn
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      integral_map (hF n).aemeasurable hL.continuous.aestronglyMeasurable,
      integral_map (hG n).aemeasurable hL.continuous.aestronglyMeasurable,
      ← integral_sub (hIntF n) (hIntG n), ← Real.norm_eq_abs]
    have hnorm : ∀ᵐ ω ∂(μ n : Measure (Ω n)), ‖φ (F n ω) - φ (G n ω)‖ ≤ (L : ℝ) * e n := by
      filter_upwards [hn] with ω hω
      have h := (hL.dist_le_mul (F n ω) (G n ω)).trans
        (mul_le_mul_of_nonneg_left hω L.coe_nonneg)
      simpa only [Real.dist_eq, Real.norm_eq_abs] using h
    simpa using norm_integral_le_of_norm_le_const hnorm
  have hdabs : Tendsto (fun n ↦ |(∫ t, φ t ∂((μ n).map (F n))) -
      ∫ t, φ t ∂((μ n).map (G n))|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hb
      (by simpa using he.const_mul (L : ℝ))
  have hd := (tendsto_zero_iff_abs_tendsto_zero _).mpr hdabs
  have hg := tendsto_iff_forall_lipschitz_integral_tendsto.mp hlim φ hbounded ⟨L, hL⟩
  convert hd.add hg using 1 <;> simp

/-- Lebesgue probability on the unit interval. -/
noncomputable def profileProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨profileMeasure, ⟨by simp [profileMeasure, Real.volume_Icc]⟩⟩

/-- Actual uniform sampling on the paper's finite label set. -/
noncomputable def uniformLabelProbability (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) : ProbabilityMeasure VertexLabel :=
  ⟨uniformVertex x n, uniformVertex_isProbabilityMeasure x hx hs⟩

/-- The actual normalized-birth distribution, now as a probability measure. -/
noncomputable def uniformBirthProbability (x : ℕ → ℤ) (n : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) : ProbabilityMeasure ℝ :=
  (uniformLabelProbability x n hx hs).map (fun v ↦ (birthTime n v : ℝ) / n)

theorem tendsto_uniformBirthProbability {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ uniformBirthProbability (x n) n (hx n).1 ((hx n).2 n le_rfl).le)
      atTop (𝓝 profileProbabilityMeasure) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  exact tendsto_uniformBirthTimeMeasure hx hα hL1 hpos

/-- The normalized half-harmonic branch ending at the actual source birth time. -/
noncomputable def normalizedBranchLength (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    (v : VertexLabel) : ℝ :=
  normalizedHarmonicPrefix x α n (birthTime n v)

/-- Exact agreement with the displayed sum of `1/(2*S_i)`. -/
theorem normalizedBranchLength_eq_sum (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ) (v : VertexLabel) :
    normalizedBranchLength x α n v = (n : ℝ) ^ (α - 1) *
      ∑ i ∈ Finset.range (birthTime n v), 1 / (2 * (activeCount (x n) (i + 1) : ℝ)) := by
  have hsum : (∑ i ∈ Finset.range (birthTime n v),
      1 / (2 * (activeCount (x n) (i + 1) : ℝ))) =
      (∑ i ∈ Finset.range (birthTime n v), (activeCount (x n) (i + 1) : ℝ)⁻¹) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_inv_rev, div_eq_mul_inv, one_mul]
  rw [hsum]
  simp only [normalizedBranchLength, normalizedHarmonicPrefix, harmonicInterval, zero_add]
  ring

/-- The genuine branch law under a uniform choice of a vertex label. -/
noncomputable def uniformBranchLengthLaw (x : ℕ → ℕ → ℤ) (α : ℝ) (n : ℕ)
    (hx : IsSigned (x n)) (hs : 0 ≤ activeCount (x n) n) : ProbabilityMeasure ℝ :=
  (uniformLabelProbability (x n) n hx hs).map (normalizedBranchLength x α n)

/-- Main-result dependency: actual normalized branch lengths converge weakly
to the reciprocal primitive at a uniform time. Local square moments are not needed. -/
theorem tendsto_uniformBranchLengthLaw {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) :
    Tendsto (fun n ↦ uniformBranchLengthLaw x α n (hx n).1 ((hx n).2 n le_rfl).le)
      atTop (𝓝 (profileProbabilityMeasure.map (profilePrimitive g))) := by
  let μ (n : ℕ) := uniformLabelProbability (x n) n (hx n).1 ((hx n).2 n le_rfl).le
  have hp := continuous_profilePrimitive hL1.1
  have hm (n : ℕ) :
      (uniformBirthProbability (x n) n (hx n).1 ((hx n).2 n le_rfl).le).map (profilePrimitive g) =
        (μ n).map (fun v ↦ profilePrimitive g ((birthTime n v : ℝ) / n)) := by
    apply Subtype.ext
    change ((uniformVertex (x n) n).map (fun v ↦ (birthTime n v : ℝ) / n)).map
      (profilePrimitive g) = (uniformVertex (x n) n).map
        (fun v ↦ profilePrimitive g ((birthTime n v : ℝ) / n))
    rw [Measure.map_map hp.measurable (measurable_of_countable _)]
    rfl
  have hG := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_uniformBirthProbability hx hα hL1 hpos) hp
  have hG' : Tendsto (fun n ↦ (μ n).map
      (fun v ↦ profilePrimitive g ((birthTime n v : ℝ) / n))) atTop
        (𝓝 (profileProbabilityMeasure.map (profilePrimitive g))) :=
    hG.congr' (Eventually.of_forall hm)
  apply tendsto_probabilityMap_of_uniform_ae_error μ
    (fun _ ↦ measurable_of_countable _) (fun _ ↦ measurable_of_countable _)
    (tendsto_branchPrimitiveError hα hL1) ?_ hG'
  filter_upwards [eventually_gt_atTop 0] with n hn
  filter_upwards [uniformVertex_mem (x n) (hx n).1 ((hx n).2 n le_rfl).le] with v hv
  exact normalizedHarmonicPrefix_error_le hx hL1.1 hn (birthTime_le (x n) hv)

/-- Independent uniform labels on the actual finite vertex set. Repeated labels
remain possible and are not removed from this sampling law. -/
noncomputable def iidUniformLabelProbability (x : ℕ → ℤ) (n k : ℕ) (hx : IsSigned x)
    (hs : 0 ≤ activeCount x n) : ProbabilityMeasure (Fin k → VertexLabel) :=
  ProbabilityMeasure.pi (fun _ ↦ uniformLabelProbability x n hx hs)

/-- The actual vector of normalized branch lengths for `k` independent labels. -/
noncomputable def uniformBranchVectorLaw (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : 0 ≤ activeCount (x n) n) : ProbabilityMeasure (Fin k → ℝ) :=
  (iidUniformLabelProbability (x n) n k hx hs).map
    (fun v i ↦ normalizedBranchLength x α n (v i))

/-- Coordinatewise mapping of independent labels gives independent branch laws. -/
theorem uniformBranchVectorLaw_eq_pi (x : ℕ → ℕ → ℤ) (α : ℝ) (n k : ℕ)
    (hx : IsSigned (x n)) (hs : 0 ≤ activeCount (x n) n) :
    uniformBranchVectorLaw x α n k hx hs =
      ProbabilityMeasure.pi (fun _ : Fin k ↦ uniformBranchLengthLaw x α n hx hs) := by
  let := uniformVertex_isProbabilityMeasure (x n) hx hs
  apply Subtype.ext
  change (Measure.pi (fun _ : Fin k ↦ uniformVertex (x n) n)).map
      (fun v i ↦ normalizedBranchLength x α n (v i)) =
    Measure.pi (fun _ : Fin k ↦ (uniformVertex (x n) n).map (normalizedBranchLength x α n))
  exact Measure.pi_map_pi (fun _ ↦ (measurable_of_countable _).aemeasurable)

/-- The limiting vector is the primitive evaluated at independent uniform times. -/
noncomputable def iidPrimitiveLaw (g : ℝ → ℝ) (k : ℕ) : ProbabilityMeasure (Fin k → ℝ) :=
  (ProbabilityMeasure.pi (fun _ : Fin k ↦ profileProbabilityMeasure)).map
    (fun u i ↦ profilePrimitive g (u i))

theorem iidPrimitiveLaw_eq_pi {g : ℝ → ℝ} (hg : Integrable g profileMeasure) (k : ℕ) :
    iidPrimitiveLaw g k =
      ProbabilityMeasure.pi (fun _ : Fin k ↦ profileProbabilityMeasure.map (profilePrimitive g)) := by
  apply Subtype.ext
  change (Measure.pi (fun _ : Fin k ↦ profileMeasure)).map (fun u i ↦ profilePrimitive g (u i)) =
    Measure.pi (fun _ : Fin k ↦ profileMeasure.map (profilePrimitive g))
  exact Measure.pi_map_pi (fun _ ↦ (continuous_profilePrimitive hg).measurable.aemeasurable)

/-- Fixed finite-dimensional convergence for the actual iid branch vector. -/
theorem tendsto_uniformBranchVectorLaw {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g) (k : ℕ) :
    Tendsto (fun n ↦ uniformBranchVectorLaw x α n k (hx n).1 ((hx n).2 n le_rfl).le)
      atTop (𝓝 (iidPrimitiveLaw g k)) := by
  simp only [uniformBranchVectorLaw_eq_pi, iidPrimitiveLaw_eq_pi hL1.1]
  exact ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr fun _ : Fin k ↦ tendsto_uniformBranchLengthLaw hx hα hL1 hpos)

/-- The limiting branch length in the manuscript's notation. Only its values on
the unit interval are sampled. -/
noncomputable def sourceBranchPrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Icc (0 : ℝ) t, 1 / (2 * f s)

theorem profilePrimitive_reciprocal_eq (f : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    profilePrimitive (fun s ↦ 1 / f s) t = sourceBranchPrimitive f t := by
  rw [profilePrimitive_eq_setIntegral _ ht0 ht1, sourceBranchPrimitive, ← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ fun s ↦ by
    change 1 / f s / 2 = 1 / (2 * f s)
    rw [div_div, mul_comm (f s) 2]

theorem profilePrimitive_reciprocal_map_eq (f : ℝ → ℝ) :
    profileProbabilityMeasure.map (profilePrimitive (fun s ↦ 1 / f s)) =
      profileProbabilityMeasure.map (sourceBranchPrimitive f) := by
  apply Subtype.ext
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact profilePrimitive_reciprocal_eq f ht.1 ht.2

/-- Independent copies of the source branch integral at uniform times. -/
noncomputable def iidSourceBranchLimit (f : ℝ → ℝ) (k : ℕ) :
    ProbabilityMeasure (Fin k → ℝ) :=
  ProbabilityMeasure.pi (fun _ : Fin k ↦ profileProbabilityMeasure.map (sourceBranchPrimitive f))

theorem iidPrimitiveLaw_reciprocal_eq {f : ℝ → ℝ}
    (hf : Integrable (fun s ↦ 1 / f s) profileMeasure) (k : ℕ) :
    iidPrimitiveLaw (fun s ↦ 1 / f s) k = iidSourceBranchLimit f k := by
  rw [iidPrimitiveLaw_eq_pi hf]
  simp only [iidSourceBranchLimit, profilePrimitive_reciprocal_map_eq]

/-- Source-facing marginal convergence uses only the positive horizons of the
manuscript; the shifted sequence is exactly those horizons. -/
theorem tendsto_uniformBranchLengthLaw_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα : α < 1) (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t)) :
    Tendsto (fun n ↦ uniformBranchLengthLaw x α (n + 1)
      (hx (n + 1) (Nat.zero_lt_succ n)).1
      ((hx (n + 1) (Nat.zero_lt_succ n)).2 (n + 1) le_rfl).le)
      atTop (𝓝 (profileProbabilityMeasure.map (sourceBranchPrimitive f))) := by
  have h := (tendsto_uniformBranchLengthLaw (admissible_initialRowExtension hx) hα
    (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)).comp
      (tendsto_add_atTop_nat 1)
  rw [profilePrimitive_reciprocal_map_eq] at h
  apply h.congr'
  exact Eventually.of_forall fun n ↦ by
    apply Subtype.ext
    change (uniformVertex (initialRowExtension x (n + 1)) (n + 1)).map
        (normalizedBranchLength (initialRowExtension x) α (n + 1)) =
      (uniformVertex (x (n + 1)) (n + 1)).map (normalizedBranchLength x α (n + 1))
    have hfun : normalizedBranchLength (initialRowExtension x) α (n + 1) =
        normalizedBranchLength x α (n + 1) := by
      funext v
      simp [normalizedBranchLength, normalizedHarmonicPrefix, initialRowExtension]
    rw [hfun]
    simp [initialRowExtension]

/-- The fixed-dimensional source branch vector consists of independent copies
of the displayed branch integral, with no conditioning on distinct labels. -/
theorem tendsto_uniformBranchVectorLaw_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα : α < 1) (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t)) (k : ℕ) :
    Tendsto (fun n ↦ uniformBranchVectorLaw x α (n + 1) k
      (hx (n + 1) (Nat.zero_lt_succ n)).1
      ((hx (n + 1) (Nat.zero_lt_succ n)).2 (n + 1) le_rfl).le)
      atTop (𝓝 (iidSourceBranchLimit f k)) := by
  simp only [uniformBranchVectorLaw_eq_pi, iidSourceBranchLimit]
  exact ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr fun _ : Fin k ↦
      tendsto_uniformBranchLengthLaw_positive_horizons hx hα hf hL1)

end Freezing2
