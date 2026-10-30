module

public import Freezing2.Analysis.FiniteFamilyScheffe

/-!
# Dominated convergence with an L¹-converging dominating sequence

The varying-domination assertion in U29. No almost-everywhere convergence of
the dominating sequence is postulated: it is extracted along subsequences
from its L¹ convergence. Limit integrability is proved from domination.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Freezing2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An a.e. limit dominated by an L¹-converging sequence is integrable,
and its integrals converge. The measure need not be finite. -/
theorem tendsto_integral_of_l1_dominating_sequence
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {b : ℕ → Ω → ℝ} {c : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hb : ∀ n, Integrable (b n) μ)
    (hc : Integrable c μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |f n ω| ≤ b n ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)))
    (hL1 : Tendsto (fun n ↦ ∫ ω, |b n ω - c ω| ∂μ) atTop (𝓝 0)) :
    Integrable g μ ∧ Tendsto (fun n ↦ ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  have hm := tendstoInMeasure_of_integral_abs_sub hb hc hL1
  have hall : ∀ᵐ ω ∂μ, ∀ n, |f n ω| ≤ b n ω := ae_all_iff.mpr hbound
  have hlimitbound : ∀ᵐ ω ∂μ, |g ω| ≤ c ω := by
    obtain ⟨s, hs, hbs⟩ := hm.exists_seq_tendsto_ae
    filter_upwards [hall, hlim, hbs] with ω hω hfω hbω
    exact le_of_tendsto_of_tendsto (hfω.comp hs.tendsto_atTop).abs hbω
      (Eventually.of_forall fun n ↦ hω (s n))
  have hg : Integrable g μ := hc.mono'
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ (hf n).aestronglyMeasurable) hlim)
    (by simpa only [Real.norm_eq_abs] using hlimitbound)
  refine ⟨hg, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨ms, hms, hae⟩ := (hm.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  let F : ℕ → Bool → Ω → ℝ := fun n a ω ↦
    if a then b (ns (ms n)) ω + f (ns (ms n)) ω
    else b (ns (ms n)) ω - f (ns (ms n)) ω
  let G : Bool → Ω → ℝ := fun a ω ↦ if a then c ω + g ω else c ω - g ω
  have hF (n : ℕ) (a : Bool) : Integrable (F n a) μ := by
    cases a
    · exact (hb _).sub (hf _)
    · exact (hb _).add (hf _)
  have hG (a : Bool) : Integrable (G a) μ := by
    cases a
    · exact hc.sub hg
    · exact hc.add hg
  have hF0 (n : ℕ) (a : Bool) : ∀ᵐ ω ∂μ, 0 ≤ F n a ω := by
    filter_upwards [hbound (ns (ms n))] with ω hω
    have hp := abs_le.mp hω
    cases a <;> simp only [F, Bool.false_eq_true, ↓reduceIte] <;> linarith [hp.1, hp.2]
  have hG0 (a : Bool) : ∀ᵐ ω ∂μ, 0 ≤ G a ω := by
    filter_upwards [hlimitbound] with ω hω
    have hp := abs_le.mp hω
    cases a <;> simp only [G, Bool.false_eq_true, ↓reduceIte] <;> linarith [hp.1, hp.2]
  have hFG (a : Bool) : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ F n a ω) atTop (𝓝 (G a ω)) := by
    filter_upwards [hae, hlim] with ω hbω hfω
    have hf' := (hfω.comp hns).comp hms.tendsto_atTop
    cases a
    · exact hbω.sub hf'
    · exact hbω.add hf'
  have hsumF (n : ℕ) : (∑ a : Bool, ∫ ω, F n a ω ∂μ) =
      2 * ∫ ω, b (ns (ms n)) ω ∂μ := by
    simp only [Fintype.sum_bool, F, Bool.false_eq_true, ↓reduceIte]
    rw [integral_add (hb _) (hf _), integral_sub (hb _) (hf _)]
    ring
  have hsumG : (∑ a : Bool, ∫ ω, G a ω ∂μ) = 2 * ∫ ω, c ω ∂μ := by
    simp only [Fintype.sum_bool, G, Bool.false_eq_true, ↓reduceIte]
    rw [integral_add hc hg, integral_sub hc hg]
    ring
  have hbint : Tendsto (fun n ↦ ∫ ω, b (ns (ms n)) ω ∂μ) atTop (𝓝 (∫ ω, c ω ∂μ)) := by
    have h := tendsto_setIntegral_of_l1 hb hc hL1 Set.univ
    simpa only [setIntegral_univ, Function.comp_def] using (h.comp hns).comp hms.tendsto_atTop
  have hmass : Tendsto (fun n ↦ ∑ a : Bool, ∫ ω, F n a ω ∂μ) atTop
      (𝓝 (∑ a : Bool, ∫ ω, G a ω ∂μ)) := by
    simpa only [hsumF, hsumG] using hbint.const_mul 2
  have hplus := finite_family_integral_tendsto hF hG hF0 hG0 hFG hmass true
  have hresult := hplus.sub hbint
  simpa only [F, G, ↓reduceIte, integral_add (hb _) (hf _), integral_add hc hg,
    add_sub_cancel_left, Function.comp_apply] using hresult

end Freezing2
