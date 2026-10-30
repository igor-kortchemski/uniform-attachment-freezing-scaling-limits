module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.PiSystem
public import Mathlib.Tactic.Linarith

/-!
# Weak convergence from half-open interval counts

The measures in Lemma `lem:hnalpha(ii)` are finite measures whose total masses
converge to one; their masses need not equal one at a finite horizon. This
criterion combines the interval version of Portmanteau with normalization and
the convergence of total mass, preserving the source's exact normalization.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Freezing2

/-- Convergence on every bounded half-open interval, together with convergence
of total mass, gives weak convergence to a nonzero finite measure on the line. -/
theorem finiteMeasure_tendsto_of_Ioc {μ : ℕ → FiniteMeasure ℝ} {ν : FiniteMeasure ℝ}
    (hν : ν ≠ 0)
    (hmass : Tendsto (fun n ↦ (μ n).mass) atTop (𝓝 ν.mass))
    (hIoc : ∀ a b : ℝ, a < b →
      Tendsto (fun n ↦ μ n (Ioc a b)) atTop (𝓝 (ν (Ioc a b)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have hνmass : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
  have hμ : ∀ᶠ n in atTop, μ n ≠ 0 := by
    filter_upwards [hmass.eventually_ne hνmass] with n hn
    exact (μ n).mass_nonzero_iff.mp hn
  apply (ν.tendsto_normalize_iff_tendsto hν).mp
  refine ⟨?_, hmass⟩
  apply (isPiSystem_Ioc (id : ℝ → ℝ) id).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, _, rfl⟩
    exact measurableSet_Ioc
  · intro U hU x hx
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
    let c : ℝ := (x + b) / 2
    have hxc : x < c := by dsimp [c]; linarith [hab.2]
    have hcb : c < b := by dsimp [c]; linarith [hab.2]
    refine ⟨Ioc a c, ⟨a, c, hab.1.trans hxc, rfl⟩,
      Ioc_mem_nhds hab.1 hxc, ?_⟩
    intro y hy
    exact hsub ⟨hy.1, hy.2.trans_lt hcb⟩
  · rintro s ⟨a, b, hab, rfl⟩
    rw [ν.normalize_eq_of_nonzero hν]
    apply ((hmass.inv₀ hνmass).mul (hIoc a b hab)).congr'
    filter_upwards [hμ] with n hn
    exact ((μ n).normalize_eq_of_nonzero hn (Ioc a b)).symm

/-- Real-valued half-open interval mass is the difference of the two cumulative
masses. Finiteness excludes subtraction of infinite quantities. -/
theorem finiteMeasure_real_Ioc (μ : FiniteMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (μ : Measure ℝ).real (Ioc a b) =
      (μ : Measure ℝ).real (Iic b) - (μ : Measure ℝ).real (Iic a) := by
  have hs : Iic b \ Iic a = Ioc a b := by
    ext t
    simp only [Set.mem_sdiff, mem_Iic, not_le, mem_Ioc, and_comm]
  rw [← hs]
  exact measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic

/-- A convenient cumulative-mass version of the finite-measure criterion.
Neither the approximating measures nor their cumulative masses are normalized. -/
theorem finiteMeasure_tendsto_of_Iic {μ : ℕ → FiniteMeasure ℝ} {ν : FiniteMeasure ℝ}
    (hν : ν ≠ 0)
    (hmass : Tendsto (fun n ↦ ((μ n).mass : ℝ)) atTop (𝓝 (ν.mass : ℝ)))
    (hIic : ∀ a : ℝ,
      Tendsto (fun n ↦ (μ n : Measure ℝ).real (Iic a))
        atTop (𝓝 ((ν : Measure ℝ).real (Iic a)))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply finiteMeasure_tendsto_of_Ioc hν (NNReal.tendsto_coe.mp hmass)
  intro a b hab
  apply NNReal.tendsto_coe.mp
  simpa only [← FiniteMeasure.measureReal_eq_coe_coeFn,
    finiteMeasure_real_Ioc _ hab.le] using (hIic b).sub (hIic a)

end Freezing2
