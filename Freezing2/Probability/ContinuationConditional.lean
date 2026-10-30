module

public import Freezing2.Probability.ReverseContinuation
public import Freezing2.Probability.ReverseConditional

/-!
# Conditional block laws on the actual reverse history

The future endpoint law given the entire exposed history is the continuation
from its last forest. This supplies the Markov step needed for block iteration;
independence of different block events is neither assumed nor asserted.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Freezing2.ReverseHistory

theorem traj_map_eval_start (x : Freezing1.SignSequence) (n a : ℕ) (h : Prefix a) :
    (Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) a h).map (fun ω ↦ ω a) =
      Measure.dirac (last a h) := by
  have he : (fun ω : History ↦ ω a) = last a ∘ frestrictLe a := rfl
  rw [he, ← Measure.map_map (measurable_last a) (measurable_frestrictLe a),
    Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
  exact Measure.map_dirac' (measurable_last a) _

theorem traj_map_eval_succ (x : Freezing1.SignSequence) (n : ℕ)
    {a k : ℕ} (hak : a ≤ k) (h : Prefix a) :
    (Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) a h).map (fun ω ↦ ω (k + 1)) =
      ((Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) a h).map
        (fun ω ↦ ω k)).bind (stepKernel x n k) := by
  let κ := prefixKernel x n
  have hsplit := congrArg (fun K ↦ K h)
    (Kernel.traj_comp_partialTraj (X := fun _ ↦ Forest) (κ := κ) hak)
  rw [Kernel.comp_apply] at hsplit
  have hnext : (Kernel.traj (X := fun _ ↦ Forest) κ a h).map (fun ω ↦ ω (k + 1)) =
      (Kernel.partialTraj (X := fun _ ↦ Forest) κ a k h).bind (κ k) := by
    rw [← hsplit, Measure.map_bind (Kernel.aemeasurable _)
      (measurable_pi_apply (k + 1)).aemeasurable]
    congr 1
    funext p
    have hm := congrArg (fun K ↦ K p)
      (Kernel.map_traj_succ_self (X := fun _ ↦ Forest) (κ := κ) (a := k))
    simpa only [Kernel.map_apply _ (measurable_pi_apply (k + 1))] using hm
  rw [hnext, ← Kernel.traj_map_frestrictLe_apply]
  change ((Kernel.traj (X := fun _ ↦ Forest) κ a h).map (frestrictLe k)).bind
      (fun p ↦ stepKernel x n k (last k p)) = _
  rw [← Measure.bind_map (measurable_last k).aemeasurable (Kernel.aemeasurable _),
    Measure.map_map (measurable_last k) (measurable_frestrictLe _)]
  rfl

/-- Future coordinates under the actual trajectory kernel have exactly the
arbitrary-initial-forest continuation law. -/
theorem traj_map_eval_continuation (x : Freezing1.SignSequence) {n a m : ℕ}
    (ham : a + m ≤ n) (h : Prefix a) :
    (Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) a h).map
      (fun ω ↦ ω (a + m)) = ReverseContinuation.law x (n - a) (last a h) m := by
  induction m with
  | zero => simpa only [Nat.add_zero, ReverseContinuation.law] using traj_map_eval_start x n a h
  | succ m ih =>
      have ham' : a + m ≤ n := by omega
      have hm : m < n - a := by omega
      have hk : a + m < n := by omega
      have he : n - (a + m + 1) = n - a - (m + 1) := by omega
      rw [Nat.add_succ, traj_map_eval_succ x n (by omega), ih ham']
      simp only [ReverseContinuation.law, hm, ite_true, stepKernel, Kernel.coe_mk, hk, he]

/-- Conditional probability of any endpoint event, given the entire actual
past, is its probability under the continuation kernel from the current forest. -/
theorem conditional_endpoint_indicator (x : Freezing1.SignSequence) {n a m : ℕ}
    (ham : a + m ≤ n) (E : Set Forest) :
    (jointLaw x n)[(fun ω ↦ E.indicator (fun _ ↦ (1 : ℝ)) (ω (a + m))) |
      Filtration.piLE (X := fun _ ↦ Forest) a] =ᵐ[jointLaw x n]
      fun ω ↦ (ReverseContinuation.law x (n - a) (ω a) m).real E := by
  have hE : MeasurableSet E := by trivial
  have hi : Integrable (fun ω : History ↦ E.indicator (fun _ ↦ (1 : ℝ)) (ω (a + m)))
      (jointLaw x n) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_const.indicator hE).comp (measurable_pi_apply (a + m))).aestronglyMeasurable)
    exact Eventually.of_forall fun ω ↦ by
      by_cases he : ω (a + m) ∈ E <;> simp [he]
  have hc := Kernel.condExp_traj (X := fun _ ↦ Forest) (κ := prefixKernel x n)
    (Nat.zero_le a) (x₀ := initialPrefix x n) hi
  refine hc.trans (Eventually.of_forall fun ω ↦ ?_)
  change (∫ y, E.indicator (fun _ ↦ (1 : ℝ)) (y (a + m))
    ∂Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) a (frestrictLe a ω)) = _
  rw [← integral_map (measurable_pi_apply (a + m)).aemeasurable
    (measurable_const.indicator hE).aestronglyMeasurable,
    traj_map_eval_continuation x ham]
  exact integral_indicator_one hE

end Freezing2.ReverseHistory
