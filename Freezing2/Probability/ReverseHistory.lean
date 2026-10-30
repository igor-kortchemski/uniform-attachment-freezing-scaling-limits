module

public import Freezing2.Companion.ReverseForest
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The joint reverse-forest history

This is the trajectory law of the actual uniform-root-pair transition kernels.
Trajectory time `k` corresponds to source forest time `n-k`; after the terminal
horizon the last forest is held fixed. Mathlib's trajectory construction supplies
the joint probability measure and its conditional-expectation property.

No Markov property, independence, or conditional-height estimate is assumed.
The existing `lawAfter` is identified with every coordinate marginal. Edge-time
labels and equality in law with the forward construction remain separate.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Freezing2.ReverseHistory

abbrev Forest := Freezing1.Reverse.Forest

/-- Full trajectories in increasing construction time. Only the first `n+1`
coordinates describe the finite reverse construction. -/
abbrev History := ℕ → Forest

abbrev Prefix (k : ℕ) := ∀ _i : Finset.Iic k, Forest

def last (k : ℕ) (h : Prefix k) : Forest := h ⟨k, Finset.mem_Iic.mpr le_rfl⟩

theorem measurable_last (k : ℕ) : Measurable (last k) := measurable_pi_apply _

/-- The actual next-state kernel, held fixed after all reverse steps. -/
noncomputable def stepKernel (x : Freezing1.SignSequence) (n k : ℕ) :
    Kernel Forest Forest where
  toFun F := if k < n then Freezing1.Reverse.transitionLaw x (n - (k + 1)) F
    else Measure.dirac F
  measurable' := measurable_from_top

instance stepKernel_markov (x : Freezing1.SignSequence) (n k : ℕ) :
    IsMarkovKernel (stepKernel x n k) := by
  constructor
  intro F
  change IsProbabilityMeasure
    (if k < n then Freezing1.Reverse.transitionLaw x (n - (k + 1)) F else Measure.dirac F)
  split_ifs <;> infer_instance

/-- The next-state kernel reads the last coordinate of the entire exposed prefix. -/
noncomputable def prefixKernel (x : Freezing1.SignSequence) (n k : ℕ) :
    Kernel (Prefix k) Forest :=
  (stepKernel x n k).comap (last k) (measurable_last k)

instance prefixKernel_markov (x : Freezing1.SignSequence) (n k : ℕ) :
    IsMarkovKernel (prefixKernel x n k) := by
  unfold prefixKernel
  infer_instance

/-- The initial prefix contains the prescribed isolated terminal active labels.
It is the empty forest when the horizon is the extinction time. -/
def initialPrefix (x : Freezing1.SignSequence) (n : ℕ) :
    Prefix 0 := fun _ ↦ Freezing1.Reverse.initial x n

/-- The concrete probability law of all reverse construction choices. -/
noncomputable def jointLaw (x : Freezing1.SignSequence) (n : ℕ) : Measure History :=
  Kernel.traj (X := fun _ ↦ Forest) (prefixKernel x n) 0 (initialPrefix x n)

instance jointLaw_probability (x : Freezing1.SignSequence) (n : ℕ) :
    IsProbabilityMeasure (jointLaw x n) := by
  unfold jointLaw
  infer_instance

/-- The forest bearing source index `i`. For the intended indices `i≤n`, this
is exactly coordinate `n-i` of the construction trajectory. -/
def forestAt (n i : ℕ) (ω : History) : Forest := ω (n - i)

/-- Every finite-dimensional prefix is the genuine iterated-kernel law. -/
theorem jointLaw_map_prefix (x : Freezing1.SignSequence) (n k : ℕ) :
    (jointLaw x n).map (frestrictLe k) =
      Kernel.partialTraj (X := fun _ ↦ Forest) (prefixKernel x n) 0 k (initialPrefix x n) :=
  Kernel.traj_map_frestrictLe_apply (X := fun _ ↦ Forest) _ _ _

/-- The initial forest coordinate is deterministic. -/
theorem jointLaw_map_zero (x : Freezing1.SignSequence) (n : ℕ) :
    (jointLaw x n).map (fun ω ↦ ω 0) = Measure.dirac (Freezing1.Reverse.initial x n) := by
  have he : (fun ω : History ↦ ω 0) = last 0 ∘ frestrictLe 0 := rfl
  rw [he, ← Measure.map_map (measurable_last 0) (measurable_frestrictLe 0),
    jointLaw_map_prefix, Kernel.partialTraj_self, Kernel.id_apply]
  exact Measure.map_dirac' (measurable_last 0) _

/-- Consecutive coordinates follow the specified transition even conditional
on the complete preceding prefix. This marginal recursion is used below. -/
theorem jointLaw_map_succ (x : Freezing1.SignSequence) (n k : ℕ) :
    (jointLaw x n).map (fun ω ↦ ω (k + 1)) =
      ((jointLaw x n).map (fun ω ↦ ω k)).bind (stepKernel x n k) := by
  let κ := prefixKernel x n
  have hsplit := congrArg (fun K ↦ K (initialPrefix x n))
    (Kernel.traj_comp_partialTraj (X := fun _ ↦ Forest) (κ := κ) (Nat.zero_le k))
  rw [Kernel.comp_apply] at hsplit
  have hnext : (jointLaw x n).map (fun ω ↦ ω (k + 1)) =
      (Kernel.partialTraj (X := fun _ ↦ Forest) κ 0 k (initialPrefix x n)).bind (κ k) := by
    change (Kernel.traj (X := fun _ ↦ Forest) κ 0 (initialPrefix x n)).map _ = _
    rw [← hsplit, Measure.map_bind (Kernel.aemeasurable _)
      (measurable_pi_apply (k + 1)).aemeasurable]
    congr 1
    funext h
    have hm := congrArg (fun K ↦ K h)
      (Kernel.map_traj_succ_self (X := fun _ ↦ Forest) (κ := κ) (a := k))
    simpa only [Kernel.map_apply _ (measurable_pi_apply (k + 1))] using hm
  rw [hnext, ← jointLaw_map_prefix]
  change ((jointLaw x n).map (frestrictLe k)).bind
      (fun h ↦ stepKernel x n k (last k h)) = _
  rw [← Measure.bind_map (measurable_last k).aemeasurable (Kernel.aemeasurable _),
    Measure.map_map (measurable_last k) (measurable_frestrictLe _)]
  rfl

/-- Every coordinate marginal agrees with the already constructed reverse law,
including absorption after the terminal horizon. -/
theorem jointLaw_map_eval (x : Freezing1.SignSequence) (n k : ℕ) :
    (jointLaw x n).map (fun ω ↦ ω k) = Freezing1.Reverse.lawAfter x n k := by
  induction k with
  | zero => exact jointLaw_map_zero x n
  | succ k ih =>
    rw [jointLaw_map_succ, ih]
    by_cases hk : k < n
    · simp only [Freezing1.Reverse.lawAfter, stepKernel, Kernel.coe_mk, hk, ite_true]
    · simp only [Freezing1.Reverse.lawAfter, stepKernel, Kernel.coe_mk, hk, ite_false,
        Measure.bind_dirac]

/-- The entire sampled trajectory is valid at every source time simultaneously. -/
theorem jointLaw_valid (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ ω ∂jointLaw x n, ∀ k ≤ n, Freezing1.Reverse.ValidAt x n (n - k) (ω k) := by
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k ≤ n
  · have h := Freezing1.Reverse.lawAfter_valid x n k hn hk
    rw [← jointLaw_map_eval] at h
    exact (ae_of_ae_map (measurable_pi_apply k).aemeasurable h).mono fun _ hω _ ↦ hω
  · exact Eventually.of_forall fun _ h ↦ False.elim (hk h)

theorem jointLaw_forestAt_valid (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ ω ∂jointLaw x n, ∀ i ≤ n, Freezing1.Reverse.ValidAt x n i (forestAt n i ω) := by
  filter_upwards [jointLaw_valid x n hn] with ω hω
  intro i hi
  simpa only [Nat.sub_sub_self hi, forestAt] using hω (n - i) (Nat.sub_le n i)

end Freezing2.ReverseHistory
