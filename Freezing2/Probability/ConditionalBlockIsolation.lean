module

public import Freezing2.Probability.ContinuationBlockIsolation
public import Freezing2.Probability.ContinuationConditional

/-!
# Actual-history conditional isolation bound

The full-past conditional endpoint law is the actual continuation kernel.
Its finite valid-state bound applies almost surely. Marked vertices born at
the initial boundary are singleton components by the actual-history birth
support theorem. No block independence hypothesis is used.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace Freezing2.ReverseHistory

open Freezing1 Freezing2.TrackedClusters

/-- The upper-boundary singleton condition for all marked labels is a
consequence of the actual joint history, not an extra model assumption. -/
theorem jointLaw_alone_at_fixed_birth_boundary {x : SignSequence} {n s : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {A : Finset (ℕ ⊕ ℕ)}
    (hA : A ⊆ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ v ∈ A, Freezing1.birthTime n v = s →
      Alone (ω (n - s)) A v := by
  apply ae_all_iff.mpr
  intro v
  by_cases hv : v ∈ A
  · by_cases hb : Freezing1.birthTime n v = s
    · have h := lawAfter_alone_at_birth hn hA (hA hv)
      rw [hb, ← jointLaw_map_eval] at h
      exact (ae_of_ae_map (measurable_pi_apply _).aemeasurable h).mono
        (fun _ hω _ _ ↦ hω)
    · exact Eventually.of_forall fun _ _ he ↦ False.elim (hb he)
  · exact Eventually.of_forall fun _ he _ ↦ False.elim (hv he)

/-- The actual conditional probability of oldest isolation is at most 3/4,
given the entire exposed past. All birth and phase conditions are explicit;
the final all-born interval may use the repaired longer sampling block. -/
theorem conditional_oldest_isolation_le_three_quarters {x : SignSequence}
    {n k K s r t : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : 0 < k) (hkn : k ≤ n)
    (hs : s ≤ n) (hr : r ≤ s) (ht : t ≤ r)
    {M : ℝ} (hM : 0 < M) (hlarge : 12 ≤ M * Real.sqrt k)
    (hpop : ∀ i ≤ n, (Freezing1.activeCount x i : ℝ) ≤ M * Real.sqrt n)
    (hlength : tightnessBlockLength M n k ≤ r - t)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n)
    (hcard : A.card = K + 1) (hK : M * Real.sqrt k ≤ K)
    {u : ℕ ⊕ ℕ} (hu : u ∈ A) (huBorn : s ≤ Freezing1.birthTime n u)
    (hyoung : ∀ v ∈ A, v ≠ u → Freezing1.birthTime n v ≤ s)
    (hborn : ∀ v ∈ A, r ≤ Freezing1.birthTime n v) :
    ∀ᵐ ω ∂jointLaw x n,
      ((jointLaw x n)[(fun ω ↦ {G | Alone G A u}.indicator (fun _ ↦ (1 : ℝ))
        (ω (n - t))) | Filtration.piLE (X := fun _ ↦ Forest) (n - s)]) ω ≤ 3 / 4 := by
  have hts : t ≤ s := ht.trans hr
  have hsum : n - s + (s - t) ≤ n := by omega
  have hphase : n - (n - s) = s := Nat.sub_sub_self hs
  have hend : n - s + (s - t) = n - t := by omega
  have hc := conditional_endpoint_indicator x hsum {G | Alone G A u}
  rw [hphase, hend] at hc
  filter_upwards [hc, jointLaw_valid x n hn,
    jointLaw_alone_at_fixed_birth_boundary hn hA (s := s)] with ω hcond hvalid hboundary
  rw [hcond]
  have hF : Reverse.ValidAt x n s (ω (n - s)) := by
    simpa only [hphase] using hvalid (n - s) (Nat.sub_le _ _)
  exact ReverseContinuation.oldest_isolation_kernel_le_three_quarters hn hk hkn hs hr ht hF
    hM hlarge hpop hlength hA hcard hK hu huBorn hyoung
    (fun v hv _ hb ↦ hboundary v hv hb) hborn

end Freezing2.ReverseHistory
