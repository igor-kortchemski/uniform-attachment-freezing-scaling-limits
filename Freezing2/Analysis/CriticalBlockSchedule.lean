module

public import Freezing2.Analysis.CriticalIsolationRate

/-!
# Disjoint alternating block schedules

Source phases decrease by two blocks at a time. Their endpoints match exactly,
including the possible upper-boundary birth. Natural subtraction is only used
with explicit inequalities proving that each trial remains at a positive phase.
-/

@[expose] public section

namespace Freezing2

def criticalTrialPhase (i₀ d j : ℕ) : ℕ := (i₀ - 2 * j) * d

def criticalTrialBlock (i₀ j : ℕ) : ℕ := i₀ - (2 * j + 1)

theorem criticalTrialPhase_antitone (i₀ d : ℕ) : Antitone (criticalTrialPhase i₀ d) := by
  intro i j hij
  exact Nat.mul_le_mul_right d (Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hij) i₀)

theorem criticalTrialPhase_le (i₀ d j : ℕ) : criticalTrialPhase i₀ d j ≤ i₀ * d :=
  Nat.mul_le_mul_right d (Nat.sub_le _ _)

theorem criticalTrialBlock_pos {i₀ m j : ℕ} (hm : 2 * m ≤ i₀) (hj : j < m) :
    1 ≤ criticalTrialBlock i₀ j := by
  unfold criticalTrialBlock
  omega

theorem criticalTrialPhase_eq_block_succ {i₀ m j d : ℕ}
    (hm : 2 * m ≤ i₀) (hj : j < m) :
    criticalTrialPhase i₀ d j = (criticalTrialBlock i₀ j + 1) * d := by
  unfold criticalTrialPhase criticalTrialBlock
  congr 1
  omega

theorem criticalTrialPhase_succ_eq_block_pred (i₀ j d : ℕ) :
    criticalTrialPhase i₀ d (j + 1) = (criticalTrialBlock i₀ j - 1) * d := by
  unfold criticalTrialPhase criticalTrialBlock
  congr 1

theorem criticalTrialBlock_middle_gap {i₀ m j d : ℕ}
    (hm : 2 * m ≤ i₀) (hj : j < m) :
    criticalTrialBlock i₀ j * d - criticalTrialPhase i₀ d (j + 1) = d := by
  rw [criticalTrialPhase_succ_eq_block_pred]
  have hi := criticalTrialBlock_pos hm hj
  have he : (criticalTrialBlock i₀ j - 1) * d + d = criticalTrialBlock i₀ j * d := by
    calc
      _ = (criticalTrialBlock i₀ j - 1 + 1) * d := by ring
      _ = _ := by rw [Nat.sub_add_cancel hi]
  omega

theorem criticalTrialBlock_in_window {p i₀ j : ℕ}
    (hj : j < (p - 1) / 2) : i₀ ≤ criticalTrialBlock i₀ j + p + 1 := by
  have hdiv := Nat.div_mul_le_self (p - 1) 2
  unfold criticalTrialBlock
  omega

theorem criticalIsolationTrials_le_window (k : ℕ) :
    2 * criticalIsolationTrials k ≤ criticalIsolationWindow k := by
  have h := Nat.div_mul_le_self (criticalIsolationWindow k - 1) 2
  unfold criticalIsolationTrials
  omega

end Freezing2
