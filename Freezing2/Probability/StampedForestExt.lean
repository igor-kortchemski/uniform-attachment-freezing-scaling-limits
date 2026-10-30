module

public import Freezing2.Probability.ActiveLabelPermutation
public import Freezing2.Probability.ReverseOutsideSupport

/-!
# Recovering total stamped forests from present parent and time records

The parent map determines roots and depths on a finite rooted forest: induction
on the original depth follows its parent chain. Outside normality then promotes
equality on present vertices to equality of the complete total representation.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.ReverseStamped

theorem root_depth_eq_of_parent_eq {V : Type*} [DecidableEq V]
    {F G : Freezing1.RootedForest V} (hverts : F.vertices = G.vertices)
    (hparent : F.parent = G.parent) {v : V} (hv : v ∈ F.vertices) :
    F.root v = G.root v ∧ F.depth v = G.depth v := by
  have hmain : ∀ d : ℕ, ∀ w : V, F.depth w = d → w ∈ F.vertices →
      F.root w = G.root w ∧ F.depth w = G.depth w := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro w hd hw
      have hwG : w ∈ G.vertices := hverts ▸ hw
      by_cases hr : w = F.root w
      · have hFdepth : F.depth w = 0 := by simpa only [← hr] using F.depth_root w hw
        have hFp : F.parent w = w := by simpa only [← hr] using F.parent_root w hw
        have hGp : G.parent w = w := by simpa only [hparent] using hFp
        have hGr : G.root w = w := by
          by_contra hn
          have hh := G.depth_parent w hwG (Ne.symm hn)
          rw [hGp] at hh
          omega
        have hGdepth : G.depth w = 0 := by simpa only [hGr] using G.depth_root w hwG
        exact ⟨hr.symm.trans hGr.symm, hFdepth.trans hGdepth.symm⟩
      · have hFp := F.depth_parent w hw hr
        have hpn : F.parent w ≠ w := by
          intro he
          rw [he] at hFp
          omega
        have hGr : w ≠ G.root w := by
          intro he
          apply hpn
          rw [hparent]
          simpa only [← he] using G.parent_root w hwG
        have hGp := G.depth_parent w hwG hGr
        have hpIH := ih (F.depth (F.parent w)) (by omega) (F.parent w) rfl
          (F.parent_mem w hw)
        constructor
        · calc
            F.root w = F.root (F.parent w) := (F.root_parent w hw).symm
            _ = G.root (F.parent w) := hpIH.1
            _ = G.root w := by rw [hparent]; exact G.root_parent w hwG
        · rw [← hparent] at hGp
          omega
  exact hmain (F.depth v) v rfl hv

/-- The actual outside normal form is what makes a present-vertex record
comparison determine literal equality of stamped forest values. -/
theorem stampedForest_eq_of_parent_time {F G : Forest}
    (hF : OutsideNormal F) (hG : OutsideNormal G)
    (hverts : F.forest.vertices = G.forest.vertices)
    (hp : ∀ v ∈ F.forest.vertices, F.forest.parent v = G.forest.parent v)
    (ht : ∀ v ∈ F.forest.vertices, F.edgeTime v = G.edgeTime v) : F = G := by
  have hparent : F.forest.parent = G.forest.parent := by
    funext v
    by_cases hv : v ∈ F.forest.vertices
    · exact hp v hv
    · have hvG : v ∉ G.forest.vertices := by simpa only [← hverts] using hv
      exact (hF v hv).1.trans (hG v hvG).1.symm
  apply stampedForest_ext
  · apply rootedForest_ext hverts hparent
    · funext v
      by_cases hv : v ∈ F.forest.vertices
      · exact (root_depth_eq_of_parent_eq hverts hparent hv).1
      · have hvG : v ∉ G.forest.vertices := by simpa only [← hverts] using hv
        exact (hF v hv).2.1.trans (hG v hvG).2.1.symm
    · funext v
      by_cases hv : v ∈ F.forest.vertices
      · exact (root_depth_eq_of_parent_eq hverts hparent hv).2
      · have hvG : v ∉ G.forest.vertices := by simpa only [← hverts] using hv
        exact (hF v hv).2.2.1.trans (hG v hvG).2.2.1.symm
  · funext v
    by_cases hv : v ∈ F.forest.vertices
    · exact ht v hv
    · have hvG : v ∉ G.forest.vertices := by simpa only [← hverts] using hv
      exact (hF v hv).2.2.2.trans (hG v hvG).2.2.2.symm

end Freezing2.ReverseStamped
