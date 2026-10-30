module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.RootedForestLaw
public import Freezing2.Companion.HistoryProbability
public import Freezing2.Companion.BirthTime

/-!
# The reverse growth and coalescence process

At reverse time `i`, active labels of the terminal tree and freezing labels
strictly later than `i` are present. A positive schedule step merges two roots
uniformly; a negative step inserts its prescribed singleton. This module
constructs the marginal laws of the graph-valued reverse construction, including
the endpoint of extinction. A joint-history object, edge times, and equality in
law with Algorithm 1 remain separate.
-/

@[expose] public section

namespace Freezing1.Reverse

open MeasureTheory
open scoped ENNReal Classical

abbrev Forest := RootedForest (ℕ ⊕ ℕ)

/-- Labels present in the reverse forest at time `i`. -/
def phaseLabels (x : SignSequence) (n i : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (Finset.range (activeCount x n).toNat).disjSum
    ((Finset.range n).filter fun j => i ≤ j ∧ x (j + 1) = false)

theorem phaseLabels_top (x : SignSequence) (n : ℕ) :
    phaseLabels x n n = (Finset.range (activeCount x n).toNat).disjSum ∅ := by
  unfold phaseLabels
  congr 1
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj
  omega

theorem phaseLabels_zero (x : SignSequence) (n : ℕ) :
    phaseLabels x n 0 = vertexLabels x n := by
  simp [phaseLabels, vertexLabels, frozenIndices]

/-- The deterministic birth time exactly characterizes label presence at each
reverse time, including the frozen-label shift by one. -/
theorem mem_phaseLabels_iff_birthTime {x : SignSequence} {n i : ℕ}
    (hi : i ≤ n) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    v ∈ phaseLabels x n i ↔ i ≤ birthTime n v := by
  cases v with
  | inl j =>
    simpa [phaseLabels, vertexLabels, birthTime, hi] using hv
  | inr j =>
    have hv' : j < n ∧ x (j + 1) = false := by
      simpa [vertexLabels, frozenIndices] using hv
    simp [phaseLabels, birthTime, hv'.1, hv'.2]

theorem fresh_freezing_label (x : SignSequence) (n i : ℕ) :
    Sum.inr i ∉ phaseLabels x n (i + 1) := by
  simp [phaseLabels]

theorem phaseLabels_attachment (x : SignSequence) (n i : ℕ) (hx : x (i + 1) = true) :
    phaseLabels x n i = phaseLabels x n (i + 1) := by
  ext v
  cases v with
  | inl j => simp [phaseLabels]
  | inr j =>
    by_cases hj : j = i
    · simp [phaseLabels, hj, hx]
    · simp only [phaseLabels, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_range]
      have h : i ≤ j ↔ i + 1 ≤ j := by omega
      rw [h]

theorem phaseLabels_freezing (x : SignSequence) (n i : ℕ) (hi : i < n)
    (hx : x (i + 1) = false) :
    phaseLabels x n i = insert (.inr i) (phaseLabels x n (i + 1)) := by
  ext v
  cases v with
  | inl j => simp [phaseLabels]
  | inr j =>
    by_cases hj : j = i
    · simp [phaseLabels, hj, hx, hi]
    · simp only [phaseLabels, Finset.inr_mem_disjSum, Finset.mem_filter, Finset.mem_range,
        Finset.mem_insert, Sum.inr.injEq]
      have h : i ≤ j ↔ i + 1 ≤ j := by omega
      simp only [hj, false_or, h]

/-- The structural assertions required at one reverse time. -/
structure ValidAt (x : SignSequence) (n i : ℕ) (F : Forest) : Prop where
  vertices_eq : F.vertices = phaseLabels x n i
  roots_card : F.roots.card = (activeCount x i).toNat
  acyclic : F.graph.IsAcyclic

def initial (x : SignSequence) (n : ℕ) : Forest :=
  RootedForest.isolated ((Finset.range (activeCount x n).toNat).disjSum ∅)

theorem initial_valid (x : SignSequence) (n : ℕ) : ValidAt x n n (initial x n) := by
  constructor
  · exact (phaseLabels_top x n).symm
  · simp [initial, RootedForest.roots, RootedForest.isolated]
  · simp [initial]

/-- Insert a freezing label if fresh. On legal reverse states it is always fresh. -/
def insertLabel (F : Forest) (i : ℕ) : Forest :=
  if h : Sum.inr i ∈ F.vertices then F else F.adjoin (.inr i) h

/-- Transition from reverse time `i+1` to `i`. -/
noncomputable def transitionLaw (x : SignSequence) (i : ℕ) (F : Forest) : Measure Forest :=
  if x (i + 1) then F.joinLaw else Measure.dirac (insertLabel F i)

instance transitionLaw_probability (x : SignSequence) (i : ℕ) (F : Forest) :
    IsProbabilityMeasure (transitionLaw x i F) := by
  unfold transitionLaw
  split_ifs <;> infer_instance

/-- The exact height-increment probability of the reverse transition kernel.
The denominator is the number of roots before the merge, as in L01. -/
theorem transitionLaw_height_increment {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {v : ℕ ⊕ ℕ} (hv : v ∈ F.vertices) :
    (transitionLaw x i F).real {F' | F'.depth v = F.depth v + 1} =
      if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0 := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  cases hx : x (i + 1)
  · have hfresh : Sum.inr i ∉ F.vertices := by
      rw [hF.vertices_eq]
      exact fresh_freezing_label x n i
    simp [transitionLaw, hx, insertLabel, hfresh, Measure.real,
      RootedForest.adjoin_depth_old F hfresh hv]
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    have hc : ((activeCount x (i + 1)).toNat : ℝ) = (activeCount x (i + 1) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hiτ)
    simp only [transitionLaw, hx, ↓reduceIte]
    rw [F.joinLaw_depth_increment htwo hv, hF.roots_card, hc]

theorem transitionLaw_valid {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n) (hF : ValidAt x n (i + 1) F) :
    ∀ᵐ F' ∂transitionLaw x i F, ValidAt x n i F' := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  have hSi : 0 < activeCount x i := positiveThrough_of_succ_le_extinctionTime hiτ i le_rfl
  cases hx : x (i + 1)
  · have hfresh : Sum.inr i ∉ F.vertices := by
      rw [hF.vertices_eq]
      exact fresh_freezing_label x n i
    have hstep : activeCount x (i + 1) = activeCount x i - 1 := by
      simp [activeCount_succ, hx, sub_eq_add_neg]
    simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte, insertLabel,
      dite_eq_right hfresh]
    apply (ae_dirac_iff (by trivial)).mpr
    constructor
    · rw [RootedForest.adjoin_vertices, hF.vertices_eq,
        phaseLabels_freezing x n i hi hx]
    · rw [RootedForest.adjoin_card_roots, hF.roots_card]
      omega
    · rw [RootedForest.adjoin_graph]
      exact hF.acyclic
  · have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
    have hstep : activeCount x (i + 1) = activeCount x i + 1 := by
      simp [activeCount_succ, hx]
    simp only [transitionLaw, hx, ↓reduceIte]
    filter_upwards [F.joinLaw_vertices htwo, F.joinLaw_roots_card htwo,
      F.joinLaw_isAcyclic htwo hF.acyclic] with F' hverts hcard hacyc
    constructor
    · rw [hverts, hF.vertices_eq, phaseLabels_attachment x n i hx]
    · have hc := hF.roots_card
      omega
    · exact hacyc

/-- Law after `k` reverse steps. After all `n` steps, the terminal law is held fixed. -/
noncomputable def lawAfter (x : SignSequence) (n : ℕ) : ℕ → Measure Forest
  | 0 => Measure.dirac (initial x n)
  | k + 1 => if k < n then
      (lawAfter x n k).bind (transitionLaw x (n - (k + 1)))
    else lawAfter x n k

instance lawAfter_probability (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (lawAfter x n k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac (initial x n)); infer_instance
  | succ k ih =>
    simp only [lawAfter]
    split_ifs
    · exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
        (Filter.Eventually.of_forall (fun F => transitionLaw_probability x _ F))
    · exact ih

/-- Every sampled reverse forest has exactly the intended labels and number
of components, and its undirected graph remains acyclic. -/
theorem lawAfter_valid (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k ≤ n) :
    ∀ᵐ F ∂lawAfter x n k, ValidAt x n (n - k) F := by
  induction k with
  | zero => simpa [lawAfter] using initial_valid x n
  | succ k ih =>
    have hkn : k < n := by omega
    have ih := ih (by omega)
    have hphase : n - k = n - (k + 1) + 1 := by omega
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [lawAfter, ite_eq_left hkn, Measure.bind_apply (by trivial)
      measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _F, (1 : ℝ≥0∞) ∂lawAfter x n k := by
        apply lintegral_congr_ae
        filter_upwards [ih] with F hF
        rw [hphase] at hF
        exact (ae_iff_prob_eq_one measurable_from_top).mp
          (transitionLaw_valid hn (by omega) hF)
      _ = 1 := by simp

/-- The terminal law of the reverse construction. -/
noncomputable def treeLaw (x : SignSequence) (n : ℕ) : Measure Forest := lawAfter x n n

instance treeLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (treeLaw x n) := lawAfter_probability x n n

theorem treeLaw_valid (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, ValidAt x n 0 F := by
  simpa only [treeLaw, Nat.sub_self] using lawAfter_valid x n n hn le_rfl

/-- The final reverse forest has exactly one component and the deterministic
vertex labels from the manuscript. -/
theorem treeLaw_vertices_and_root (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, F.vertices = vertexLabels x n ∧ F.roots.card = 1 := by
  filter_upwards [treeLaw_valid x n hn] with F hF
  constructor
  · simpa only [phaseLabels_zero] using hF.vertices_eq
  · simpa using hF.roots_card

theorem treeLaw_isTree (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, F.toGraph.IsTree := by
  filter_upwards [treeLaw_valid x n hn, treeLaw_vertices_and_root x n hn] with F hF hverts
  exact F.isTree_of_one_root hverts.2 hF.acyclic

/-- Uniform vertex selection conditional on the actual terminal reverse tree. -/
noncomputable def uniformVertexLaw (x : SignSequence) (n : ℕ) : Measure (ℕ ⊕ ℕ) :=
  (treeLaw x n).bind (fun F => Measure.uniformOfFinset F.vertices)

/-- Randomizing the forest does not randomize its label set. -/
theorem uniformVertexLaw_eq (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : uniformVertexLaw x n = uniformVertex x n := by
  apply Measure.ext
  intro A hA
  rw [uniformVertexLaw, Measure.bind_apply hA measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ _F, uniformVertex x n A ∂treeLaw x n := by
      apply lintegral_congr_ae
      filter_upwards [treeLaw_vertices_and_root x n hn] with F hF
      simp only [hF.1, uniformVertex]
    _ = uniformVertex x n A := by simp

/-- The birth-time formula for a vertex chosen uniformly conditional on the
constructed reverse tree. The birth map's phase-presence interpretation is
`mem_phaseLabels_iff_birthTime`. -/
theorem uniform_birthTime_lt (x : SignSequence) (n m : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hm : m ≤ n) :
    (uniformVertexLaw x n).real {v | birthTime n v < m} =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  rw [uniformVertexLaw_eq x n hn]
  exact Freezing1.uniform_birthTime_lt (activeCount_nonneg_of_le_extinctionTime hn) hm

end Freezing1.Reverse
