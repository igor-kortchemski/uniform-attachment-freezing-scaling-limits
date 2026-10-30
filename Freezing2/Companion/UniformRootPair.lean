module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

/-!
# Uniform ordered pairs of distinct component roots

Algorithm 2 chooses an ordered pair of different roots uniformly. The counting
laws here give the one-step height and coalescence hazards: the second root is
uniform, and either ordering of two fixed distinct roots has total probability
`2 / (S * (S - 1))`. These are laws of the actual finite uniform measure, not
assumed conditional probabilities for a forest process.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem card_offDiag_eq_mul_pred (s : Finset V) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

omit [DecidableEq V] in
theorem offDiag_nonempty_of_two_le_card {s : Finset V} (hs : 2 ≤ s.card) :
    s.offDiag.Nonempty := by
  rw [← Finset.card_pos, card_offDiag_eq_mul_pred]
  exact Nat.mul_pos (by omega) (by omega)

theorem offDiag_filter_snd (s : Finset V) {v : V} (hv : v ∈ s) :
    s.offDiag.filter (fun p => p.2 = v) = (s.erase v) ×ˢ {v} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
    Finset.mem_erase, Finset.mem_singleton]
  aesop

theorem offDiag_filter_snd_card (s : Finset V) {v : V} (hv : v ∈ s) :
    (s.offDiag.filter (fun p => p.2 = v)).card = s.card - 1 := by
  rw [offDiag_filter_snd s hv, Finset.card_product]
  simp [Finset.card_erase_of_mem hv]

omit [DecidableEq V] in
theorem card_offDiag_real (s : Finset V) (hs : 1 ≤ s.card) :
    (s.offDiag.card : ℝ) = (s.card : ℝ) * ((s.card : ℝ) - 1) := by
  rw [card_offDiag_eq_mul_pred, Nat.cast_mul, Nat.cast_sub hs]
  norm_num

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Uniform sampling without replacement, with the order retained. -/
noncomputable def uniformRootPair (s : Finset V) : Measure (V × V) :=
  Measure.uniformOfFinset s.offDiag

omit [DecidableEq V] in
theorem uniformRootPair_isProbabilityMeasure (s : Finset V) (hs : 2 ≤ s.card) :
    IsProbabilityMeasure (uniformRootPair s) := by
  constructor
  rw [uniformRootPair, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self
    (by exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne')
    (ENNReal.natCast_ne_top _)

omit [DecidableEq V] in
/-- Every prescribed ordered pair of distinct roots has the claimed mass. -/
theorem uniformRootPair_ordered (s : Finset V) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    (uniformRootPair s).real {(a, b)} =
      1 / ((s.card : ℝ) * ((s.card : ℝ) - 1)) := by
  have hs : 1 ≤ s.card := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, ha⟩)
  change ((Measure.uniformOfFinset s.offDiag) {(a, b)}).toReal = _
  rw [Measure.uniformOfFinset_apply_singleton_of_mem
    (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [card_offDiag_real s hs]
  exact one_div _ |>.symm

/-- The second root is uniform; this is the one-step height-increment hazard. -/
theorem uniformRootPair_second (s : Finset V) {v : V}
    (hv : v ∈ s) (hs : 2 ≤ s.card) :
    (uniformRootPair s).real {p | p.2 = v} = 1 / (s.card : ℝ) := by
  change ((Measure.uniformOfFinset s.offDiag) {p | p.2 = v}).toReal = _
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [offDiag_filter_snd_card s hv, card_offDiag_real s (by omega)]
  rw [Nat.cast_sub (by omega : 1 ≤ s.card), Nat.cast_one]
  have hcard : (s.card : ℝ) ≥ 2 := by exact_mod_cast hs
  have hzero : (s.card : ℝ) ≠ 0 := by linarith
  have hone : (s.card : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hzero, hone]

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The two orders of distinct prescribed roots form exactly a two-element set. -/
theorem offDiag_filter_unordered (s : Finset V) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    s.offDiag.filter (fun p => p = (a, b) ∨ p = (b, a)) = {(a, b), (b, a)} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
    Finset.mem_singleton]
  aesop

/-- Either ordering of two fixed distinct roots has mass `2/[S(S-1)]`.
This is the one-step coalescence hazard before the two vertices have merged. -/
theorem uniformRootPair_unordered (s : Finset V) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    (uniformRootPair s).real {p | p = (a, b) ∨ p = (b, a)} =
      2 / ((s.card : ℝ) * ((s.card : ℝ) - 1)) := by
  have hs : 1 ≤ s.card := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a, ha⟩)
  change ((Measure.uniformOfFinset s.offDiag) {p | p = (a, b) ∨ p = (b, a)}).toReal = _
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [offDiag_filter_unordered s ha hb hab, card_offDiag_real s hs]
  have hp : (a, b) ≠ (b, a) := by intro h; exact hab (congrArg Prod.fst h)
  simp [hp]

/-- The same coalescence hazard in the binomial-coefficient notation of the paper. -/
theorem uniformRootPair_coalescence (s : Finset V) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    (uniformRootPair s).real {p | p = (a, b) ∨ p = (b, a)} =
      1 / (s.card.choose 2 : ℝ) := by
  rw [uniformRootPair_unordered s ha hb hab, Nat.cast_choose_two, one_div, inv_div]

end Freezing1
