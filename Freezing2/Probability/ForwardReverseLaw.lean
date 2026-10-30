module

public import Freezing2.Probability.CanonicalPermutation
public import Freezing2.Probability.CanonicalForwardGraph
public import Freezing2.Probability.ActivePermutationHistory
public import Freezing2.Probability.ReverseTerminalLaw
public import Freezing2.Probability.AtomicComparison
public import Freezing2.Probability.FiniteFibreMass

/-!
# Exact probability comparison from the active-label fibres

The actual terminal-history mass formulas and the exact factorial active-label
fibres prove equality of the two concrete laws. Comparison takes place first
on the countable forward-history carrier: matching positive atoms and total
mass one suffice, without a separate converse support reconstruction. The
canonical map's finite graph and label interpretation is proved independently
in `CanonicalForwardGraph`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseStamped

/-- An actual canonical fibre consisting of exactly the active-label orbit has
the forward source mass: the factorial orbit size cancels the reverse factor. -/
theorem canonicalHistory_map_atom_of_ae_orbit (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {h : ReverseChoiceHistory.History} (hh : ReverseChoiceHistory.Legal x n h)
    (hlen : h.length = n)
    (hFibre : (canonicalHistory x n) ⁻¹' {canonicalHistory x n (ReverseChoiceHistory.state x n h)}
      =ᵐ[Freezing1.ReverseStamped.treeLaw x n]
        (activeOrbit (Freezing1.activeCount x n).toNat (ReverseChoiceHistory.state x n h) : Set Forest)) :
    ((Freezing1.ReverseStamped.treeLaw x n).map (canonicalHistory x n)).real
      {canonicalHistory x n (ReverseChoiceHistory.state x n h)} =
      Freezing1.forwardHistoryWeight x n := by
  have hvalid := ReverseChoiceHistory.state_valid_of_legal x n hh hn
  simp only [hlen, Nat.sub_self] at hvalid
  have hmass := map_real_singleton_eq_card_mul (μ := Freezing1.ReverseStamped.treeLaw x n)
    (f := canonicalHistory x n) measurable_from_top
    (activeOrbit (Freezing1.activeCount x n).toNat (ReverseChoiceHistory.state x n h))
    (Freezing1.reverseHistoryWeight x n) hFibre (by
      intro F hF
      obtain ⟨h', hh', hlen', he⟩ := activeOrbit_supported_by_legal_histories x n hh hF
      have he' := ReverseChoiceHistory.treeLaw_real_singleton_of_legal x n hh'
        (hlen'.trans hlen) hn
      simpa only [he] using he')
  rw [card_activeOrbit_of_terminal_valid hvalid.1 hvalid.2,
    Freezing1.factorial_mul_reverseHistoryWeight_eq_forward x n hn] at hmass
  exact hmass

/-- The orbit calculation matches the atom of the actual forward choice law,
using the proved legality of the canonical replay. -/
theorem canonicalHistory_map_atom_eq_forward_of_ae_orbit (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {h : ReverseChoiceHistory.History} (hh : ReverseChoiceHistory.Legal x n h)
    (hlen : h.length = n)
    (hFibre : (canonicalHistory x n) ⁻¹' {canonicalHistory x n (ReverseChoiceHistory.state x n h)}
      =ᵐ[Freezing1.ReverseStamped.treeLaw x n]
        (activeOrbit (Freezing1.activeCount x n).toNat (ReverseChoiceHistory.state x n h) : Set Forest)) :
    ((Freezing1.ReverseStamped.treeLaw x n).map (canonicalHistory x n)).real
      {canonicalHistory x n (ReverseChoiceHistory.state x n h)} =
      (ForwardHistory.law x n).real {canonicalHistory x n (ReverseChoiceHistory.state x n h)} := by
  have hvalid := ReverseChoiceHistory.state_valid_of_legal x n hh hn
  simp only [hlen, Nat.sub_self] at hvalid
  have horder := state_canonicalOrder_of_legal x n hh hn
  have hlegal := canonicalHistory_legal hvalid.1 hvalid.2 horder
  have hforward := ForwardHistory.law_real_singleton_of_legal x hlegal
    (by simpa only [canonicalHistory_length] using hn)
  simp only [canonicalHistory_length] at hforward
  rw [hforward]
  exact canonicalHistory_map_atom_of_ae_orbit x n hn hh hlen hFibre

/-- Probability assembly from the explicit orbit identities. The final source
theorem discharges this fibre premise by the active-label comparison. -/
theorem map_treeLaw_canonicalHistory_eq_forward_of_ae_orbits
    (x : Freezing1.SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hFibres : ∀ (h : ReverseChoiceHistory.History), ReverseChoiceHistory.Legal x n h →
      h.length = n →
      (canonicalHistory x n) ⁻¹' {canonicalHistory x n (ReverseChoiceHistory.state x n h)}
        =ᵐ[Freezing1.ReverseStamped.treeLaw x n]
          (activeOrbit (Freezing1.activeCount x n).toNat (ReverseChoiceHistory.state x n h) : Set Forest)) :
    (Freezing1.ReverseStamped.treeLaw x n).map (canonicalHistory x n) = ForwardHistory.law x n := by
  have : IsProbabilityMeasure ((Freezing1.ReverseStamped.treeLaw x n).map (canonicalHistory x n)) :=
    Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance
  apply probability_eq_of_agree_on_positive_atoms
  intro a ha
  obtain ⟨F, ⟨h, hlen, hh, rfl⟩, himage⟩ :=
    exists_supported_preimage_of_map_atom_ne_zero measurable_from_top
      (ReverseChoiceHistory.treeLaw_ae_exists_legal_history x n hn) ha
  have hreal := canonicalHistory_map_atom_eq_forward_of_ae_orbit x n hn hh hlen (hFibres h hh hlen)
  rw [himage] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- Equality of canonical histories is the same finite orbit relation as
equality of canonical states, because every actual replay is legal. -/
theorem canonicalHistory_eq_iff_mem_activeOrbit_of_supported
    {x : Freezing1.SignSequence} {n : ℕ} {F G : Forest}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hF : TerminalSupported x n F) (hG : TerminalSupported x n G) :
    canonicalHistory x n G = canonicalHistory x n F ↔
      G ∈ activeOrbit (Freezing1.activeCount x n).toNat F := by
  constructor
  · intro he
    exact (canonicalForwardState_eq_iff_mem_activeOrbit_of_supported hn hF hG).mp
      (congrArg (ForwardHistory.state x) he)
  · intro hOrbit
    obtain ⟨hvF, htF, hoF, _⟩ := hF.invariants hn
    obtain ⟨hvG, htG, hoG, _⟩ := hG.invariants hn
    exact ForwardHistory.state_injective_on_legal x
      (canonicalHistory_legal hvG htG hoG) (canonicalHistory_legal hvF htF hoF)
      (by simp) ((canonicalForwardState_eq_iff_mem_activeOrbit_of_supported hn hF hG).mpr hOrbit)

/-- Outside the actual full-measure support no fibre assertion is needed. -/
theorem canonicalHistory_fibre_ae_activeOrbit
    {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hF : TerminalSupported x n F) :
    (canonicalHistory x n) ⁻¹' {canonicalHistory x n F}
      =ᵐ[Freezing1.ReverseStamped.treeLaw x n]
        (activeOrbit (Freezing1.activeCount x n).toNat F : Set Forest) := by
  filter_upwards [treeLaw_terminalSupported x n hn] with G hG
  apply propext
  exact canonicalHistory_eq_iff_mem_activeOrbit_of_supported hn hF hG

/-- The actual stamped reverse process, after forgetting only active names
and reading its records, has exactly the actual forward choice-history law. -/
theorem map_treeLaw_canonicalHistory_eq_forward
    (x : Freezing1.SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (Freezing1.ReverseStamped.treeLaw x n).map (canonicalHistory x n) = ForwardHistory.law x n := by
  apply map_treeLaw_canonicalHistory_eq_forward_of_ae_orbits x n hn
  intro h hh hlen
  exact canonicalHistory_fibre_ae_activeOrbit hn ⟨h, hlen, hh, rfl⟩

/-- **N01 (`thm:samelaw`).** The two actual tree laws agree after erasing the
numerical names of active reverse vertices and using incoming timestamps as
forward birth identifiers. The map preserves the complete finite graph,
root and frozen labels, as checked in `CanonicalForwardGraph`. Zero horizons
and a horizon exactly at extinction are included. -/
theorem forward_reverse_same_law (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    (Freezing1.ReverseStamped.treeLaw x n).map (canonicalForwardState x n) =
      Freezing1.Forward.treeLaw x n := by
  calc
    _ = ((Freezing1.ReverseStamped.treeLaw x n).map (canonicalHistory x n)).map
        (ForwardHistory.state x) := by
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl
    _ = _ := by
      rw [map_treeLaw_canonicalHistory_eq_forward x n hn, ForwardHistory.map_law_state]

end Freezing2.ReverseStamped
