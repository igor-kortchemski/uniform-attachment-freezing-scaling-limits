module

public import Freezing2.Probability.CoalescenceTransition
public import Freezing2.Probability.ReverseConditional
public import Freezing2.Probability.ReverseLabelBridge

/-!
# The coalescence time on the concrete reverse history

The random time is the largest source phase at which two present labels share a
component. Validity, persistence, and initial separation follow from the actual
transition law. Conditional survival then gives the exact product distribution,
including the original one-based paper labels and binomial notation. The
distinct-label premise repairs the documented source issue S02; the diagonal
is proved separately to equal the birth time.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseCoalescence

open Freezing1 Freezing2.ReverseHistory Freezing2.ForestCoalescence

abbrev Label := ℕ ⊕ ℕ

def commonBirth (n : ℕ) (u v : Label) : ℕ := min (Freezing1.birthTime n u) (Freezing1.birthTime n v)

/-- The common root represents an actual connected component on present labels. -/
def connectedAt (n : ℕ) (u v : Label) (i : ℕ) (ω : History) : Prop :=
  (forestAt n i ω).root u = (forestAt n i ω).root v

theorem measurable_connectedAt (n : ℕ) (u v : Label) (i : ℕ) :
    Measurable (connectedAt n u v i) :=
  (show Measurable (fun F : Forest ↦ F.root u = F.root v) from measurable_from_top).comp
    (measurable_pi_apply (n - i))

/-- Maximum connected source phase, restricted to phases where both labels have
been born. The zero default is justified on actual histories by terminal connectivity. -/
noncomputable def coalescenceTime (n : ℕ) (u v : Label) (ω : History) : ℕ :=
  ((Finset.Iic (commonBirth n u v)).filter (fun i ↦ connectedAt n u v i ω)).sup id

theorem coalescenceTime_le_commonBirth (n : ℕ) (u v : Label) (ω : History) :
    coalescenceTime n u v ω ≤ commonBirth n u v := by
  apply Finset.sup_le
  intro i hi
  exact Finset.mem_Iic.mp (Finset.mem_filter.mp hi).1

theorem le_coalescenceTime_of_connected {n : ℕ} {u v : Label} {i : ℕ} {ω : History}
    (hi : i ≤ commonBirth n u v) (hc : connectedAt n u v i ω) :
    i ≤ coalescenceTime n u v ω := by
  change id i ≤ ((Finset.Iic (commonBirth n u v)).filter
    (fun j ↦ connectedAt n u v j ω)).sup id
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hi, hc⟩)

theorem connectedAt_coalescenceTime {n : ℕ} {u v : Label} {ω : History}
    (hzero : connectedAt n u v 0 ω) :
    connectedAt n u v (coalescenceTime n u v ω) ω := by
  have hne : ((Finset.Iic (commonBirth n u v)).filter
      (fun i ↦ connectedAt n u v i ω)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Nat.zero_le _), hzero⟩⟩
  have hmem := Finset.sup_mem_of_nonempty (f := id) hne
  have hmem' : coalescenceTime n u v ω ∈
      (Finset.Iic (commonBirth n u v)).filter (fun i ↦ connectedAt n u v i ω) := by
    simpa only [Set.image_id, Finset.mem_coe, coalescenceTime] using hmem
  exact (Finset.mem_filter.mp hmem').2

/-- The diagonal is the birth phase, rather than a two-component merger time. -/
@[simp] theorem coalescenceTime_self (n : ℕ) (u : Label) (ω : History) :
    coalescenceTime n u u ω = Freezing1.birthTime n u := by
  apply le_antisymm
  · simpa [commonBirth] using coalescenceTime_le_commonBirth n u u ω
  · apply le_coalescenceTime_of_connected
    · simp [commonBirth]
    · rfl

theorem measurable_coalescenceTime (n : ℕ) (u v : Label) :
    Measurable (coalescenceTime n u v) := by
  have hm (s : Finset ℕ) : Measurable (fun ω : History ↦
      s.sup (fun i ↦ if connectedAt n u v i ω then i else 0)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa only [Finset.sup_insert, Pi.sup_apply] using
        (Measurable.ite (measurable_connectedAt n u v i).setOf measurable_const
          measurable_const).max ih
  have heq : coalescenceTime n u v = fun ω : History ↦
      (Finset.Iic (commonBirth n u v)).sup
        (fun i ↦ if connectedAt n u v i ω then i else 0) := by
    funext ω
    simp [coalescenceTime, Finset.sup_ite]
    rfl
  rw [heq]
  exact hm _

/-- The precise direction of component persistence in decreasing source time. -/
def CoarseningHistory (n : ℕ) (ω : History) : Prop :=
  ∀ i j, i ≤ j → j ≤ n → Coarsens (forestAt n j ω) (forestAt n i ω)

/-- Every consecutive pair of the actual trajectory preserves vertices and
component connectivity, including the held-fixed tail after time `n`. -/
theorem jointLaw_step_coarsens (x : SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂jointLaw x n, ∀ k, Coarsens (ω k) (ω (k + 1)) := by
  apply ae_all_iff.mpr
  intro k
  apply jointLaw_ae_transition x n k measurableSet_coarsens
  apply Eventually.of_forall
  intro ω
  apply (ae_iff_prob_eq_one measurable_from_top).mp
  by_cases hk : k < n
  · simpa only [stepKernel, Kernel.coe_mk, ite_eq_left hk, Set.mem_ofPred_eq] using
      transitionLaw_ae_coarsens x (n - (k + 1)) (ω k)
  · simp only [stepKernel, Kernel.coe_mk, ite_eq_right hk]
    exact (ae_dirac_iff (by trivial)).mpr (Coarsens.refl _)

/-- Connectivity is monotone simultaneously over all source phases. -/
theorem jointLaw_coarsening (x : SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂jointLaw x n, CoarseningHistory n ω := by
  filter_upwards [jointLaw_step_coarsens x n] with ω hω
  have hchain : ∀ a b, a ≤ b → Coarsens (ω a) (ω b) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact Coarsens.refl _
    | succ b hab ih => exact ih.trans (hω b)
  intro i j hij hjn
  exact hchain (n - j) (n - i) (by omega)

theorem connectedAt_iff_le_coalescenceTime {n : ℕ} {u v : Label} {ω : History}
    (hmono : CoarseningHistory n ω) (hb : commonBirth n u v ≤ n)
    (hmem : ∀ i ≤ commonBirth n u v,
      u ∈ (forestAt n i ω).vertices ∧ v ∈ (forestAt n i ω).vertices)
    (hzero : connectedAt n u v 0 ω) {i : ℕ} (hi : i ≤ commonBirth n u v) :
    connectedAt n u v i ω ↔ i ≤ coalescenceTime n u v ω := by
  constructor
  · exact le_coalescenceTime_of_connected hi
  · intro hic
    have hcb := coalescenceTime_le_commonBirth n u v ω
    have hc := hmono i (coalescenceTime n u v ω) hic (hcb.trans hb)
    exact hc.2 u (hmem _ hcb).1 v (hmem _ hcb).2 (connectedAt_coalescenceTime hzero)

/-- A strict interior coalescence phase is exactly a first-merger transition. -/
theorem coalescenceTime_eq_iff {n : ℕ} {u v : Label} {ω : History}
    (hmono : CoarseningHistory n ω) (hb : commonBirth n u v ≤ n)
    (hmem : ∀ i ≤ commonBirth n u v,
      u ∈ (forestAt n i ω).vertices ∧ v ∈ (forestAt n i ω).vertices)
    (hzero : connectedAt n u v 0 ω) {c : ℕ} (hc : c < commonBirth n u v) :
    coalescenceTime n u v ω = c ↔
      connectedAt n u v c ω ∧ ¬connectedAt n u v (c + 1) ω := by
  rw [connectedAt_iff_le_coalescenceTime hmono hb hmem hzero (by omega),
    connectedAt_iff_le_coalescenceTime hmono hb hmem hzero (by omega)]
  omega

theorem birthTime_le_horizon {x : SignSequence} {n : ℕ} {u : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) : Freezing1.birthTime n u ≤ n := by
  cases u with
  | inl j => rfl
  | inr i =>
    have hi : i < n := (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hu)).1
      |> Finset.mem_range.mp
    exact hi.le

theorem commonBirth_le_horizon {x : SignSequence} {n : ℕ} {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) : commonBirth n u v ≤ n :=
  (min_le_left _ _).trans (birthTime_le_horizon hu)

/-- The deterministic birth rule supplies simultaneous membership at every
phase appearing in the coalescence maximum. -/
theorem jointLaw_members {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ i ≤ commonBirth n u v,
      u ∈ (forestAt n i ω).vertices ∧ v ∈ (forestAt n i ω).vertices := by
  filter_upwards [jointLaw_forestAt_valid x n hn] with ω hω
  intro i hi
  have hin : i ≤ n := hi.trans (commonBirth_le_horizon hu)
  rw [(hω i hin).vertices_eq]
  exact ⟨(Reverse.mem_phaseLabels_iff_birthTime hin hu).mpr (hi.trans (min_le_left _ _)),
    (Reverse.mem_phaseLabels_iff_birthTime hin hv).mpr (hi.trans (min_le_right _ _))⟩

/-- The terminal forest connects every pair of labels, justifying the maximum's
nonempty set even at the extinction horizon. -/
theorem jointLaw_connected_zero {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, connectedAt n u v 0 ω := by
  filter_upwards [jointLaw_forestAt_valid x n hn, jointLaw_members hn hu hv] with ω hω hmem
  have hc : (forestAt n 0 ω).roots.card = 1 := by
    simpa using (hω 0 (Nat.zero_le n)).roots_card
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc
  have hru := (forestAt n 0 ω).root_mem_roots (hmem 0 (Nat.zero_le _)).1
  have hrv := (forestAt n 0 ω).root_mem_roots (hmem 0 (Nat.zero_le _)).2
  rw [hr, Finset.mem_singleton] at hru hrv
  exact hru.trans hrv.symm

/-- A birth before the terminal horizon belongs to its unique frozen label. -/
theorem label_of_birth_lt {x : SignSequence} {n : ℕ} {u : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (h : Freezing1.birthTime n u < n) :
    u = Sum.inr (Freezing1.birthTime n u) ∧
      x (Freezing1.birthTime n u + 1) = false := by
  cases u with
  | inl j => simp [Freezing1.birthTime] at h
  | inr i => exact ⟨rfl, (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hu)).2⟩

/-- At the terminal phase all initial components are singletons. -/
theorem jointLaw_distinct_top (x : SignSequence) (n : ℕ) {u v : Label} (huv : u ≠ v) :
    ∀ᵐ ω ∂jointLaw x n, ¬connectedAt n u v n ω := by
  have h : ∀ᵐ F ∂Measure.dirac (Reverse.initial x n), F.root u ≠ F.root v := by
    simpa [Reverse.initial, RootedForest.isolated] using huv
  rw [← jointLaw_map_zero x n] at h
  simpa only [connectedAt, forestAt, Nat.sub_self] using
    ae_of_ae_map (measurable_pi_apply 0).aemeasurable h

/-- At a frozen vertex's birth, it is separated from every vertex born earlier
in construction time (that is, at a strictly larger source phase). -/
theorem jointLaw_distinct_at_smaller_birth {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (hb : Freezing1.birthTime n u < Freezing1.birthTime n v) :
    ∀ᵐ ω ∂jointLaw x n, ¬connectedAt n u v (Freezing1.birthTime n u) ω := by
  let b := Freezing1.birthTime n u
  let k := n - (b + 1)
  have hbn : b < n := hb.trans_le (birthTime_le_horizon hv)
  have hkn : k < n := by dsimp [k]; omega
  have hphase : n - (k + 1) = b := by dsimp [k]; omega
  have hnext : k + 1 = n - b := by dsimp [k]; omega
  obtain ⟨hu', hx⟩ := label_of_birth_lt hu hbn
  have hxb : x (b + 1) = false := hx
  have hE : MeasurableSet {p : Forest × Forest | p.2.root u ≠ p.2.root v} :=
    ((show Measurable (fun F : Forest ↦ F.root u ≠ F.root v) from
      measurable_from_top).comp measurable_snd).setOf
  have hevent := jointLaw_ae_transition x n k hE (by
    filter_upwards [jointLaw_forestAt_valid x n hn] with ω hω
    have hF : Reverse.ValidAt x n (b + 1) (ω k) := hω (b + 1) (by omega)
    have hvF : v ∈ (ω k).vertices := by
      rw [hF.vertices_eq]
      exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) hv).mpr (by omega)
    have hfresh : Sum.inr b ∉ (ω k).vertices := by
      rw [hF.vertices_eq]
      exact Reverse.fresh_freezing_label x n b
    have hne : (Reverse.insertLabel (ω k) b).root u ≠
        (Reverse.insertLabel (ω k) b).root v := by
      rw [hu']
      exact insertLabel_root_new_ne_old (ω k) b hfresh hvF
    apply (ae_iff_prob_eq_one measurable_from_top).mp
    simp only [stepKernel, Kernel.coe_mk, ite_eq_left hkn, hphase,
      Reverse.transitionLaw, hxb, Bool.false_eq_true, ↓reduceIte]
    exact (ae_dirac_iff (by trivial)).mpr hne)
  simpa only [Set.mem_ofPred_eq, connectedAt, forestAt, hnext] using hevent

/-- Distinct labels occupy distinct components when both have just become
present. This supplies the initial condition for the survival-product recursion. -/
theorem jointLaw_distinct_at_commonBirth {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) :
    ∀ᵐ ω ∂jointLaw x n, ¬connectedAt n u v (commonBirth n u v) ω := by
  by_cases htop : commonBirth n u v = n
  · simpa only [htop] using jointLaw_distinct_top x n huv
  have hbn : commonBirth n u v < n := lt_of_le_of_ne (commonBirth_le_horizon hu) htop
  have hne : Freezing1.birthTime n u ≠ Freezing1.birthTime n v := by
    intro heq
    have hbu : Freezing1.birthTime n u < n := by simpa [commonBirth, heq] using hbn
    have hbv : Freezing1.birthTime n v < n := by omega
    have heu := (label_of_birth_lt hu hbu).1
    have hev := (label_of_birth_lt hv hbv).1
    apply huv
    rw [heu, hev, heq]
  rcases lt_or_gt_of_ne hne with hb | hb
  · simpa only [commonBirth, min_eq_left hb.le] using
      jointLaw_distinct_at_smaller_birth hn hu hv hb
  · have h := jointLaw_distinct_at_smaller_birth hn hv hu hb
    filter_upwards [h] with ω hω
    simpa only [commonBirth, min_eq_right hb.le, connectedAt, ne_eq, eq_comm] using hω

/-- The merger hazard at source step `i`, derived from the actual transition law. -/
noncomputable def coalescenceHazard (x : SignSequence) (i : ℕ) : ℝ :=
  if x i then 2 / ((Freezing1.activeCount x i : ℝ) * ((Freezing1.activeCount x i : ℝ) - 1)) else 0

noncomputable def separatedIndicator (n : ℕ) (u v : Label) (i : ℕ) : History → ℝ :=
  {ω | ¬connectedAt n u v i ω}.indicator (fun _ ↦ 1)

theorem measurable_separatedIndicator (n : ℕ) (u v : Label) (i : ℕ) :
    Measurable (separatedIndicator n u v i) :=
  measurable_const.indicator (measurable_connectedAt n u v i).not.setOf

theorem integrable_separatedIndicator (x : SignSequence) (n : ℕ) (u v : Label) (i : ℕ) :
    Integrable (separatedIndicator n u v i) (jointLaw x n) :=
  (integrable_const (1 : ℝ)).indicator (measurable_connectedAt n u v i).not.setOf

/-- Conditional survival of two still distinct components, given the entire
exposed history. The zero value after a merger is included in the same formula. -/
theorem conditional_separatedIndicator {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    {i : ℕ} (hi : i < commonBirth n u v) :
    (jointLaw x n)[separatedIndicator n u v i |
      Filtration.piLE (X := fun _ ↦ Forest) (n - (i + 1))] =ᵐ[jointLaw x n]
      fun ω ↦ (1 - coalescenceHazard x (i + 1)) * separatedIndicator n u v (i + 1) ω := by
  let k := n - (i + 1)
  have hin : i < n := hi.trans_le (commonBirth_le_horizon hu)
  have hkn : k < n := by dsimp [k]; omega
  have hphase : n - (k + 1) = i := by dsimp [k]; omega
  have hnext : k + 1 = n - i := by dsimp [k]; omega
  let E : Set (Forest × Forest) := {p | p.2.root u ≠ p.2.root v}
  have hE : MeasurableSet E :=
    ((show Measurable (fun F : Forest ↦ F.root u ≠ F.root v) from
      measurable_from_top).comp measurable_snd).setOf
  have hleft : transitionIndicator E k = separatedIndicator n u v i := by
    funext ω
    simp only [transitionIndicator, transitionEvent, E, separatedIndicator,
      connectedAt, forestAt, hnext]
    rfl
  have hcond := conditional_transition_indicator x n k hE
  rw [hleft] at hcond
  refine hcond.trans ?_
  filter_upwards [jointLaw_forestAt_valid x n hn, jointLaw_members hn hu hv] with ω hvalid hmem
  have hF : Reverse.ValidAt x n (i + 1) (ω k) := hvalid (i + 1) (by omega)
  have huF : u ∈ (ω k).vertices := (hmem (i + 1) (by omega)).1
  have hvF : v ∈ (ω k).vertices := (hmem (i + 1) (by omega)).2
  change (stepKernel x n k (ω k)).real {F | F.root u ≠ F.root v} = _
  simp only [stepKernel, Kernel.coe_mk, ite_eq_left hkn, hphase]
  change (Reverse.transitionLaw x i (ω k)).real {F | F.root u = F.root v}ᶜ = _
  rw [probReal_compl_eq_one_sub (by trivial), transitionLaw_root_eq_probability hn hin hF huF hvF]
  by_cases hroot : (ω k).root u = (ω k).root v
  · simp [hroot, separatedIndicator, connectedAt, forestAt, k]
  · simp [hroot, separatedIndicator, connectedAt, forestAt, k,
      coalescenceHazard]

/-- The marginal probability of remaining in different components at phase `i`. -/
noncomputable def separationProbability (x : SignSequence) (n : ℕ) (u v : Label) (i : ℕ) : ℝ :=
  (jointLaw x n).real {ω | ¬connectedAt n u v i ω}

theorem integral_separatedIndicator (x : SignSequence) (n : ℕ) (u v : Label) (i : ℕ) :
    (∫ ω, separatedIndicator n u v i ω ∂jointLaw x n) = separationProbability x n u v i :=
  integral_indicator_one (measurable_connectedAt n u v i).not.setOf

/-- Integrating the proved conditional law gives the survival recursion. -/
theorem separationProbability_recursion {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    {i : ℕ} (hi : i < commonBirth n u v) :
    separationProbability x n u v i =
      (1 - coalescenceHazard x (i + 1)) * separationProbability x n u v (i + 1) := by
  rw [← integral_separatedIndicator x n u v i,
    ← integral_condExp (Filtration.piLE.le (n - (i + 1))),
    integral_congr_ae (conditional_separatedIndicator hn hu hv hi), integral_const_mul,
    integral_separatedIndicator]

/-- Initially distinct labels have survival probability one at their common birth. -/
theorem separationProbability_commonBirth {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) : separationProbability x n u v (commonBirth n u v) = 1 := by
  have h := (ae_iff_prob_eq_one (measurable_connectedAt n u v _).not).mp
    (jointLaw_distinct_at_commonBirth hn hu hv huv)
  change ((jointLaw x n) {ω | ¬connectedAt n u v (commonBirth n u v) ω}).toReal = 1
  rw [h, ENNReal.toReal_one]

/-- The survival product is obtained by finite recursion on the actual joint law. -/
theorem separationProbability_eq_product {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) {i : ℕ} (hi : i ≤ commonBirth n u v) :
    separationProbability x n u v i =
      ∏ j ∈ Finset.Ioc i (commonBirth n u v), (1 - coalescenceHazard x j) := by
  induction hi using Nat.decreasingInduction with
  | self => simp [separationProbability_commonBirth hn hu hv huv]
  | of_succ i hi ih =>
    rw [separationProbability_recursion hn hu hv hi, ih,
      ← Finset.prod_Ioc_consecutive (fun j ↦ 1 - coalescenceHazard x j)
        (Nat.le_succ i) hi, Nat.Ioc_succ_singleton, Finset.prod_singleton]

/-- The maximum characterization holds simultaneously at every common phase
of almost every actual history. -/
theorem jointLaw_connected_iff_le_coalescenceTime {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ i ≤ commonBirth n u v,
      connectedAt n u v i ω ↔ i ≤ coalescenceTime n u v ω := by
  filter_upwards [jointLaw_coarsening x n, jointLaw_members hn hu hv,
    jointLaw_connected_zero hn hu hv] with ω hm hv' hzero
  intro i hi
  exact connectedAt_iff_le_coalescenceTime hm (commonBirth_le_horizon hu) hv' hzero hi

/-- Distinct labels merge strictly after their common birth in construction time. -/
theorem jointLaw_coalescenceTime_lt_commonBirth {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) :
    ∀ᵐ ω ∂jointLaw x n, coalescenceTime n u v ω < commonBirth n u v := by
  filter_upwards [jointLaw_connected_iff_le_coalescenceTime hn hu hv,
    jointLaw_distinct_at_commonBirth hn hu hv huv] with ω hω hne
  have hnot : ¬commonBirth n u v ≤ coalescenceTime n u v ω :=
    fun h ↦ hne ((hω _ le_rfl).mpr h)
  omega

/-- The actual first-merger event at each strict common phase. -/
theorem jointLaw_coalescenceTime_eq_iff {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ c < commonBirth n u v,
      coalescenceTime n u v ω = c ↔
        connectedAt n u v c ω ∧ ¬connectedAt n u v (c + 1) ω := by
  filter_upwards [jointLaw_connected_iff_le_coalescenceTime hn hu hv] with ω hω
  intro c hc
  rw [hω c (by omega), hω (c + 1) (by omega)]
  omega

/-- The coalescence tail is the exact survival product. -/
theorem coalescenceTime_lt_probability {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) {i : ℕ} (hi : i ≤ commonBirth n u v) :
    (jointLaw x n).real {ω | coalescenceTime n u v ω < i} =
      ∏ j ∈ Finset.Ioc i (commonBirth n u v), (1 - coalescenceHazard x j) := by
  rw [← separationProbability_eq_product hn hu hv huv hi]
  apply measureReal_congr
  filter_upwards [jointLaw_connected_iff_le_coalescenceTime hn hu hv] with ω hω
  apply propext
  rw [hω i hi]
  omega

/-- Corrected source N04: the first-merger mass is its proved one-step hazard
times the survival product, for distinct labels. Freezing phases have mass zero. -/
theorem coalescenceTime_probability {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) {c : ℕ} (hc : c < commonBirth n u v) :
    (jointLaw x n).real {ω | coalescenceTime n u v ω = c} =
      coalescenceHazard x (c + 1) *
        ∏ j ∈ Finset.Ioc (c + 1) (commonBirth n u v), (1 - coalescenceHazard x j) := by
  have hE : MeasurableSet {ω : History | coalescenceTime n u v ω = c} :=
    (measurable_coalescenceTime n u v).eq_const c |>.setOf
  have hind : ({ω | coalescenceTime n u v ω = c}.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[jointLaw x n] fun ω ↦ separatedIndicator n u v (c + 1) ω -
        separatedIndicator n u v c ω := by
    filter_upwards [jointLaw_connected_iff_le_coalescenceTime hn hu hv,
      jointLaw_coalescenceTime_eq_iff hn hu hv] with ω hconn hfirst
    have hdown : connectedAt n u v (c + 1) ω → connectedAt n u v c ω := by
      rw [hconn (c + 1) (by omega), hconn c (by omega)]
      omega
    have heq := hfirst c hc
    by_cases hci : connectedAt n u v c ω <;>
      by_cases hcn : connectedAt n u v (c + 1) ω <;>
        simp_all [separatedIndicator]
    omega
  calc
    _ = ∫ ω, ({ω | coalescenceTime n u v ω = c}.indicator (fun _ ↦ (1 : ℝ))) ω
        ∂jointLaw x n := (integral_indicator_one hE).symm
    _ = ∫ ω, separatedIndicator n u v (c + 1) ω - separatedIndicator n u v c ω
        ∂jointLaw x n := integral_congr_ae hind
    _ = separationProbability x n u v (c + 1) - separationProbability x n u v c := by
      rw [integral_sub (integrable_separatedIndicator x n u v (c + 1))
        (integrable_separatedIndicator x n u v c), integral_separatedIndicator,
        integral_separatedIndicator]
    _ = _ := by
      rw [separationProbability_recursion hn hu hv hc,
        separationProbability_eq_product hn hu hv huv (Nat.succ_le_of_lt hc)]
      ring

/-- The algebraic hazard agrees exactly with the manuscript's binomial notation. -/
theorem coalescenceHazard_eq_inv_choose {x : SignSequence} {n i : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i ≤ n) (hx : x i = true) :
    coalescenceHazard x i = 1 / ((Freezing1.activeCount x i).toNat.choose 2 : ℝ) := by
  have hiτ : (i : ℕ∞) ≤ extinctionTime x :=
    le_trans (by exact_mod_cast hi) hn
  have hc : ((Freezing1.activeCount x i).toNat : ℝ) =
      (Freezing1.activeCount x i : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hiτ)
  rw [coalescenceHazard, hx]
  simp only [↓reduceIte]
  rw [Nat.cast_choose_two, hc, one_div, inv_div]

/-- Corrected N04 in the displayed binomial notation and with only up steps
retained in the survival product. The distinct-label premise repairs S02. -/
theorem coalescenceTime_probability_choose {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) {c : ℕ} (hc : c < commonBirth n u v) (hup : x (c + 1) = true) :
    (jointLaw x n).real {ω | coalescenceTime n u v ω = c} =
      (1 / ((Freezing1.activeCount x (c + 1)).toNat.choose 2 : ℝ)) *
        ∏ j ∈ (Finset.Ioc (c + 1) (commonBirth n u v)).filter (fun j ↦ x j = true),
          (1 - 1 / ((Freezing1.activeCount x j).toNat.choose 2 : ℝ)) := by
  rw [coalescenceTime_probability hn hu hv huv hc,
    coalescenceHazard_eq_inv_choose hn
      ((Nat.succ_le_of_lt hc).trans (commonBirth_le_horizon hu)) hup]
  congr 1
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  have hjn : j ≤ n := (Finset.mem_Ioc.mp hj).2.trans (commonBirth_le_horizon hu)
  by_cases hx : x j = true
  · rw [ite_eq_left hx, coalescenceHazard_eq_inv_choose hn hjn hx]
  · simp [coalescenceHazard, hx]

/-- The coalescence time for the paper's displayed one-based vertex labels. -/
noncomputable def sourceCoalescenceTime (n : ℕ) (u v : VertexLabel) : History → ℕ :=
  coalescenceTime n (toCompanionLabel u) (toCompanionLabel v)

@[simp] theorem sourceCoalescenceTime_self (n : ℕ) (u : VertexLabel) (ω : History) :
    sourceCoalescenceTime n u u ω = Freezing2.birthTime n u := by
  simp [sourceCoalescenceTime]

theorem measurable_sourceCoalescenceTime (n : ℕ) (u v : VertexLabel) :
    Measurable (sourceCoalescenceTime n u v) :=
  measurable_coalescenceTime n (toCompanionLabel u) (toCompanionLabel v)

/-- Corrected N04 for the original integer schedule and one-based paper labels.
The probability is taken under the constructed reverse joint history. -/
theorem sourceCoalescenceTime_probability (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x)) {u v : VertexLabel}
    (hu : u ∈ Freezing2.vertexLabels x n) (hv : v ∈ Freezing2.vertexLabels x n)
    (huv : u ≠ v) {c : ℕ}
    (hc : c < min (Freezing2.birthTime n u) (Freezing2.birthTime n v)) (hup : x (c + 1) = 1) :
    (jointLaw (companionSchedule x) n).real {ω | sourceCoalescenceTime n u v ω = c} =
      (1 / ((Freezing2.activeCount x (c + 1)).toNat.choose 2 : ℝ)) *
        ∏ j ∈ (Finset.Ioc (c + 1)
          (min (Freezing2.birthTime n u) (Freezing2.birthTime n v))).filter (fun j ↦ x j = 1),
          (1 - 1 / ((Freezing2.activeCount x j).toNat.choose 2 : ℝ)) := by
  have huv' : toCompanionLabel u ≠ toCompanionLabel v := by
    intro h
    apply huv
    have h' := congrArg fromCompanionLabel h
    simpa only [from_toCompanionLabel hu, from_toCompanionLabel hv] using h'
  have hc' : c < commonBirth n (toCompanionLabel u) (toCompanionLabel v) := by
    simpa only [commonBirth, companion_birthTime] using hc
  have hup' : companionSchedule x (c + 1) = true := by simp [companionSchedule, hup]
  have h := coalescenceTime_probability_choose hn (toCompanionLabel_mem x hx hu)
    (toCompanionLabel_mem x hx hv) huv' hc' hup'
  simpa only [sourceCoalescenceTime, commonBirth, companion_birthTime,
    companion_activeCount x hx, companionSchedule, decide_eq_true_eq] using h

end Freezing2.ReverseCoalescence
