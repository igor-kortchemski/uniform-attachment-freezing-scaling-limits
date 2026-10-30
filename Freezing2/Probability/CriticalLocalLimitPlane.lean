module

public import Freezing2.Probability.CriticalLocalLimit

/-!
# The critical local limit `eq:cv locale` for plane forests

This file completes the corrected local limit of `CriticalLocalLimit.lean` (inventory N12a,
display `eq:cv locale` of `attachement-uniforme-2-final.tex`) in the source's plane form, with
limit the density `g_{r,k}(F₀, ·)` itself.

## The plane structure of the discrete genealogy

The source orders the two children of each merge of the sampled genealogy "taking into account
which one of the two roots remains the root of the tree after the coalescence". We use the
convention that the left child (the first in the plane forest `F₀ ∈ 𝔉⁺_{r,k}`) is the subtree
whose root survives. This is read off the actual reverse forests: at the merge phase, the
component of a particle below the left child keeps its root (`planeForestEvent`, `leftRep`). Any
fixed convention gives the same law, since both orientations of a merge have the same
probability.

* `transitionLaw_orientedMerge`: under the actual transition law, the oriented merge of two
  tracked components has probability `1 / (S (S - 1))`, half of the merge hazard
  (from `transitionLaw_orderedPair`).
* `jointLaw_real_inter_transitionEvent`, `jointLaw_chainState_orientedStep`,
  `jointLaw_orientedPath`: the path law of the tracked chain with oriented merges, from the
  conditional law of a transition given the whole past.
* `jointLaw_planePatternEvent`: prescribing the orientations divides the pattern probability by
  `2^m`.
* `leftRep_mem_mergedSet`: alignment with `histForest`, whose vertex of the `s`-th merge has as
  children the two components it merges (`DAdm.leafSet_histForest`, `Fits.leafSet_kids`).
* `scaledPlaneProb_eq`: the rescaled probability of the plane forest `F₀` is `2^{-(k-1-r)}` times
  that of `F₀` up to child orders.

## Main results

* `critical_local_limit_plane`: under the source hypotheses alone (no measurability of `g`), for
  every cutoff `ε > 0` the laws of `scaledPlaneProb` and of the source's exact quantity
  `sourcePlaneProb` (`(n/2)^(2k-1-r)` times the probability including the choice of the sampled
  vertices) at the source's samples converge weakly as `n → ∞`, the limits converge as
  `ε → 0⁺`, and the final limit is the law of `g_{r,k}(F₀, B, C)` (`sourceDensity`) at
  independent uniform times.
* `critical_local_limit_forest_of_profile`: the non-plane forest form without measurability.
* `ae_patternEvent_iff_coalescenceTimes`: almost surely, the tracked-chain event says that the
  coalescence times `coal_n(V_j, V_l)` of the sampled vertices (`sourceCoalescenceTime`),
  truncated below the cutoff, are those prescribed by the pattern.

## Ingredients

* `tendsto_map_mul_of_tendsto`: Slutsky's lemma for a deterministic factor tending to one, used
  for the source's normalization `(n/2)^k / N^k → 1` (`vertexFactor`).
* `exists_measurable_modification` and the congruence lemmas `limitLocalLaw_congr`,
  `limitFun_congr`, `limitFun0_congr`, `ae_sourceDensity_congr` remove the measurability of `g`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Freezing2.CriticalLocalLimit

open Freezing1 TrackedGenealogy TrackedClusters ReverseCoalescence ReverseHistory
  CriticalGenealogy CoalescentDensity

variable {k m : ℕ}

/-! ### A Markov step for events of two consecutive forests -/

/-- **Relational Markov step.** If, almost surely on a past event `A`, the next forest falls,
together with the current one, in `E` with deterministic probability `q`, then `A` followed by
this transition event has probability `P(A) q`. -/
theorem jointLaw_real_inter_transitionEvent (x : SignSequence) (n : ℕ) {N : ℕ} (hN : N < n)
    {A : Set History} (hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N] A)
    {E : Set (Reverse.Forest × Reverse.Forest)} (hE : MeasurableSet E) (q : ℝ)
    (hq : ∀ᵐ ω ∂jointLaw x n, ω ∈ A →
      (Reverse.transitionLaw x (n - (N + 1)) (ω N)).real {F | (ω N, F) ∈ E} = q) :
    (jointLaw x n).real (A ∩ transitionEvent E N) = (jointLaw x n).real A * q := by
  let μ := jointLaw x n
  have hc := conditional_transition_indicator x n N hE
  have hi := integrable_transitionIndicator hE N μ
  have he := setIntegral_condExp ((Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N) hi hA
  have hAmeas : MeasurableSet A := (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N A hA
  have hstep : ∀ ω : History, stepKernel x n N (ω N) =
      Reverse.transitionLaw x (n - (N + 1)) (ω N) := fun ω ↦ by
    simp only [stepKernel, ite_eq_left hN]
    rfl
  have h1 : ∫ ω in A, (μ[transitionIndicator E N |
      Filtration.piLE (X := fun _ ↦ Reverse.Forest) N]) ω ∂μ =
      ∫ ω in A, (Reverse.transitionLaw x (n - (N + 1)) (ω N)).real {F | (ω N, F) ∈ E} ∂μ :=
    setIntegral_congr_ae hAmeas (hc.mono fun ω h _ ↦ by rw [h]; dsimp only; rw [hstep])
  have h2 : ∫ ω in A, (Reverse.transitionLaw x (n - (N + 1)) (ω N)).real {F | (ω N, F) ∈ E} ∂μ =
      ∫ _ω in A, q ∂μ := setIntegral_congr_ae hAmeas hq
  have h3 : ∫ ω in A, transitionIndicator E N ω ∂μ = μ.real (A ∩ transitionEvent E N) := by
    rw [transitionIndicator, setIntegral_indicator (measurableSet_transitionEvent hE N),
      setIntegral_const, smul_eq_mul, mul_one]
  rw [← h3, ← he, h1, h2, setIntegral_const, smul_eq_mul, mul_comm]

/-! ### The oriented merge -/

variable {n p : ℕ} {u : Fin k → ℕ ⊕ ℕ} {x : SignSequence}

theorem mergeState_comm (s : ConnState k) (j₀ l₀ : Fin k) :
    mergeState s j₀ l₀ = mergeState s l₀ j₀ := by
  funext j l
  simp only [mergeState]
  cases s j l <;> cases s j j₀ <;> cases s l l₀ <;> cases s j l₀ <;> cases s l j₀ <;> rfl

theorem trackedState_symm (F : Reverse.Forest) (j l : Fin k) :
    trackedState n p u F j l = trackedState n p u F l j := by
  classical
  unfold trackedState
  by_cases h : Born n p u j ∧ Born n p u l
  · have h' : Born n p u l ∧ Born n p u j := ⟨h.2, h.1⟩
    simp only [h, and_self, ↓reduceIte, eq_comm]
  · have h' : ¬ (Born n p u l ∧ Born n p u j) := fun h' ↦ h ⟨h'.2, h'.1⟩
    simp only [h, h', ↓reduceIte, eq_comm]

theorem trackedState_refl (F : Reverse.Forest) (j : Fin k) : trackedState n p u F j j = true := by
  classical
  unfold trackedState
  split_ifs <;> simp

/-- **The oriented merge.** At an attachment step merging the components of `j₀` and `l₀`,
the probability that the components merge and that the component of a label `j` of one of them
keeps its root is `1 / (S (S - 1))`, half of the merge hazard. -/
theorem transitionLaw_orientedMerge (hn : (n : ℕ∞) ≤ extinctionTime x) (hp : p < n)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) {F : Reverse.Forest}
    (hFv : Reverse.ValidAt x n (p + 1) F) (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices)
    (hx : x (p + 1) = true) {j₀ l₀ j : Fin k} (hj₀ : Born n (p + 1) u j₀)
    (hl₀ : Born n (p + 1) u l₀) (hsep : trackedState n (p + 1) u F j₀ l₀ = false)
    (hj : trackedState n (p + 1) u F j j₀ = true ∨ trackedState n (p + 1) u F j l₀ = true) :
    (Reverse.transitionLaw x p F).real {G | trackedState n p u G =
        mergeState (trackedState n (p + 1) u F) j₀ l₀ ∧ G.root (u j) = F.root (u j)} =
      1 / 2 * chainStep x n p u (trackedState n (p + 1) u F)
        (mergeState (trackedState n (p + 1) u F) j₀ l₀) := by
  classical
  -- reduce to `j` in the component of `j₀`
  wlog hjj : trackedState n (p + 1) u F j j₀ = true generalizing j₀ l₀
  · have hj' : trackedState n (p + 1) u F j l₀ = true := by
      rcases hj with h | h
      · exact absurd h hjj
      · exact h
    have hsep' : trackedState n (p + 1) u F l₀ j₀ = false := by
      rw [trackedState_symm]; exact hsep
    have := this hl₀ hj₀ hsep' (Or.inl hj') hj'
    rwa [mergeState_comm] at this
  set s := trackedState n (p + 1) u F with hsdef
  have hborn := born_iff_of_attachment hu hp hx
  have hjb : Born n (p + 1) u j := by
    by_contra hjn
    by_cases hjj₀ : j = j₀
    · exact hjn (hjj₀ ▸ hj₀)
    · have := trackedState_respects F j j₀ (fun h ↦ hjn h.1)
      rw [← hsdef, hjj] at this
      simp [hjj₀] at this
  set rA := F.root (u j₀) with hrA
  set rB := F.root (u l₀) with hrB
  have hrj : F.root (u j) = rA := (conn_of_trackedState_eq hsdef.symm j j₀ hjb hj₀).mpr hjj
  have hAB : rA ≠ rB := fun h ↦ by
    have := (conn_of_trackedState_eq hsdef.symm j₀ l₀ hj₀ hl₀).mp h
    rw [hsep] at this
    exact Bool.false_ne_true this
  have hrAm : rA ∈ F.roots := F.root_mem_roots (hmem j₀ hj₀)
  have hrBm : rB ∈ F.roots := F.root_mem_roots (hmem l₀ hl₀)
  have htwo := two_le_roots_of_attachment hn hp hFv hx
  have hm : mergeState s j₀ l₀ j₀ l₀ = true := by
    simp [mergeState, hsdef, trackedState_refl]
  -- the event is the ordered join `(rA, rB)`
  have hev : (Reverse.transitionLaw x p F) {G | trackedState n p u G = mergeState s j₀ l₀ ∧
      G.root (u j) = F.root (u j)} = (Reverse.transitionLaw x p F) {G | G.root rB = rA} := by
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    apply joinLaw_congr_offDiag F htwo
    intro q hq
    have hq12 : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hq).2.2
    simp only [mem_ofPred_eq]
    rw [joinChoice_root_eq_iff_ordered F hq hrBm hAB, joinChoice_root_apply F hq, hrj]
    constructor
    · rintro ⟨hst, hroot⟩
      have hconn : (F.joinChoice q).root (u j₀) = (F.joinChoice q).root (u l₀) := by
        exact (conn_of_trackedState_eq hst j₀ l₀ ((hborn j₀).mpr hj₀) ((hborn l₀).mpr hl₀)).mpr hm
      rw [joinChoice_root_apply F hq, joinChoice_root_apply F hq, ← hrA, ← hrB,
        joinRelabel_eq_iff hq12] at hconn
      rcases hconn with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h hAB
      · exact Prod.ext h1.symm h2.symm
      · exfalso
        unfold joinRelabel at hroot
        rw [ite_eq_left h1] at hroot
        exact hAB (h2 ▸ hroot).symm
    · rintro rfl
      refine ⟨(trackedState_joinChoice_of_tracked hborn hmem hq hj₀ hl₀ rfl rfl).2, ?_⟩
      simp [joinRelabel, hAB]
  have hcs : chainStep x n p u s (mergeState s j₀ l₀) =
      1 / ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ) := by
    have hne : mergeState s j₀ l₀ ≠ s := by
      intro h
      have := congrFun (congrFun h j₀) l₀
      rw [hm, hsep] at this
      exact Bool.noConfusion this
    have hmerge : IsMerge n (p + 1) u s (mergeState s j₀ l₀) := ⟨j₀, l₀, hj₀, hl₀, hsep, rfl⟩
    simp [chainStep, hx, hne, hmerge]
  rw [measureReal_def, hev, ← measureReal_def,
    transitionLaw_orderedPair hn hp hFv hrAm hrBm hAB, ite_eq_left hx, hcs]
  ring


theorem measurableSet_orientedEvent (q : ℕ) (s' : ConnState k) (w : ℕ ⊕ ℕ) :
    MeasurableSet {pr : Reverse.Forest × Reverse.Forest |
      trackedState n q u pr.2 = s' ∧ pr.2.root w = pr.1.root w} := by
  have h1 : Measurable (fun pr : Reverse.Forest × Reverse.Forest ↦ trackedState n q u pr.2) :=
    (measurable_from_top (f := fun G : Reverse.Forest ↦ trackedState n q u G)).comp measurable_snd
  have h2 : Measurable (fun pr : Reverse.Forest × Reverse.Forest ↦ pr.2.root w) :=
    (measurable_from_top (f := fun G : Reverse.Forest ↦ G.root w)).comp measurable_snd
  have h3 : Measurable (fun pr : Reverse.Forest × Reverse.Forest ↦ pr.1.root w) :=
    (measurable_from_top (f := fun G : Reverse.Forest ↦ G.root w)).comp measurable_fst
  exact (h1 (measurableSet_singleton s')).inter (measurableSet_eq_fun h2 h3)

/-- **Markov step of an oriented merge.** Jointly with any past event and the current tracked
state, an oriented merge of the components of `j₀` and `l₀`, in which the component of `j`
keeps its root, has probability half of the merge step. -/
theorem jointLaw_chainState_orientedStep (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) {N : ℕ} (hN : N < n) {A : Set History}
    (hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N] A)
    {s : ConnState k} {j₀ l₀ j : Fin k} (hx : x (n - N) = true)
    (hj₀ : Born n (n - N) u j₀) (hl₀ : Born n (n - N) u l₀) (hsep : s j₀ l₀ = false)
    (hj : s j j₀ = true ∨ s j l₀ = true) :
    (jointLaw x n).real (A ∩ {ω | chainState n u N ω = s} ∩
        {ω | chainState n u (N + 1) ω = mergeState s j₀ l₀ ∧
          (ω (N + 1)).root (u j) = (ω N).root (u j)}) =
      (jointLaw x n).real (A ∩ {ω | chainState n u N ω = s}) *
        (1 / 2 * chainStep x n (n - (N + 1)) u s (mergeState s j₀ l₀)) := by
  have hp1 : n - (N + 1) + 1 = n - N := by omega
  have hval : ∀ᵐ ω ∂jointLaw x n, Reverse.ValidAt x n (n - N) (ω N) := by
    have h := Freezing1.Reverse.lawAfter_valid x n N hn hN.le
    rw [← ReverseHistory.jointLaw_map_eval x n N] at h
    exact ae_of_ae_map (measurable_pi_apply N).aemeasurable h
  have hA' : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N]
      (A ∩ {ω | chainState n u N ω = s}) := hA.inter (measurableSet_chainState n u le_rfl s)
  have hE := measurableSet_orientedEvent (n := n) (u := u) (n - (N + 1)) (mergeState s j₀ l₀)
    (u j)
  have hev : {ω : History | chainState n u (N + 1) ω = mergeState s j₀ l₀ ∧
      (ω (N + 1)).root (u j) = (ω N).root (u j)} = transitionEvent {pr : Reverse.Forest ×
        Reverse.Forest | trackedState n (n - (N + 1)) u pr.2 = mergeState s j₀ l₀ ∧
          pr.2.root (u j) = pr.1.root (u j)} N := rfl
  rw [hev]
  apply jointLaw_real_inter_transitionEvent x n hN hA' hE
  filter_upwards [hval] with ω hω hAω
  have hω' : Reverse.ValidAt x n (n - (N + 1) + 1) (ω N) := by rwa [hp1]
  have hmem : ∀ j, Born n (n - (N + 1) + 1) u j → u j ∈ (ω N).vertices := by
    intro j hj
    rw [hω'.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) (hu j)).mpr hj
  have hs : trackedState n (n - (N + 1) + 1) u (ω N) = s := by
    rw [hp1]
    exact hAω.2
  have hx' : x (n - (N + 1) + 1) = true := by rwa [hp1]
  have hj₀' : Born n (n - (N + 1) + 1) u j₀ := by rwa [hp1]
  have hl₀' : Born n (n - (N + 1) + 1) u l₀ := by rwa [hp1]
  have h := transitionLaw_orientedMerge hn (by omega) hu hω' hmem hx' hj₀' hl₀'
    (by rw [hs]; exact hsep) (by rw [hs]; exact hj)
  rw [hs] at h
  exact h


/-- The orientation constraint at step `N`: when `o N = some j`, the component of `j` keeps its
root through the step. -/
def OrientCond (u : Fin k → ℕ ⊕ ℕ) (o : ℕ → Option (Fin k)) (N : ℕ) (ω : History) : Prop :=
  ∀ j, o N = some j → (ω (N + 1)).root (u j) = (ω N).root (u j)

/-- A path of the tracked chain with orientation constraints at some steps. -/
def orientedPathEvent (n : ℕ) (u : Fin k → ℕ ⊕ ℕ) (π : ℕ → ConnState k)
    (o : ℕ → Option (Fin k)) (D : ℕ) : Set History :=
  {ω | (∀ N ≤ D, chainState n u N ω = π N) ∧ ∀ N < D, OrientCond u o N ω}

theorem measurableSet_orientCond (u : Fin k → ℕ ⊕ ℕ) (o : ℕ → Option (Fin k)) {N D : ℕ}
    (hN : N < D) :
    MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) D] {ω | OrientCond u o N ω} := by
  have : {ω : History | OrientCond u o N ω} =
      ⋂ j, {ω | o N = some j → (ω (N + 1)).root (u j) = (ω N).root (u j)} := by
    ext ω
    simp [OrientCond]
  rw [this]
  refine MeasurableSet.iInter fun j ↦ ?_
  by_cases hj : o N = some j
  · simp only [hj, forall_const]
    exact measurableSet_eq_fun
      ((measurable_from_top (f := fun G : Reverse.Forest ↦ G.root (u j))).comp
        (measurable_eval_piLE (Nat.succ_le_of_lt hN)))
      ((measurable_from_top (f := fun G : Reverse.Forest ↦ G.root (u j))).comp
        (measurable_eval_piLE hN.le))
  · simp [hj]

/-- **Path law of the tracked chain with oriented merges.** The probability that the tracked
state follows a prescribed path for `D` steps, with the prescribed component keeping its root
at each oriented merge, is the product of the one-step transition probabilities, halved at the
oriented merges. -/
theorem jointLaw_orientedPath (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u)
    (hbirth : ∀ j, Freezing1.birthTime n (u j) < n) (π : ℕ → ConnState k)
    (o : ℕ → Option (Fin k))
    (ho : ∀ N < n, ∀ j, o N = some j → x (n - N) = true ∧ ∃ j₀ l₀, Born n (n - N) u j₀ ∧
      Born n (n - N) u l₀ ∧ π N j₀ l₀ = false ∧ π (N + 1) = mergeState (π N) j₀ l₀ ∧
        (π N j j₀ = true ∨ π N j l₀ = true)) :
    ∀ D ≤ n, (jointLaw x n).real (orientedPathEvent n u π o D) =
      (open Classical in if π 0 = diagState then 1 else 0) *
        ∏ N ∈ Finset.range D, ((if o N = none then 1 else 1 / 2) *
          chainStep x n (n - (N + 1)) u (π N) (π (N + 1))) := by
  classical
  intro D
  induction D with
  | zero =>
    intro hD
    have h := jointLaw_chainPath hn hu hinj hbirth π 0 hD
    have hset : orientedPathEvent n u π o 0 = {ω | ∀ N ≤ 0, chainState n u N ω = π N} := by
      ext ω
      simp [orientedPathEvent]
    rw [hset, h]
    simp
  | succ D ih =>
    intro hD
    set A : Set History := {ω | (∀ N < D, chainState n u N ω = π N) ∧
      ∀ N < D, OrientCond u o N ω} with hAdef
    have hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) D] A := by
      have : A = (⋂ N ∈ Finset.range D, {ω | chainState n u N ω = π N}) ∩
          ⋂ N ∈ Finset.range D, {ω | OrientCond u o N ω} := by
        ext ω
        simp [hAdef]
      rw [this]
      exact (Finset.measurableSet_biInter _ fun N hN ↦
        measurableSet_chainState n u (Finset.mem_range.mp hN).le (π N)).inter
        (Finset.measurableSet_biInter _ fun N hN ↦
          measurableSet_orientCond u o (Finset.mem_range.mp hN))
    have h2 : orientedPathEvent n u π o D = A ∩ {ω | chainState n u D ω = π D} := by
      ext ω
      simp only [orientedPathEvent, hAdef, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨h, ho'⟩
        exact ⟨⟨fun N hN ↦ h N hN.le, ho'⟩, h D le_rfl⟩
      · rintro ⟨⟨h, ho'⟩, hD'⟩
        refine ⟨fun N hN ↦ ?_, ho'⟩
        rcases Nat.lt_or_ge N D with hlt | hge
        · exact h N hlt
        · exact (le_antisymm hN hge) ▸ hD'
    have hsplit : ∀ ω, (ω ∈ orientedPathEvent n u π o (D + 1) ↔
        ω ∈ A ∩ {ω | chainState n u D ω = π D} ∧ chainState n u (D + 1) ω = π (D + 1) ∧
          OrientCond u o D ω) := by
      intro ω
      simp only [orientedPathEvent, hAdef, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨h, ho'⟩
        exact ⟨⟨⟨fun N hN ↦ h N (by omega), fun N hN ↦ ho' N (by omega)⟩, h D (by omega)⟩,
          h (D + 1) le_rfl, ho' D (by omega)⟩
      · rintro ⟨⟨⟨h, ho'⟩, hD'⟩, hD1, hoD⟩
        refine ⟨fun N hN ↦ ?_, fun N hN ↦ ?_⟩
        · rcases Nat.lt_or_ge N D with hlt | hge
          · exact h N hlt
          · rcases Nat.eq_or_lt_of_le hge with heq | hgt
            · exact heq ▸ hD'
            · have : N = D + 1 := by omega
              exact this ▸ hD1
        · rcases Nat.lt_or_ge N D with hlt | hge
          · exact ho' N hlt
          · have : N = D := by omega
            exact this ▸ hoD
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih (by omega), h2]
    cases hoD : o D with
    | none =>
      have hset : orientedPathEvent n u π o (D + 1) =
          A ∩ {ω | chainState n u D ω = π D} ∩ {ω | chainState n u (D + 1) ω = π (D + 1)} := by
        ext ω
        rw [hsplit ω]
        simp [OrientCond, hoD]
      rw [hset, jointLaw_chainState_step hn hu hinj (by omega) hA]
      simp
    | some j =>
      obtain ⟨hx, j₀, l₀, hj₀, hl₀, hsep, hπ, hj⟩ := ho D (by omega) j hoD
      have hset : orientedPathEvent n u π o (D + 1) =
          A ∩ {ω | chainState n u D ω = π D} ∩
            {ω | chainState n u (D + 1) ω = mergeState (π D) j₀ l₀ ∧
              (ω (D + 1)).root (u j) = (ω D).root (u j)} := by
        ext ω
        rw [hsplit ω, hπ]
        simp only [OrientCond, hoD, Option.some.injEq, forall_eq', mem_inter_iff,
          mem_ofPred_eq]
      rw [hset, jointLaw_chainState_orientedStep hn hu (by omega) hA hx hj₀ hl₀ hsep hj, hπ]
      simp


/-! ### Oriented patterns -/

/-- The pattern event with orientations: the tracked genealogy follows the pattern `(xs, c)` at
the phases `≥ p₀`, and at the `i`-th merge the component of the label `rep i` keeps its root. -/
def planePatternEvent (n p₀ : ℕ) (b : Fin k → ℕ) (xs : Fin m → ConnState k) (c : Fin m → ℕ)
    (rep : Fin m → Fin k) : Set History :=
  patternEvent n p₀ b xs c ∩ {ω | ∀ i, (ω (n - c i)).root (frozenLabels b (rep i)) =
    (ω (n - (c i + 1))).root (frozenLabels b (rep i))}

open Classical in
/-- The orientation constraints of an oriented pattern, indexed by the reverse steps. -/
noncomputable def patternOrient (n : ℕ) (c : Fin m → ℕ) (rep : Fin m → Fin k) (N : ℕ) :
    Option (Fin k) :=
  if h : ∃ i, c i + N + 1 = n then some (rep h.choose) else none

theorem mem_mergedSet_cases {xs : Fin m → ConnState k} {s : Fin m} {j j₀ l₀ : Fin k}
    (hpost : stateSeq xs s.succ = mergeState (stateSeq xs s.castSucc) j₀ l₀)
    (hj : j ∈ mergedSet xs s) :
    stateSeq xs s.castSucc j j₀ = true ∨ stateSeq xs s.castSucc j l₀ = true := by
  obtain ⟨l, h1, h2⟩ := hj
  rw [hpost, mergeState_iff] at h1
  rcases h1 with h | ⟨h, -⟩ | ⟨h, -⟩
  · rw [h] at h2
    exact Bool.noConfusion h2
  · exact Or.inl h
  · exact Or.inr h

/-- **The exact oriented pattern probability.** For an admissible pattern above `p₀` and
representatives `rep i` of the components merged at the `i`-th merge, prescribing which
component keeps its root at each merge divides the pattern probability by `2^m`. -/
theorem jointLaw_planePatternEvent {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {b : Fin k → ℕ} {xs : Fin m → ConnState k}
    {c : Fin m → ℕ} (hb : ∀ j, b j < n ∧ x (b j + 1) = false) (hbinj : Function.Injective b)
    (hcx : ∀ i, x (c i + 1) = true)
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ)))
    {p₀ : ℕ} (hcp : ∀ i, p₀ ≤ c i) {rep : Fin m → Fin k} (hrep : ∀ i, rep i ∈ mergedSet xs i) :
    (jointLaw x n).real (planePatternEvent n p₀ b xs c rep) =
      (1 / 2) ^ m * (jointLaw x n).real (patternEvent n p₀ b xs c) := by
  classical
  set u := frozenLabels b
  have hanti : StrictAnti c := fun a a' h ↦ by
    have := hadm.strictAnti h
    exact_mod_cast this
  have hcn : ∀ i, c i < n := fun i ↦ by
    have := (hadm.time_mem i).2
    exact_mod_cast this
  have hu : ∀ j, u j ∈ Freezing1.vertexLabels x n := by
    intro j
    simp only [u, frozenLabels, Freezing1.vertexLabels, Finset.inr_mem_disjSum,
      Freezing1.frozenIndices, Finset.mem_filter, Finset.mem_range]
    exact hb j
  have hinj : Function.Injective u := fun a a' h ↦ hbinj (Sum.inr_injective h)
  have hbirth : ∀ j, Freezing1.birthTime n (u j) < n := fun j ↦ (hb j).1
  set π : ℕ → ConnState k := fun N ↦ patternState xs c (n - N) with hπdef
  set o := patternOrient n c rep with hodef
  set D := n - p₀ with hDdef
  have hoiff : ∀ N j, o N = some j ↔ ∃ i, c i + N + 1 = n ∧ rep i = j := by
    intro N j
    simp only [hodef, patternOrient]
    split_ifs with h
    · constructor
      · intro hj
        exact ⟨h.choose, h.choose_spec, Option.some.inj hj⟩
      · rintro ⟨i, hi, rfl⟩
        have : h.choose = i := hanti.injective (by have := h.choose_spec; omega)
        rw [this]
    · constructor
      · intro hj
        simp at hj
      · rintro ⟨i, hi, -⟩
        exact absurd ⟨i, hi⟩ h
  have hND : ∀ i, n - (c i + 1) < D := fun i ↦ by have := hcp i; have := hcn i; omega
  -- the oriented pattern event is an oriented path event
  have hset : planePatternEvent n p₀ b xs c rep = orientedPathEvent n u π o D := by
    ext ω
    simp only [planePatternEvent, patternEvent, orientedPathEvent, OrientCond, mem_inter_iff,
      mem_ofPred_eq, hπdef]
    constructor
    · rintro ⟨hpath, hor⟩
      refine ⟨hpath, fun N _ j hj ↦ ?_⟩
      obtain ⟨i, hi, rfl⟩ := (hoiff N j).mp hj
      have h1 : N + 1 = n - c i := by omega
      have h2 : N = n - (c i + 1) := by omega
      rw [h1, h2]
      exact hor i
    · rintro ⟨hpath, hor⟩
      refine ⟨hpath, fun i ↦ ?_⟩
      have h := hor (n - (c i + 1)) (hND i) (rep i)
        ((hoiff _ _).mpr ⟨i, by have := hcn i; omega, rfl⟩)
      rwa [show n - (c i + 1) + 1 = n - c i by have := hcn i; omega] at h
  -- the hypotheses of the oriented path law
  have ho : ∀ N < n, ∀ j, o N = some j → x (n - N) = true ∧ ∃ j₀ l₀, Born n (n - N) u j₀ ∧
      Born n (n - N) u l₀ ∧ π N j₀ l₀ = false ∧ π (N + 1) = mergeState (π N) j₀ l₀ ∧
        (π N j j₀ = true ∨ π N j l₀ = true) := by
    intro N _ j hj
    obtain ⟨i, hi, rfl⟩ := (hoiff N j).mp hj
    have e1 : n - N = c i + 1 := by omega
    have e2 : n - (N + 1) = c i := by omega
    obtain ⟨hpre, hpost⟩ := patternState_merge (xs := xs) hanti i
    obtain ⟨-, j₀, hj₀, l₀, hl₀, hsep, hmerge⟩ := (isAdmissible_iff_forall.mp hadm).2 i
    have hborn : ∀ l ∈ bornAt (fun j ↦ (b j : ℝ)) ((c i : ℕ) : ℝ), Born n (c i + 1) u l := by
      intro l hl
      simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_le] at hl
      have hne : b l ≠ c i := fun h ↦ by
        have h1 := (hb l).2
        rw [h, hcx i] at h1
        exact Bool.noConfusion h1
      show c i + 1 ≤ b l
      omega
    simp only [hπdef, e1, e2, hpre, hpost]
    refine ⟨hcx i, j₀, l₀, hborn j₀ hj₀, hborn l₀ hl₀, hsep, hmerge, ?_⟩
    exact mem_mergedSet_cases hmerge (hrep i)
  have hplane := jointLaw_orientedPath hn hu hinj hbirth π o ho D (Nat.sub_le n p₀)
  have hpat := jointLaw_chainPath hn hu hinj hbirth π D (Nat.sub_le n p₀)
  have hpe : patternEvent n p₀ b xs c = {ω | ∀ N ≤ D, chainState n u N ω = π N} := rfl
  rw [hset, hplane, hpe, hpat, Finset.prod_mul_distrib]
  -- the number of oriented steps is `m`
  have hcount : ∏ N ∈ Finset.range D, (if o N = none then (1 : ℝ) else 1 / 2) =
      (1 / 2) ^ m := by
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have himg : (Finset.range D).filter (fun N ↦ ¬ o N = none) =
        Finset.univ.image (fun i ↦ n - (c i + 1)) := by
      ext N
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨hN, hne⟩
        obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
        obtain ⟨i, hi, -⟩ := (hoiff N j).mp hj
        exact ⟨i, by omega⟩
      · rintro ⟨i, rfl⟩
        refine ⟨hND i, fun h ↦ ?_⟩
        have := (hoiff (n - (c i + 1)) (rep i)).mpr ⟨i, by have := hcn i; omega, rfl⟩
        rw [h] at this
        simp at this
    rw [himg, Finset.card_image_of_injective _ (fun i i' h ↦ hanti.injective (by
      have h' : n - (c i + 1) = n - (c i' + 1) := h
      have := hcn i; have := hcn i'; omega)), Finset.card_univ, Fintype.card_fin]
  rw [hcount]
  ring


/-! ### The plane forests `𝔉⁺_{r,k}` of the discrete genealogy -/

section PlaneForest

variable {r : ℕ}

/-- The particles below the left child of the vertex of the `s`-th merge of a plane forest. -/
def leftLeaves {N : ℕ} (F : KidsMap N) (e : Fin k ⊕ Fin m ≃ Fin N) (s : Fin m) : Set (Fin k) :=
  match F (e (.inr s)) with
  | some (a, _) => leafSet F e a
  | none => ∅

open Classical in
/-- A particle below the left child of the vertex of the `s`-th merge of `F₀ ∈ 𝔉⁺_{r,k}`, the
vertices being labelled by the ranks of the event times `(β, γ)`. In the discrete plane forest,
the left child of a merge is the subtree whose root survives the merge. -/
noncomputable def leftRep (r : ℕ) (F₀ : SourceForest r k) (β : Fin k → ℝ)
    (γ : Fin (k - 1 - r) → ℝ) (s : Fin (k - 1 - r)) : Fin k :=
  if h : ∃ (hinj : Function.Injective (Sum.elim β γ)) (j : Fin k),
      j ∈ leftLeaves F₀.1 (labelEquiv (cmpOf (Sum.elim β γ)) (rankFin_bijective_iff.mpr hinj)
        (show k + (k - 1 - r) = 2 * k - 1 - r by have := s.2; omega)) s then
    h.choose_spec.choose
  else ⟨0, by have := s.2; omega⟩

/-- **Alignment with the plane forests.** For a plane history with forest `F₀`, the
representative of the left child of the `s`-th merge is one of the particles merged by it. -/
theorem leftRep_mem_mergedSet (hr : r < k) {F₀ : SourceForest r k}
    {xs : Fin (k - 1 - r) → ConnState k} {σ : Fin (k - 1 - r) → Bool} {β : Fin k → ℝ}
    {γ : Fin (k - 1 - r) → ℝ}
    (h : patternForest r xs σ (cmpOf (Sum.elim β γ)) (unitPattern γ) = some F₀)
    (s : Fin (k - 1 - r)) : leftRep r F₀ β γ s ∈ mergedSet xs s := by
  classical
  have hN : k + (k - 1 - r) = 2 * k - 1 - r := by omega
  obtain ⟨hinj, hadm, hF⟩ := (patternForest_eq_some_iff hr xs σ β γ F₀).mp h
  set e := labelEquiv (cmpOf (Sum.elim β γ)) (rankFin_bijective_iff.mpr hinj) hN with hedef
  have hD : DAdm e xs := ((isAdmissible_iff_dAdm hinj (labelEquiv_lt_iff_times hinj hN) xs).mp
    hadm).2
  have hfits : Fits F₀.1 e := hF ▸ hD.fits σ
  have hleaf : leafSet F₀.1 e = clusterOf e xs := hF ▸ hD.leafSet_histForest σ
  obtain ⟨a, a', hkids⟩ := hfits.exists_kids ⟨s, rfl⟩
  have hsub : leftLeaves F₀.1 e s ⊆ mergedSet xs s := by
    intro j hj
    simp only [leftLeaves, hkids] at hj
    have : j ∈ leafSet F₀.1 e (e (.inr s)) := by
      rw [hfits.leafSet_kids hkids]
      exact Or.inl hj
    rwa [hleaf, clusterOf_inr] at this
  have hne : (leftLeaves F₀.1 e s).Nonempty := by
    simp only [leftLeaves, hkids]
    exact hfits.leafSet_nonempty a
  have hex : ∃ (hinj : Function.Injective (Sum.elim β γ)) (j : Fin k),
      j ∈ leftLeaves F₀.1 (labelEquiv (cmpOf (Sum.elim β γ)) (rankFin_bijective_iff.mpr hinj)
        (show k + (k - 1 - r) = 2 * k - 1 - r by have := s.2; omega)) s :=
    ⟨hinj, hne.some, hne.some_mem⟩
  rw [leftRep, dite_eq_left hex]
  exact hsub hex.choose_spec.choose_spec

/-- **The discrete plane forest event.** The tracked genealogy of the frozen vertices born at
`b` follows the merge history `xs` at the phases `c` above `p₀`, and at each merge the subtree
whose root survives is the left child in `F₀ ∈ 𝔉⁺_{r,k}` (vertices labelled by the ranks of the
scaled event times). -/
def planeForestEvent (n p₀ : ℕ) (F₀ : SourceForest r k) (b : Fin k → ℕ)
    (xs : Fin (k - 1 - r) → ConnState k) (c : Fin (k - 1 - r) → ℕ) : Set History :=
  planePatternEvent n p₀ b xs c (leftRep r F₀ (scaledPhases n b) (scaledPhases n c))

open Classical in
/-- **The rescaled conditional probability of a plane forest** `F₀ ∈ 𝔉⁺_{r,k}`: `(n/2)^(k-1-r)`
times the probability, given that the sampled vertices are the frozen vertices born at `b`, that
the merges above `ε n` occur at the phases `c` and form the plane forest `F₀`, the children of
each merge being ordered by the survival of their roots (left = surviving root). -/
noncomputable def scaledPlaneProb (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (F₀ : SourceForest r k)
    (b : Fin k → ℕ) (c : Fin (k - 1 - r) → ℕ) : ℝ :=
  ∑ xs : Fin (k - 1 - r) → ConnState k,
    if ForestCompatible r F₀ xs (scaledPhases n b) (scaledPhases n c) ∧
        LocalAdmissible xa n ε xs b c then
      ((n : ℝ) / 2) ^ (k - 1 - r) * (jointLaw (companionSchedule xa) n).real
        (planeForestEvent n (phaseAbove n ε) F₀ b xs c)
    else 0

/-- **The orientation factor.** Prescribing the child orders by root survival divides the
probability of the forest by `2^(k-1-r)`: each oriented merge has probability `1 / (S (S - 1))`,
half of the merge hazard. -/
theorem scaledPlaneProb_eq {xa : ℕ → ℤ} (hx : IsSigned xa) {n : ℕ} (hs : SurvivesThrough xa n)
    (hr : r < k) (ε : ℝ) (F₀ : SourceForest r k) (b : Fin k → ℕ) (c : Fin (k - 1 - r) → ℕ) :
    scaledPlaneProb xa n ε F₀ b c = (1 / 2) ^ (k - 1 - r) * scaledForestProb xa n ε F₀ b c := by
  classical
  unfold scaledPlaneProb scaledForestProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  by_cases hF : ForestCompatible r F₀ xs (scaledPhases n b) (scaledPhases n c)
  · by_cases hL : LocalAdmissible xa n ε xs b c
    · rw [ite_eq_left ⟨hF, hL⟩, ite_eq_left hF, scaledPatternProb, ite_eq_left hL]
      obtain ⟨σ, hσ⟩ := hF
      obtain ⟨hbinj, hb, hc, hcp, hadm⟩ := hL
      have hn : (n : ℕ∞) ≤ extinctionTime (companionSchedule xa) :=
        (companion_before_extinction xa hx hs).le
      have hb' : ∀ j, b j < n ∧ companionSchedule xa (b j + 1) = false := fun j ↦
        ⟨(hb j).1, by simp [companionSchedule, (hb j).2]⟩
      have hcx : ∀ i, companionSchedule xa (c i + 1) = true := fun i ↦ by
        simp [companionSchedule, hc i]
      rw [planeForestEvent, jointLaw_planePatternEvent hn hb' hbinj hcx hadm hcp
        (leftRep_mem_mergedSet hr hσ)]
      ring
    · rw [ite_eq_right fun h ↦ hL h.2, ite_eq_left hF, scaledPatternProb, ite_eq_right hL,
        mul_zero]
  · rw [ite_eq_right fun h ↦ hF h.1, ite_eq_right hF, mul_zero]


/-! ### The plane local limit -/

/-- The discrete plane functional: `2^{-(k-1-r)}` times the forest functional. -/
noncomputable def discFunPlane (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (F₀ : SourceForest r k)
    (z : LocalSpace k (k - 1 - r)) : ℝ :=
  (1 / 2) ^ (k - 1 - r) * discFunForest xa n ε F₀ z

/-- The limit plane functional at cutoff `ε`. -/
noncomputable def limitFunPlane (g : ℝ → ℝ) (ε : ℝ) (F₀ : SourceForest r k)
    (z : LocalSpace k (k - 1 - r)) : ℝ :=
  (1 / 2) ^ (k - 1 - r) * limitFunForest g ε F₀ z

/-- The limit plane functional without cutoff. -/
noncomputable def limitFun0Plane (g : ℝ → ℝ) (F₀ : SourceForest r k)
    (z : LocalSpace k (k - 1 - r)) : ℝ :=
  (1 / 2) ^ (k - 1 - r) * limitFun0Forest g F₀ z

theorem measurable_const_mul_real (a : ℝ) : Measurable (fun t : ℝ ↦ a * t) :=
  measurable_const.mul measurable_id

theorem map_const_mul {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    {f : Ω → ℝ} (hf : Measurable f) (a : ℝ) :
    μ.map (fun z ↦ a * f z) = (μ.map f).map (fun t ↦ a * t) := by
  apply Subtype.ext
  change (μ : Measure Ω).map (fun z ↦ a * f z) = ((μ : Measure Ω).map f).map (fun t ↦ a * t)
  rw [Measure.map_map (measurable_const_mul_real a) hf]
  rfl

theorem eventually_map_discFunPlane_eq {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g) (hr : r < k)
    (ε : ℝ) (F₀ : SourceForest r k) :
    ∀ᶠ n in atTop,
      ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀) : Measure ℝ) =
        (sourceSampleLaw (xa n) n k (k - 1 - r)).map
          (fun q ↦ scaledPlaneProb (xa n) n ε F₀ q.1 q.2) := by
  filter_upwards [eventually_map_discFunForest_eq hx hL1 hpos ε F₀] with n hn
  have h1 : (auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀) =
      ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀)).map
        (fun t ↦ (1 / 2) ^ (k - 1 - r) * t) :=
    map_const_mul _ (measurable_discFunForest (xa n) n ε F₀) _
  have hfun : (fun q : (Fin k → ℕ) × (Fin (k - 1 - r) → ℕ) ↦
      scaledPlaneProb (xa n) n ε F₀ q.1 q.2) = (fun t ↦ (1 / 2) ^ (k - 1 - r) * t) ∘
        (fun q ↦ scaledForestProb (xa n) n ε F₀ q.1 q.2) :=
    funext fun q ↦ scaledPlaneProb_eq (hx n).1 (hx n).2 hr ε F₀ q.1 q.2
  rw [h1, ProbabilityMeasure.toMeasure_map, hn,
    Measure.map_map (measurable_const_mul_real _) (measurable_of_countable _), hfun]

theorem tendsto_localLawPlane {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g) {ε : ℝ} (hε : 0 < ε)
    (F₀ : SourceForest r k) :
    Tendsto (fun n ↦ (auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀))
      atTop (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunPlane g ε F₀))) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_localLawForest hx hL1 hpos h2 hg hε F₀)
    (f := fun t : ℝ ↦ (1 / 2) ^ (k - 1 - r) * t) (continuous_const.mul continuous_id)
  rw [← map_const_mul _ (measurable_limitFunForest hg ε F₀)] at h
  refine h.congr fun n ↦ ?_
  exact (map_const_mul _ (measurable_discFunForest (xa n) n ε F₀) _).symm

theorem tendsto_limitLawPlane_zero {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hg : Measurable g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (F₀ : SourceForest r k) :
    Tendsto (fun ε ↦ (limitLocalLaw g k (k - 1 - r)).map (limitFunPlane g ε F₀)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Plane g F₀))) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_limitLawForest_zero hg h2 F₀)
    (f := fun t : ℝ ↦ (1 / 2) ^ (k - 1 - r) * t) (continuous_const.mul continuous_id)
  rw [← map_const_mul _ (measurable_limitFun0Forest hg F₀)] at h
  refine h.congr fun ε ↦ ?_
  exact (map_const_mul _ (measurable_limitFunForest hg ε F₀) _).symm

/-- At marks `g²`, the limit forest functional is `2^(k-1-r) g_{r,k}`. -/
theorem limitFun0Forest_markEmbed (g : ℝ → ℝ) (hr : r < k) (F₀ : SourceForest r k)
    {q : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ)} (hinj : Function.Injective q.1) :
    limitFun0Forest g F₀ (markEmbed g q) =
      (2 ^ (k - 1 - r) * sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev)).toReal := by
  classical
  simp only [limitFun0Forest]
  rw [show mergeTimes (markEmbed g q) = q.2 from rfl, show (markEmbed g q).1 = q.1 from rfl,
    ← sum_historyDensity_forest g hr F₀ q.1 q.2, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun xs _ ↦ ?_
    split_ifs
    · exact limitFun0_markEmbed g xs hinj
    · rfl
  · intro xs _
    split_ifs
    · exact historyDensity_ne_top g q.1 xs q.2
    · simp

theorem measurable_limitFun0Plane {g : ℝ → ℝ} (hg : Measurable g) (F₀ : SourceForest r k) :
    Measurable (limitFun0Plane g F₀) :=
  measurable_const.mul (measurable_limitFun0Forest hg F₀)

/-- **Identification of the plane limit law** with the source's density `g_{r,k}`. -/
theorem limitLocalLaw_map_limitFun0Plane {g : ℝ → ℝ} (hg : Measurable g) (hr : r < k)
    (F₀ : SourceForest r k) :
    ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Plane g F₀) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure (k - 1 - r))).map
        (fun q ↦ (sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev)).toReal) := by
  classical
  rw [ProbabilityMeasure.toMeasure_map, limitLocalLaw_eq_map hg,
    show (fun q : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ) ↦ (q.1, fun i ↦ (q.2 i, g (q.2 i) ^ 2))) =
      markEmbed g from rfl,
    Measure.map_map (measurable_limitFun0Plane hg F₀) (measurable_markEmbed hg)]
  apply Measure.map_congr
  filter_upwards [ae_cubeProd_good (k := k) (m := k - 1 - r) 0] with q hq
  have hinj : Function.Injective q.1 := (hq.2.2.1).comp Sum.inl_injective
  simp only [Function.comp_apply, limitFun0Plane]
  rw [limitFun0Forest_markEmbed g hr F₀ hinj, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ← mul_assoc, ← mul_pow]
  norm_num


/-! ### The source's exact normalization -/

/-- Conditioning on the sampled vertices, for any history event. -/
theorem sampledReverseVectorLaw_prod_frozenVertex {xa : ℕ → ℤ} {n : ℕ} {b : Fin k → ℕ}
    (hb : ∀ j, b j < n ∧ xa (b j + 1) = -1) (E : Set History) :
    (sampledReverseVectorLaw xa n k).real (E ×ˢ {frozenVertex b}) =
      ((vertexCount xa n : ℝ)⁻¹) ^ k * (jointLaw (companionSchedule xa) n).real E := by
  classical
  have hmem : ∀ j, frozenVertex b j ∈ vertexLabels xa n := by
    intro j
    simp only [frozenVertex, vertexLabels, Finset.inl_mem_disjSum, downSteps, Finset.mem_filter,
      Finset.mem_Ioc]
    exact ⟨⟨by omega, by have := (hb j).1; omega⟩, (hb j).2⟩
  have : IsFiniteMeasure (uniformVertex xa n) := uniformOfFinset_finite _
  have hpt : (Measure.pi fun _ : Fin k ↦ uniformVertex xa n) {frozenVertex b} =
      ((vertexCount xa n : ℝ≥0∞)⁻¹) ^ k := by
    rw [← Set.univ_pi_singleton, Measure.pi_pi]
    simp only [uniformVertex]
    rw [Finset.prod_congr rfl fun j _ ↦ Measure.uniformOfFinset_apply_singleton_of_mem (hmem j),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_vertexLabels]
  rw [measureReal_def, sampledReverseVectorLaw, Measure.prod_prod, hpt, ENNReal.toReal_mul,
    mul_comm, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, measureReal_def]

open Classical in
/-- **The source's quantity for a plane forest**: `(n/2)^(2k-1-r)` times the probability,
under one reverse history and `k` iid uniform vertices, that the sampled vertices are the
frozen vertices born at `b` and that the merges above `ε n` occur at the phases `c` and form
the plane forest `F₀` (children ordered by root survival). -/
noncomputable def sourcePlaneProb (xa : ℕ → ℤ) (n : ℕ) (ε : ℝ) (F₀ : SourceForest r k)
    (b : Fin k → ℕ) (c : Fin (k - 1 - r) → ℕ) : ℝ :=
  ∑ xs : Fin (k - 1 - r) → ConnState k,
    if ForestCompatible r F₀ xs (scaledPhases n b) (scaledPhases n c) ∧
        LocalAdmissible xa n ε xs b c then
      ((n : ℝ) / 2) ^ (2 * k - 1 - r) * (sampledReverseVectorLaw xa n k).real
        (planeForestEvent n (phaseAbove n ε) F₀ b xs c ×ˢ {frozenVertex b})
    else 0

/-- The source's normalization differs from `scaledPlaneProb` by the factor `((n/2)/N)^k`. -/
theorem sourcePlaneProb_eq {xa : ℕ → ℤ} {n : ℕ} (hr : r < k) (ε : ℝ) (F₀ : SourceForest r k)
    (b : Fin k → ℕ) (c : Fin (k - 1 - r) → ℕ) :
    sourcePlaneProb xa n ε F₀ b c =
      (((n : ℝ) / 2) / vertexCount xa n) ^ k * scaledPlaneProb xa n ε F₀ b c := by
  classical
  unfold sourcePlaneProb scaledPlaneProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun xs _ ↦ ?_
  split_ifs with h
  · rw [sampledReverseVectorLaw_prod_frozenVertex h.2.2.1,
      show 2 * k - 1 - r = k + (k - 1 - r) by omega, pow_add, div_pow ((n : ℝ) / 2), inv_pow]
    ring
  · rw [mul_zero]

/-- The Dirac mass as a probability measure. -/
noncomputable def diracPM (a : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac a, inferInstance⟩

theorem tendsto_diracPM {a : ℕ → ℝ} {a₀ : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun n ↦ diracPM (a n)) atTop (𝓝 (diracPM a₀)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  change Tendsto (fun n ↦ ∫ ω, f ω ∂(Measure.dirac (a n))) atTop
    (𝓝 (∫ ω, f ω ∂(Measure.dirac a₀)))
  simp only [integral_dirac]
  exact (f.continuous.tendsto a₀).comp ha

/-- **Slutsky's lemma for a deterministic factor tending to one.** -/
theorem tendsto_map_mul_of_tendsto {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto μs atTop (𝓝 μ)) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun n ↦ (μs n).map (fun t ↦ a n * t)) atTop (𝓝 μ) := by
  have hprod : Tendsto (fun n ↦ (diracPM (a n)).prod (μs n)) atTop
      (𝓝 ((diracPM 1).prod μ)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      ((tendsto_diracPM ha).prodMk_nhds h)
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hprod
    (f := fun p : ℝ × ℝ ↦ p.1 * p.2) (continuous_fst.mul continuous_snd)
  have hid : ∀ (c : ℝ) (ν : ProbabilityMeasure ℝ),
      ((diracPM c).prod ν).map (fun p : ℝ × ℝ ↦ p.1 * p.2) = ν.map (fun t ↦ c * t) := by
    intro c ν
    apply Subtype.ext
    change ((Measure.dirac c).prod (ν : Measure ℝ)).map (fun p : ℝ × ℝ ↦ p.1 * p.2) =
      (ν : Measure ℝ).map (fun t ↦ c * t)
    rw [Measure.dirac_prod, Measure.map_map
      (show Measurable (fun p : ℝ × ℝ ↦ p.1 * p.2) from measurable_fst.mul measurable_snd)
      measurable_prodMk_left]
    rfl
  have h1 : μ.map (fun t ↦ (1 : ℝ) * t) = μ := by
    apply Subtype.ext
    change (μ : Measure ℝ).map (fun t ↦ (1 : ℝ) * t) = (μ : Measure ℝ)
    simp only [one_mul]
    exact Measure.map_id'
  rw [hid, h1] at hmap
  exact hmap.congr fun n ↦ hid _ _

/-- The source's normalization factor. -/
noncomputable def vertexFactor (xa : ℕ → ℤ) (n k : ℕ) : ℝ :=
  (((n : ℝ) / 2) / vertexCount xa n) ^ k

theorem eventually_map_sourcePlaneProb_eq {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (hr : r < k) (ε : ℝ) (F₀ : SourceForest r k) :
    ∀ᶠ n in atTop,
      (((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀)).map
          (fun t ↦ vertexFactor (xa n) n k * t) : Measure ℝ) =
        (sourceSampleLaw (xa n) n k (k - 1 - r)).map
          (fun q ↦ sourcePlaneProb (xa n) n ε F₀ q.1 q.2) := by
  filter_upwards [eventually_map_discFunPlane_eq hx hL1 hpos hr ε F₀] with n hn
  have hfun : (fun q : (Fin k → ℕ) × (Fin (k - 1 - r) → ℕ) ↦
      sourcePlaneProb (xa n) n ε F₀ q.1 q.2) = (fun t ↦ vertexFactor (xa n) n k * t) ∘
        (fun q ↦ scaledPlaneProb (xa n) n ε F₀ q.1 q.2) :=
    funext fun q ↦ sourcePlaneProb_eq hr ε F₀ q.1 q.2
  rw [ProbabilityMeasure.toMeasure_map, hn,
    Measure.map_map (measurable_const_mul_real _) (measurable_of_countable _), hfun]

theorem tendsto_sourcePlaneLaw {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hg : Measurable g) {ε : ℝ} (hε : 0 < ε)
    (F₀ : SourceForest r k) :
    Tendsto (fun n ↦ ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀)).map
        (fun t ↦ vertexFactor (xa n) n k * t)) atTop
      (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunPlane g ε F₀))) :=
  tendsto_map_mul_of_tendsto (tendsto_localLawPlane hx hL1 hpos h2 hg hε F₀)
    (tendsto_vertexFactor hx hL1 hpos k)


end PlaneForest

/-! ### Removing the measurability assumption on the profile -/

section Modification

variable {g g' : ℝ → ℝ}

theorem ae_profileMeasure_of_ae_Ioo (h : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), g t = g' t) :
    ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t := by
  have heq : (profileMeasure : Measure ℝ) = volume.restrict (Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [heq]
  exact h

theorem hasL1ReciprocalProfile_congr {xa : ℕ → ℕ → ℤ}
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t) :
    HasL1ReciprocalProfile xa (1 / 2) g' :=
  ⟨hL1.1.congr h, hL1.2.congr fun n ↦ integral_congr_ae (h.mono fun t ht ↦ by simp only [ht])⟩

theorem positiveProfile_congr (hpos : PositiveProfile g)
    (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t) : PositiveProfile g' := by
  unfold PositiveProfile at hpos ⊢
  filter_upwards [hpos, h] with t ht h'
  rwa [← h']

theorem hasLocalSquareMomentProfile_congr {xa : ℕ → ℕ → ℤ}
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (h : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), g t = g' t) :
    HasLocalSquareMomentProfile xa (1 / 2) g' := by
  intro a b ha hab hb
  have hae : ∀ᵐ t ∂volume.restrict (Icc a b), g t = g' t :=
    ae_restrict_of_ae_restrict_of_subset (fun t (ht : t ∈ Icc a b) ↦
      (show t ∈ Ioo (0 : ℝ) 1 from ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩)) h
  have hsq : (fun t ↦ g t ^ 2) =ᵐ[volume.restrict (Icc a b)] (fun t ↦ g' t ^ 2) :=
    hae.mono fun t ht ↦ by simp only [ht]
  obtain ⟨hi, hlim⟩ := h2 a b ha hab hb
  exact ⟨hi.congr_fun_ae hsq, by rwa [integral_congr_ae hsq] at hlim⟩

theorem limitLocalLaw_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t) (k m : ℕ) :
    limitLocalLaw g k m = limitLocalLaw g' k m := by
  apply Subtype.ext
  change (Measure.pi fun _ : Fin k ↦ (profileMeasure : Measure ℝ)).prod
      (Measure.pi fun _ : Fin m ↦ (profileMeasure : Measure ℝ).map (fun t ↦ (t, g t ^ 2))) =
    (Measure.pi fun _ : Fin k ↦ (profileMeasure : Measure ℝ)).prod
      (Measure.pi fun _ : Fin m ↦ (profileMeasure : Measure ℝ).map (fun t ↦ (t, g' t ^ 2)))
  rw [Measure.map_congr (h.mono fun t ht ↦ by simp only [ht] :
    (fun t ↦ (t, g t ^ 2)) =ᵐ[(profileMeasure : Measure ℝ)] fun t ↦ (t, g' t ^ 2))]

theorem limitFun_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t) {ε : ℝ}
    (hε : 0 ≤ ε) (xs : Fin m → ConnState k) (z : LocalSpace k m) :
    limitFun g ε xs z = limitFun g' ε xs z := by
  have h' := (ae_restrict_iff' measurableSet_Icc).mp h
  have hint : ∫ t in Ioc ε 1, pairWeight z.1 (mergeTimes z) t * g t ^ 2 =
      ∫ t in Ioc ε 1, pairWeight z.1 (mergeTimes z) t * g' t ^ 2 :=
    setIntegral_congr_ae measurableSet_Ioc (h'.mono fun t ht hmem ↦ by
      rw [ht (show t ∈ Icc (0 : ℝ) 1 from ⟨hε.trans hmem.1.le, hmem.2⟩)])
  simp only [limitFun, hint]

theorem survLIntegral_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t)
    (β : Fin k → ℝ) (γ : Fin m → ℝ) : survLIntegral g β γ 0 = survLIntegral g' β γ 0 := by
  have h' := (ae_restrict_iff' measurableSet_Icc).mp h
  unfold survLIntegral
  exact setLIntegral_congr_fun_ae measurableSet_Ioc (h'.mono fun t ht hmem ↦ by
    rw [ht (show t ∈ Icc (0 : ℝ) 1 from ⟨hmem.1.le, hmem.2⟩)])

theorem limitFun0_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t)
    (xs : Fin m → ConnState k) (z : LocalSpace k m) : limitFun0 g xs z = limitFun0 g' xs z := by
  simp only [limitFun0, survLIntegral_congr h]

variable {r : ℕ}

theorem limitFunPlane_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t) {ε : ℝ}
    (hε : 0 ≤ ε) (F₀ : SourceForest r k) : limitFunPlane g ε F₀ = limitFunPlane g' ε F₀ := by
  funext z
  simp only [limitFunPlane, limitFunForest, limitFun_congr h hε]

theorem limitFun0Plane_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t)
    (F₀ : SourceForest r k) : limitFun0Plane g F₀ = limitFun0Plane g' F₀ := by
  funext z
  simp only [limitFun0Plane, limitFun0Forest, limitFun0_congr h]

theorem ae_sourceDensity_congr (h : ∀ᵐ t ∂(profileMeasure : Measure ℝ), g t = g' t)
    (F₀ : SourceForest r k) :
    ∀ᵐ q ∂((cubeMeasure k).prod (cubeMeasure (k - 1 - r))),
      sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev) = sourceDensity g' F₀ q.1 (q.2 ∘ Fin.rev) := by
  have hcube : cubeMeasure (k - 1 - r) =
      Measure.pi fun _ : Fin (k - 1 - r) ↦ (profileMeasure : Measure ℝ) := rfl
  have hcoord : ∀ᵐ v ∂cubeMeasure (k - 1 - r), ∀ i, g (v i) = g' (v i) := by
    rw [hcube]
    exact ae_all_iff.mpr fun i ↦ (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (k - 1 - r) ↦ (profileMeasure : Measure ℝ)) (i := i)).eventually h
  have hq := ae_of_ae_map (μ := (cubeMeasure k).prod (cubeMeasure (k - 1 - r)))
    measurable_snd.aemeasurable (p := fun v ↦ ∀ i, g (v i) = g' (v i)) (by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact hcoord)
  have h' := (ae_restrict_iff' measurableSet_Icc).mp h
  have hint : ∀ (b : Fin k → ℝ) (c : Fin (k - 1 - r) → ℝ),
      (∫⁻ u in Ioc 0 1, ((sourceClusterCount b c u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2)) =
        ∫⁻ u in Ioc 0 1, ((sourceClusterCount b c u).choose 2 : ℝ≥0∞) *
          ENNReal.ofReal (g' u ^ 2) := fun b c ↦
    setLIntegral_congr_fun_ae measurableSet_Ioc (h'.mono fun t ht hmem ↦ by
      rw [ht (show t ∈ Icc (0 : ℝ) 1 from ⟨hmem.1.le, hmem.2⟩)])
  filter_upwards [hq] with q hq
  unfold sourceDensity
  rw [hint]
  congr 2
  exact Finset.prod_congr rfl fun i _ ↦ by simp only [Function.comp_apply, hq]

end Modification

/-! ### The corrected local limit for plane forests -/

/-- **The corrected local limit `eq:cv locale` (inventory N12a), plane-forest form.**
Under the critical hypotheses (no measurability of `g = 1/f` is assumed), let `k > r ≥ 0` and
`F₀ ∈ 𝔉⁺_{r,k}`. In the discrete genealogy the children of a merge are ordered by the survival
of their roots (left = the subtree whose root survives).
1. For every cutoff `ε > 0`:
   * the law of `scaledPlaneProb` at the source's samples (iid uniform down-step births, iid
     uniform up-step merge phases) is eventually the image of the auxiliary law by the discrete
     plane functional;
   * the law of the source's exact quantity `sourcePlaneProb`, that is `(n/2)^(2k-1-r)` times
     the probability (including that of picking the sampled vertices) that the sampled vertices
     are the frozen vertices born at `B̃ⁿ` and the merges above `ε n` occur at `C̃ⁿ` and form
     `F₀`, is eventually the image of the former law by the factor `((n/2)/N)^k`;
   * both laws converge weakly as `n → ∞`, to the same limit.
2. As `ε → 0⁺`, these limits converge weakly.
3. The final limit is the law of `g_{r,k}(F₀, B, C)` (`sourceDensity`) at independent uniform
   births `B` and merge times `C` (listed increasingly, `C = cs ∘ rev`). -/
theorem critical_local_limit_plane {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {r : ℕ} (hr : r < k)
    (F₀ : SourceForest r k) :
    (∀ ε, 0 < ε →
      (∀ᶠ n in atTop,
        ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀) : Measure ℝ) =
          (sourceSampleLaw (xa n) n k (k - 1 - r)).map
            (fun q ↦ scaledPlaneProb (xa n) n ε F₀ q.1 q.2)) ∧
      (∀ᶠ n in atTop,
        (((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀)).map
            (fun t ↦ vertexFactor (xa n) n k * t) : Measure ℝ) =
          (sourceSampleLaw (xa n) n k (k - 1 - r)).map
            (fun q ↦ sourcePlaneProb (xa n) n ε F₀ q.1 q.2)) ∧
      Tendsto (fun n ↦ (auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunPlane (xa n) n ε F₀))
        atTop (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunPlane g ε F₀))) ∧
      Tendsto (fun n ↦ ((auxLocalLaw (xa n) n k (k - 1 - r)).map
          (discFunPlane (xa n) n ε F₀)).map (fun t ↦ vertexFactor (xa n) n k * t))
        atTop (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunPlane g ε F₀)))) ∧
    Tendsto (fun ε ↦ (limitLocalLaw g k (k - 1 - r)).map (limitFunPlane g ε F₀)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Plane g F₀))) ∧
    ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Plane g F₀) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure (k - 1 - r))).map
        (fun q ↦ (sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev)).toReal) := by
  obtain ⟨g', hg', -, hae⟩ := exists_measurable_modification hL1 h2
  have hprof := ae_profileMeasure_of_ae_Ioo hae
  have hL1' := hasL1ReciprocalProfile_congr hL1 hprof
  have hpos' := positiveProfile_congr hpos hprof
  have h2' := hasLocalSquareMomentProfile_congr h2 hae
  have hlaw := limitLocalLaw_congr hprof k (k - 1 - r)
  refine ⟨fun ε hε ↦ ⟨eventually_map_discFunPlane_eq hx hL1 hpos hr ε F₀,
      eventually_map_sourcePlaneProb_eq hx hL1 hpos hr ε F₀, ?_, ?_⟩, ?_, ?_⟩
  · rw [hlaw, limitFunPlane_congr hprof hε.le]
    exact tendsto_localLawPlane hx hL1' hpos' h2' hg' hε F₀
  · rw [hlaw, limitFunPlane_congr hprof hε.le]
    exact tendsto_sourcePlaneLaw hx hL1' hpos' h2' hg' hε F₀
  · rw [hlaw, limitFun0Plane_congr hprof]
    refine (tendsto_limitLawPlane_zero hg' h2' F₀).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [limitFunPlane_congr hprof (le_of_lt hε)]
  · rw [hlaw, limitFun0Plane_congr hprof, limitLocalLaw_map_limitFun0Plane hg' hr F₀]
    exact Measure.map_congr ((ae_sourceDensity_congr hprof F₀).mono fun q hq ↦ by
      simp only [hq])


/-- **The forest form of the corrected local limit without measurability of `g`**: the
statement of `critical_local_limit_forest`, under the source hypotheses alone. -/
theorem critical_local_limit_forest_of_profile {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) {r : ℕ}
    (hr : r < k) (F₀ : SourceForest r k) :
    (∀ ε, 0 < ε →
      (∀ᶠ n in atTop,
        ((auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀) : Measure ℝ) =
          (sourceSampleLaw (xa n) n k (k - 1 - r)).map
            (fun q ↦ scaledForestProb (xa n) n ε F₀ q.1 q.2)) ∧
      Tendsto (fun n ↦ (auxLocalLaw (xa n) n k (k - 1 - r)).map (discFunForest (xa n) n ε F₀))
        atTop (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFunForest g ε F₀)))) ∧
    Tendsto (fun ε ↦ (limitLocalLaw g k (k - 1 - r)).map (limitFunForest g ε F₀)) (𝓝[>] 0)
      (𝓝 ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Forest g F₀))) ∧
    ((limitLocalLaw g k (k - 1 - r)).map (limitFun0Forest g F₀) : Measure ℝ) =
      ((cubeMeasure k).prod (cubeMeasure (k - 1 - r))).map
        (fun q ↦ (2 ^ (k - 1 - r) * sourceDensity g F₀ q.1 (q.2 ∘ Fin.rev)).toReal) := by
  obtain ⟨g', hg', -, hae⟩ := exists_measurable_modification hL1 h2
  have hprof := ae_profileMeasure_of_ae_Ioo hae
  have hL1' := hasL1ReciprocalProfile_congr hL1 hprof
  have hpos' := positiveProfile_congr hpos hprof
  have h2' := hasLocalSquareMomentProfile_congr h2 hae
  have hlaw := limitLocalLaw_congr hprof k (k - 1 - r)
  have hF : ∀ ε, 0 ≤ ε → limitFunForest g ε F₀ = limitFunForest g' ε F₀ := fun ε hε ↦ by
    funext z
    simp only [limitFunForest, limitFun_congr hprof hε]
  have hF0 : limitFun0Forest g F₀ = limitFun0Forest g' F₀ := by
    funext z
    simp only [limitFun0Forest, limitFun0_congr hprof]
  obtain ⟨h1, h2'', h3⟩ := critical_local_limit_forest hx hL1' hpos' h2' hg' hr F₀
  refine ⟨fun ε hε ↦ ⟨eventually_map_discFunForest_eq hx hL1 hpos ε F₀, ?_⟩, ?_, ?_⟩
  · rw [hlaw, hF ε hε.le]
    exact (h1 ε hε).2
  · rw [hlaw, hF0]
    refine h2''.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hF ε (le_of_lt hε)]
  · rw [hlaw, hF0, h3]
    exact Measure.map_congr ((ae_sourceDensity_congr hprof F₀).mono fun q hq ↦ by
      simp only [hq])

/-! ### The pattern event and the coalescence times of the sampled vertices -/

theorem patternState_refl {n : ℕ} {b : Fin k → ℕ} {xs : Fin m → ConnState k} {c : Fin m → ℕ}
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ))) (p : ℕ)
    (j : Fin k) : patternState xs c p j j = true := by
  have hanti : StrictAnti c := fun a a' h ↦ by
    have := hadm.strictAnti h
    exact_mod_cast this
  rw [patternState_eq_cons hanti p (Nat.lt_succ_of_le (by simpa using countAbove_le c p))]
  generalize (⟨countAbove c p, _⟩ : Fin (m + 1)) = i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp [diagState]
  · rw [Fin.cons_succ]
    exact hadm.state_mono (show diagState j j = true by simp [diagState]) i

/-- **The pattern event in terms of the coalescence times of the sampled vertices.** Almost
surely, the tracked genealogy of the frozen vertices born at `b` follows the pattern `(xs, c)` at
the phases `≥ p₀` exactly when, for all distinct sampled vertices `j, l` and every phase
`p₀ ≤ p ≤ n`, their coalescence time `coal_n(V_j, V_l)` (`sourceCoalescenceTime`, the
source's `coal_n` for the paper labels `V_j = b j + 1`) is `≥ p` exactly when `j` and `l` are
related in the prescribed state at phase `p`. In other words, the matrix of the coalescence
times of the sampled vertices, truncated below `p₀`, is that of the pattern; the source's
ordered times `C^n_j` and its forest `𝓕^n_r` are read off this matrix. -/
theorem ae_patternEvent_iff_coalescenceTimes {xa : ℕ → ℤ} (hx : IsSigned xa) {n : ℕ}
    (hs : SurvivesThrough xa n) {b : Fin k → ℕ} (hb : ∀ j, b j < n ∧ xa (b j + 1) = -1)
    {xs : Fin m → ConnState k} {c : Fin m → ℕ}
    (hadm : IsAdmissible (fun j ↦ (b j : ℝ)) m n diagState xs (fun i ↦ (c i : ℝ)))
    {p₀ : ℕ} (hp₀ : p₀ ≤ n) :
    ∀ᵐ ω ∂jointLaw (companionSchedule xa) n, (ω ∈ patternEvent n p₀ b xs c ↔
      ∀ j l, j ≠ l → ∀ p, p₀ ≤ p → p ≤ n →
        (p ≤ sourceCoalescenceTime n (frozenVertex b j) (frozenVertex b l) ω ↔
          patternState xs c p j l = true)) := by
  classical
  set u := frozenLabels b with hudef
  have hn : (n : ℕ∞) ≤ extinctionTime (companionSchedule xa) :=
    (companion_before_extinction xa hx hs).le
  have hu : ∀ j, u j ∈ Freezing1.vertexLabels (companionSchedule xa) n := by
    intro j
    simp only [hudef, frozenLabels, Freezing1.vertexLabels, Finset.inr_mem_disjSum,
      Freezing1.frozenIndices, Finset.mem_filter, Finset.mem_range]
    exact ⟨(hb j).1, by simp [companionSchedule, (hb j).2]⟩
  have hC : ∀ j l ω, sourceCoalescenceTime n (frozenVertex b j) (frozenVertex b l) ω =
      coalescenceTime n (u j) (u l) ω := by
    intro j l ω
    simp [sourceCoalescenceTime, frozenVertex, toCompanionLabel, hudef, frozenLabels]
  have hae : ∀ᵐ ω ∂jointLaw (companionSchedule xa) n, ∀ j l, ∀ i ≤ commonBirth n (u j) (u l),
      connectedAt n (u j) (u l) i ω ↔ i ≤ coalescenceTime n (u j) (u l) ω :=
    ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun l ↦
      jointLaw_connected_iff_le_coalescenceTime hn (hu j) (hu l)
  filter_upwards [hae] with ω hω
  -- the tracked state at phase `p` in terms of the coalescence times
  have hkey : ∀ p ≤ n, ∀ j l, j ≠ l →
      (chainState n u (n - p) ω j l = true ↔ p ≤ coalescenceTime n (u j) (u l) ω) := by
    intro p hp j l hjl
    have hcb : commonBirth n (u j) (u l) = min (b j) (b l) := rfl
    have hle := coalescenceTime_le_commonBirth n (u j) (u l) ω
    simp only [chainState, show n - (n - p) = p by omega, trackedState]
    by_cases hborn : Born n p u j ∧ Born n p u l
    · have hpb : p ≤ commonBirth n (u j) (u l) := by
        rw [hcb]
        exact le_min hborn.1 hborn.2
      rw [ite_eq_left hborn, decide_eq_true_iff]
      exact hω j l p hpb
    · rw [ite_eq_right hborn, decide_eq_true_iff]
      constructor
      · intro h
        exact absurd h hjl
      · intro h
        exfalso
        apply hborn
        rw [hcb] at hle
        exact ⟨(h.trans hle).trans (min_le_left _ _), (h.trans hle).trans (min_le_right _ _)⟩
  simp only [hC]
  constructor
  · intro hev j l hjl p hp₀p hpn
    have h := hev (n - p) (by omega)
    rw [show n - (n - p) = p by omega] at h
    rw [← hkey p hpn j l hjl, h]
  · intro h N hN
    funext j l
    by_cases hjl : j = l
    · subst hjl
      rw [patternState_refl hadm]
      simp [chainState, trackedState_refl]
    · have h1 := hkey (n - N) (by omega) j l hjl
      rw [show n - (n - N) = N by omega] at h1
      exact Bool.eq_iff_iff.mpr (h1.trans (h j l hjl (n - N) (by omega) (by omega)))

end Freezing2.CriticalLocalLimit
