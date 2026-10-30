module

public import Freezing2.Companion.ForwardLaw
public import Freezing2.MainResults.SupercriticalNonTight

/-!
# Uniform recursive trees and the absence of supercritical scaling limits

Two remarks of the introduction of the source.

* **U01, first clause.** When every sign is `+1`, nothing ever freezes, and uniform
  attachment with freezing is the uniform recursive tree: each new vertex attaches to a
  uniformly chosen vertex among all existing ones. The law `urtLaw` below is defined with
  no freezing and no active set: it chooses uniformly in `s.vertices` and calls
  `Freezing1.Forward.attach`. Under the all-`true` sign sequence the active set equals the
  vertex set almost surely, so `Freezing1.Forward.treeLaw` agrees with `urtLaw` at every
  time (`treeLaw_allPlus_eq_urtLaw`).
* **No scaling limit in the supercritical case.** For `α ∈ (1/2, 1)` the trees grow
  polynomially but have no scaling limit: no subsequence of the laws of the scaled
  measured trees converges weakly in the GHP topology (`supercritical_no_weak_limit`).
  The proof uses the portmanteau theorem on the open sets of classes covered by `K` open
  `r`-balls, whose union over `K` is the whole space.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Freezing2

/-! ### The uniform recursive tree -/

section UniformRecursiveTree

open Freezing1

/-- One step of the uniform recursive tree: choose a uniform vertex among all existing
vertices of `s` and attach the fresh vertex `t` to it. -/
noncomputable def urtTransition (s : Forward.State) (t : ℕ) : Measure Forward.State :=
  (Measure.uniformOfFinset s.vertices).map (fun v ↦ Forward.attach s t v)

/-- The law of the uniform recursive tree after `n` attachment steps, started from the
single root `0`. Vertex `n + 1` attaches to a uniform vertex of the current tree. -/
noncomputable def urtLaw : ℕ → Measure Forward.State
  | 0 => Measure.dirac Forward.initial
  | n + 1 => (urtLaw n).bind (fun s ↦ urtTransition s (n + 1))

theorem urtLaw_zero : urtLaw 0 = Measure.dirac Forward.initial := rfl

theorem urtLaw_succ (n : ℕ) :
    urtLaw (n + 1) = (urtLaw n).bind (fun s ↦ urtTransition s (n + 1)) := rfl

/-- Under the all-`+1` sign sequence no vertex is ever frozen: the active set is the whole
vertex set almost surely. -/
theorem treeLaw_allPlus_active_eq_vertices (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw (fun _ ↦ true) n, s.active = s.vertices := by
  apply Forward.treeLaw_ae_induction (fun _ ↦ true) (fun _ s ↦ s.active = s.vertices)
  · rfl
  · intro _ s hs _
    exact hs
  · intro _ s hs v hv
    simp only [Forward.step, hv, ↓reduceIte, Forward.attach]
    rw [hs]

/-- When every vertex is active, a `+1` step of the forward construction is a uniform
recursive tree step. -/
theorem transitionLaw_true_eq_urtTransition {s : Forward.State} (hs : s.active = s.vertices)
    (hne : s.vertices.Nonempty) (t : ℕ) :
    Forward.transitionLaw s t true = urtTransition s t := by
  rw [Forward.transitionLaw, ite_eq_left (hs ▸ hne), urtTransition, hs]
  apply Measure.map_congr
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (t := ((s.vertices : Set ℕ))ᶜ) ?_ ?_
  · intro v hv hvs
    apply hv
    have hva : v ∈ s.active := hs ▸ hvs
    simp only [Forward.step, hva, ↓reduceIte]
  · classical
    rw [Measure.uniformOfFinset_apply]
    simp

/-- **U01, first clause.** With all signs `+1`, uniform attachment with freezing is the
uniform recursive tree: the forward law equals `urtLaw` at every time. -/
theorem treeLaw_allPlus_eq_urtLaw (n : ℕ) : Forward.treeLaw (fun _ ↦ true) n = urtLaw n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [urtLaw_succ, ← ih]
    change (Forward.treeLaw (fun _ ↦ true) n).bind
      (fun s ↦ Forward.transitionLaw s (n + 1) true) = _
    apply Measure.bind_congr_right
    filter_upwards [treeLaw_allPlus_active_eq_vertices n,
      Forward.treeLaw_valid (fun _ ↦ true) n] with s hs hv
    exact transitionLaw_true_eq_urtTransition hs ⟨0, hv.root_mem⟩ (n + 1)

instance urtLaw_probability (n : ℕ) : IsProbabilityMeasure (urtLaw n) := by
  rw [← treeLaw_allPlus_eq_urtLaw]
  infer_instance

end UniformRecursiveTree

/-! ### No weak limit in the supercritical regime -/

section NoWeakLimit

open GHCovering MeasuredGHSpace

universe u

/-- If, at a fixed radius `r > 0` and for every `K`, the probability of not being covered
by `K` open `r`-balls tends to one, then the sequence of laws has no weak limit. -/
theorem not_tendsto_of_not_coverable {μ : ℕ → ProbabilityMeasure MeasuredGHSpace.{u}} {r : ℝ}
    (hr : 0 < r)
    (h : ∀ K : ℕ, Tendsto (fun n ↦ (μ n : Measure MeasuredGHSpace.{u})
      {X | ¬ Coverable (underlyingGH X).Rep K r}) atTop (𝓝 1))
    (Q : ProbabilityMeasure MeasuredGHSpace.{u}) : ¬ Tendsto μ atTop (𝓝 Q) := by
  intro hQ
  have hopen (K : ℕ) : IsOpen {X : MeasuredGHSpace.{u} | Coverable (underlyingGH X).Rep K r} :=
    (isOpen_setOf_coverable K r).preimage continuous_underlyingGH
  have hzero (K : ℕ) :
      (Q : Measure MeasuredGHSpace.{u}) {X | Coverable (underlyingGH X).Rep K r} = 0 := by
    have hcompl : {X : MeasuredGHSpace.{u} | Coverable (underlyingGH X).Rep K r} =
        {X | ¬ Coverable (underlyingGH X).Rep K r}ᶜ := by
      ext X
      simp
    have hlim : Tendsto (fun n ↦ (μ n : Measure MeasuredGHSpace.{u})
        {X | Coverable (underlyingGH X).Rep K r}) atTop (𝓝 0) := by
      have hsub := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) (h K)
        (Or.inl ENNReal.one_ne_top)
      rw [tsub_self] at hsub
      refine hsub.congr fun n ↦ ?_
      rw [hcompl, prob_compl_eq_one_sub]
      exact (hopen K).measurableSet.compl
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hQ (hopen K)
    rw [hlim.liminf_eq] at hle
    exact le_antisymm hle zero_le
  have hunion : (⋃ K : ℕ, {X : MeasuredGHSpace.{u} | Coverable (underlyingGH X).Rep K r}) =
      univ :=
    eq_univ_of_forall fun X ↦ mem_iUnion.mpr (exists_coverable (underlyingGH X).Rep hr)
  have hnull := measure_iUnion_null hzero
  rw [hunion, measure_univ] at hnull
  exact one_ne_zero hnull

/-- **No scaling limit in the supercritical case.** For `α ∈ (1/2, 1)`, under the
hypotheses of `supercritical_not_coverable`, no subsequence of the laws of the scaled
forward measured trees converges weakly in the GHP topology. -/
theorem supercritical_no_weak_limit {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) :
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Q : ProbabilityMeasure MeasuredGHSpace.{0},
      ¬ Tendsto (fun n ↦ forwardMeasuredTreeLaw x α (φ n)) atTop (𝓝 Q) := by
  intro φ hφ Q
  obtain ⟨r, hr, hK⟩ := supercritical_not_coverable hx hαhalf hα1 hf hL1 h2
  exact not_tendsto_of_not_coverable hr (fun K ↦ (hK K).comp hφ.tendsto_atTop) Q

end NoWeakLimit

end Freezing2
