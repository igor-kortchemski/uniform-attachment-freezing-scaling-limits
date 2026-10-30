module

public import Freezing2.Companion.ForwardLaw
public import Freezing2.Probability.CoalescentForests
public import Freezing2.MainResults.BoundedPopulation

/-!
# Small model facts stated in the source

This file states three short claims of `attachement-uniforme-2-final.tex` that no other
declaration exports (omission scan of 30 October 2026).

## U06 (L478–L481): the forward trees

* `forward_treeLaw_eq_of_eqOn`, `freezingTreeLaw_eq_of_eqOn`: the law of `𝒯_n` depends only
  on the signs `X_1, …, X_n`.
* `ForwardExtends s s'`: `s'` extends `s`. Its vertices contain those of `s`, its graph
  contains the graph of `s`, the tree of `s` is an induced subgraph, and the heights and
  parents of the old vertices are unchanged. `ForwardExtends.tree_embedding`: the tree of `s`
  then embeds in the tree of `s'` as an induced subgraph, by the identity on vertex labels.
* `forward_step_vertices_subset`, `forward_step_graph_le`: one transition of Algorithm 1
  never removes a vertex or an edge. `forward_step_extends`: from a valid state at time `n`,
  the transition at time `n + 1` is an extension.
* `forward_run_extends`: along the deterministic trajectory, `𝒯_m ⊆ 𝒯_n` for `m ≤ n`.
* The natural coupling of the laws: `forwardEvolve x m j s` is the law of the state `j` steps
  after the state `s` at time `m`, and `forward_treeLaw_add_eq_bind` shows that
  `treeLaw x (m + j)` is `treeLaw x m` followed by this evolution.
  `forward_treeLaw_ae_evolve_extends`: under this coupling `𝒯_m ⊆ 𝒯_{m+j}` almost surely.
* Stationarity: `forward_treeLaw_succ_eq_self_iff` shows that
  `treeLaw x (n + 1) = treeLaw x n` if and only if `τ ≤ n`. Hence the sequence of laws is
  stationary exactly from `τ` on, and only when `τ < ∞`. Pathwise,
  `forward_treeLaw_ae_transition_eq` and `forward_treeLaw_ae_transition_ne` show that the
  transition at time `n + 1` almost surely fixes the tree if `τ ≤ n` and almost surely
  changes it if `n < τ`.

## U29 (L1419): the coalescent densities sum to one

* `planeLaw_univ_eq_one`: the plane law is a probability measure.
* `planeLaw_planeForest_fibre`: the mass of the fibre `{𝓕 = F₀}` is the integral of
  `g_{r,k}(F₀, ·, ·)` over `[0,1]^k × ℝ^{k-1-r}`.
* `sum_lintegral_sourceDensity_eq_one`, `sum_lintegral_indicator_sourceDensity_eq_one`:
  `∑_{r<k} ∑_{F₀ ∈ 𝔉⁺_{r,k}} ∫ 1_{[0,1]^k}(b) g_{r,k}(F₀, b, c) db dc = 1`.

## U20 / L1046: the `L^p` height limit under bounded population

* `bounded_population_height_tendsto_Lp`: under the hypotheses of
  `bounded_population_GH_limit`, `Height(𝒯_n)/h_n^+ → 1` in `L^p` for every real `p ≥ 1`.
  `bounded_population_height_tendsto_Lp_harmonic` states the same limit with the integer-sign
  height scale `harmonicUpTotal x n`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Freezing2

/-! ### U06: the forward trees -/

section ForwardTrees

open Freezing1.Forward

/-- **U06 (L480).** The law of `𝒯_n` depends only on the first `n` signs: two sign
sequences that agree on `[1, n]` give the same law at time `n`. -/
theorem forward_treeLaw_eq_of_eqOn {x y : Freezing1.SignSequence} {n : ℕ}
    (h : ∀ k, 1 ≤ k → k ≤ n → x k = y k) : treeLaw x n = treeLaw y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (treeLaw x n).bind (fun s ↦ transitionLaw s (n + 1) (x (n + 1))) =
      (treeLaw y n).bind (fun s ↦ transitionLaw s (n + 1) (y (n + 1)))
    rw [ih (fun k hk1 hkn ↦ h k hk1 (Nat.le_succ_of_le hkn)),
      h (n + 1) (Nat.le_add_left 1 n) le_rfl]

/-- **U06 (L480), integer signs.** The tree law of the `n`-th row depends only on the entries
`1, …, n` of that row. -/
theorem freezingTreeLaw_eq_of_eqOn {x y : ℕ → ℕ → ℤ} {n : ℕ}
    (h : ∀ k, 1 ≤ k → k ≤ n → x n k = y n k) : freezingTreeLaw x n = freezingTreeLaw y n :=
  forward_treeLaw_eq_of_eqOn fun k hk1 hkn ↦ by simp [companionSchedule, h k hk1 hkn]

/-- One transition of Algorithm 1 never removes a vertex. -/
theorem forward_step_vertices_subset (s : State) (t : ℕ) (sign : Bool) (v : ℕ) :
    s.vertices ⊆ (step s t sign v).vertices := by
  unfold step
  split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl
  · exact subset_rfl

/-- One transition of Algorithm 1 never removes an edge. -/
theorem forward_step_graph_le (s : State) (t : ℕ) (sign : Bool) (v : ℕ) :
    s.graph ≤ (step s t sign v).graph := by
  unfold step
  split_ifs
  · exact le_sup_left
  · exact le_rfl
  · exact le_rfl

/-- The state `s'` extends `s`. Its vertices and edges contain those of `s`, two old vertices
are adjacent in `s'` exactly when they are adjacent in `s`, and the heights and parents of
the old vertices are unchanged. -/
def ForwardExtends (s s' : State) : Prop :=
  s.vertices ⊆ s'.vertices ∧ s.graph ≤ s'.graph ∧
    (∀ u ∈ s.vertices, ∀ w ∈ s.vertices, s'.graph.Adj u w ↔ s.graph.Adj u w) ∧
    (∀ u ∈ s.vertices, s'.height u = s.height u) ∧
    (∀ u ∈ s.vertices, s'.parent u = s.parent u)

theorem ForwardExtends.refl (s : State) : ForwardExtends s s :=
  ⟨subset_rfl, le_rfl, fun _ _ _ _ ↦ Iff.rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem ForwardExtends.trans {s₁ s₂ s₃ : State} (h₁₂ : ForwardExtends s₁ s₂)
    (h₂₃ : ForwardExtends s₂ s₃) : ForwardExtends s₁ s₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.1.trans h₂₃.2.1,
    fun u hu w hw ↦ (h₂₃.2.2.1 u (h₁₂.1 hu) w (h₁₂.1 hw)).trans (h₁₂.2.2.1 u hu w hw),
    fun u hu ↦ (h₂₃.2.2.2.1 u (h₁₂.1 hu)).trans (h₁₂.2.2.2.1 u hu),
    fun u hu ↦ (h₂₃.2.2.2.2 u (h₁₂.1 hu)).trans (h₁₂.2.2.2.2 u hu)⟩

/-- An extension contains the old finite tree as an induced subgraph: the identity on vertex
labels is a graph embedding of `s.tree` into `s'.tree`. -/
theorem ForwardExtends.tree_embedding {s s' : State} (h : ForwardExtends s s') :
    ∃ f : s.tree ↪g s'.tree, ∀ u, (f u : ℕ) = u :=
  ⟨{ toFun := fun u ↦ ⟨u.1, h.1 u.2⟩
     inj' := fun _ _ huw ↦ Subtype.ext (Subtype.mk.inj huw)
     map_rel_iff' := fun {u w} ↦ h.2.2.1 u.1 u.2 w.1 w.2 }, fun _ ↦ rfl⟩

/-- **U06 (L480), one step.** From a valid state at time `n`, every transition at time
`n + 1` extends the tree. -/
theorem forward_step_extends {n : ℕ} {s : State} (hs : ValidAt n s) (sign : Bool) (v : ℕ) :
    ForwardExtends s (step s (n + 1) sign v) := by
  have hfresh : ∀ u ∈ s.vertices, u ≠ n + 1 := fun u hu he ↦ by
    have := hs.vertices_le u hu
    omega
  refine ⟨forward_step_vertices_subset s (n + 1) sign v, forward_step_graph_le s (n + 1) sign v,
    ?_, ?_, ?_⟩
  · intro u hu w hw
    unfold step
    split_ifs
    · change s.graph.Adj u w ∨ (SimpleGraph.edge v (n + 1)).Adj u w ↔ _
      simp [SimpleGraph.edge_adj, hfresh u hu, hfresh w hw]
    · exact Iff.rfl
    · exact Iff.rfl
  · intro u hu
    unfold step
    split_ifs
    · simp [attach, hfresh u hu]
    · rfl
    · rfl
  · intro u hu
    unfold step
    split_ifs
    · simp [attach, hfresh u hu]
    · rfl
    · rfl

/-- **U06 (L480), deterministic trajectory.** Along the forward construction driven by any
choices, the trees are non-decreasing: `𝒯_m ⊆ 𝒯_n` for `m ≤ n`. -/
theorem forward_run_extends (x : Freezing1.SignSequence) (choice : ℕ → ℕ) {m n : ℕ}
    (hmn : m ≤ n) : ForwardExtends (run x choice m) (run x choice n) := by
  induction hmn with
  | refl => exact ForwardExtends.refl _
  | step _ ih => exact ih.trans (forward_step_extends (run_valid x choice _) _ _)

/-- Almost every transition from a valid state at time `n` is valid at time `n + 1`. -/
theorem forward_transitionLaw_ae_valid {n : ℕ} {s : State} (hs : ValidAt n s) (sign : Bool) :
    ∀ᵐ s' ∂transitionLaw s (n + 1) sign, ValidAt (n + 1) s' :=
  transitionLaw_ae s (n + 1) sign _ (fun _ ↦ hs.mono (Nat.le_succ n)) (fun v _ ↦ hs.step sign v)

/-- Almost every transition from a valid state is an extension. -/
theorem forward_transitionLaw_ae_extends {n : ℕ} {s : State} (hs : ValidAt n s) (sign : Bool) :
    ∀ᵐ s' ∂transitionLaw s (n + 1) sign, ForwardExtends s s' :=
  transitionLaw_ae s (n + 1) sign _ (fun _ ↦ ForwardExtends.refl s)
    (fun v _ ↦ forward_step_extends hs sign v)

/-- The forward recursion: the law at time `n + 1` is the law at time `n` followed by one
transition. -/
theorem forward_treeLaw_succ_eq_bind (x : Freezing1.SignSequence) (n : ℕ) :
    treeLaw x (n + 1) = (treeLaw x n).bind (fun s ↦ transitionLaw s (n + 1) (x (n + 1))) :=
  rfl

/-- **U06 (L480), one-step coupling.** Under the forward recursion, the tree at time `n + 1`
almost surely extends the tree at time `n`. -/
theorem forward_treeLaw_ae_extends (x : Freezing1.SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, ∀ᵐ s' ∂transitionLaw s (n + 1) (x (n + 1)), ForwardExtends s s' :=
  (treeLaw_valid x n).mono fun _ hs ↦ forward_transitionLaw_ae_extends hs _

/-- Almost-sure properties pass through a bind of state laws. -/
theorem forward_bind_ae {μ : Measure State} {κ : State → Measure State} {P Q : State → Prop}
    (hP : ∀ᵐ s ∂μ, P s) (hPQ : ∀ s, P s → ∀ᵐ s' ∂κ s, Q s') :
    ∀ᵐ s' ∂μ.bind κ, Q s' := by
  rw [ae_iff, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hP] with s hs
  exact ae_iff.mp (hPQ s hs)

/-- The law of the state `j` steps after a given state at time `m`. -/
noncomputable def forwardEvolve (x : Freezing1.SignSequence) (m : ℕ) :
    ℕ → State → Measure State
  | 0 => Measure.dirac
  | j + 1 => fun s ↦
    (forwardEvolve x m j s).bind fun s' ↦ transitionLaw s' (m + j + 1) (x (m + j + 1))

/-- The law at time `m + j` is the law at time `m` followed by `j` further steps. -/
theorem forward_treeLaw_add_eq_bind (x : Freezing1.SignSequence) (m j : ℕ) :
    treeLaw x (m + j) = (treeLaw x m).bind (forwardEvolve x m j) := by
  induction j with
  | zero =>
    change treeLaw x m = (treeLaw x m).bind Measure.dirac
    rw [Measure.bind_dirac]
  | succ j ih =>
    rw [← add_assoc, forward_treeLaw_succ_eq_bind, ih,
      Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    rfl

/-- From a valid state at time `m`, the state `j` steps later is almost surely valid at time
`m + j` and extends it. -/
theorem forward_evolve_ae_extends (x : Freezing1.SignSequence) {m : ℕ} {s : State}
    (hs : ValidAt m s) (j : ℕ) :
    ∀ᵐ s' ∂forwardEvolve x m j s, ValidAt (m + j) s' ∧ ForwardExtends s s' := by
  induction j with
  | zero =>
    change ∀ᵐ s' ∂Measure.dirac s, ValidAt (m + 0) s' ∧ ForwardExtends s s'
    exact (ae_dirac_iff (by trivial)).mpr ⟨hs, ForwardExtends.refl s⟩
  | succ j ih =>
    refine forward_bind_ae ih fun s' hs' ↦ ?_
    filter_upwards [forward_transitionLaw_ae_extends hs'.1 (x (m + j + 1)),
      forward_transitionLaw_ae_valid hs'.1 (x (m + j + 1))] with s'' h1 h2
    exact ⟨h2, hs'.2.trans h1⟩

/-- **U06 (L480), coupling.** Under the natural coupling of `treeLaw x m` and
`treeLaw x (m + j)` (`forward_treeLaw_add_eq_bind`), the later tree almost surely extends the
earlier one: the trees are non-decreasing. -/
theorem forward_treeLaw_ae_evolve_extends (x : Freezing1.SignSequence) (m j : ℕ) :
    ∀ᵐ s ∂treeLaw x m, ∀ᵐ s' ∂forwardEvolve x m j s, ForwardExtends s s' :=
  (treeLaw_valid x m).mono fun _ hs ↦ (forward_evolve_ae_extends x hs j).mono fun _ h ↦ h.2

/-- After extinction there is almost surely no active vertex. -/
theorem forward_treeLaw_ae_active_empty {x : Freezing1.SignSequence} {n : ℕ}
    (hτ : Freezing1.extinctionTime x ≤ n) : ∀ᵐ s ∂treeLaw x n, s.active = ∅ := by
  have hfin : Freezing1.extinctionTime x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hτ
  obtain ⟨N, hNτ⟩ : ∃ N : ℕ, (N : ℕ∞) = Freezing1.extinctionTime x :=
    ⟨_, ENat.natCast_toNat hfin⟩
  obtain ⟨j, hjN, hj0⟩ := (Freezing1.extinctionTime_le_iff x N).mp hNτ.ge
  have hNj : N ≤ j := by
    have := (Freezing1.extinctionTime_le_iff x j).mpr ⟨j, le_rfl, hj0⟩
    rw [← hNτ] at this
    exact_mod_cast this
  obtain rfl : j = N := le_antisymm hjN hNj
  have hjn : j ≤ n := by
    rw [← hNτ] at hτ
    exact_mod_cast hτ
  have h0 : ∀ᵐ s ∂treeLaw x j, s.active = ∅ := by
    filter_upwards [treeLaw_counts x j hNτ.le] with s hs
    have h := hs.1
    rw [hj0] at h
    exact Finset.card_eq_zero.mp (by exact_mod_cast h)
  clear hτ hfin
  induction n, hjn using Nat.le_induction with
  | base => exact h0
  | succ m _ ih =>
    exact forward_bind_ae ih fun s hs ↦
      transitionLaw_ae s _ _ _ (fun h ↦ h) (fun v hv ↦ absurd hv (by simp [hs]))

/-- **U06 (L480), stationarity after `τ`.** If `τ ≤ n`, the law of the tree does not change
at time `n + 1`. -/
theorem forward_treeLaw_succ_eq_self {x : Freezing1.SignSequence} {n : ℕ}
    (hτ : Freezing1.extinctionTime x ≤ n) : treeLaw x (n + 1) = treeLaw x n := by
  rw [forward_treeLaw_succ_eq_bind]
  conv_rhs => rw [← Measure.bind_dirac (m := treeLaw x n)]
  exact Measure.bind_congr_right ((forward_treeLaw_ae_active_empty hτ).mono fun s hs ↦
    transitionLaw_eq_dirac_of_empty s _ _ hs)

/-- **U06 (L480), no stationarity before `τ`.** If `n < τ`, the law of the tree changes at
time `n + 1`: its number of active vertices moves by one. -/
theorem forward_treeLaw_succ_ne {x : Freezing1.SignSequence} {n : ℕ}
    (hτ : (n : ℕ∞) < Freezing1.extinctionTime x) : treeLaw x (n + 1) ≠ treeLaw x n := by
  intro heq
  have hτ1 : ((n + 1 : ℕ) : ℕ∞) ≤ Freezing1.extinctionTime x := by
    rw [Nat.cast_succ]
    exact Order.add_one_le_of_lt hτ
  have h1 := treeLaw_counts x (n + 1) hτ1
  rw [heq] at h1
  have h0 := treeLaw_counts x n hτ.le
  obtain ⟨s, hs1, hs0⟩ := (h1.and h0).exists
  have h := Freezing1.activeCount_succ x n
  rw [← hs1.1, ← hs0.1] at h
  split_ifs at h <;> omega

/-- **U06 (L480), stationarity.** The law of `𝒯_{n+1}` equals that of `𝒯_n` if and only if
`τ ≤ n`. So the sequence of laws becomes stationary if and only if `τ < ∞`, and then first
at time `τ`. -/
theorem forward_treeLaw_succ_eq_self_iff (x : Freezing1.SignSequence) (n : ℕ) :
    treeLaw x (n + 1) = treeLaw x n ↔ Freezing1.extinctionTime x ≤ n := by
  refine ⟨fun h ↦ ?_, forward_treeLaw_succ_eq_self⟩
  by_contra hlt
  exact forward_treeLaw_succ_ne (lt_of_not_ge hlt) h

/-- **U06 (L480), pathwise stationarity after `τ`.** If `τ ≤ n`, the transition at time
`n + 1` almost surely leaves the tree unchanged. -/
theorem forward_treeLaw_ae_transition_eq {x : Freezing1.SignSequence} {n : ℕ}
    (hτ : Freezing1.extinctionTime x ≤ n) :
    ∀ᵐ s ∂treeLaw x n, ∀ᵐ s' ∂transitionLaw s (n + 1) (x (n + 1)), s' = s :=
  (forward_treeLaw_ae_active_empty hτ).mono fun s hs ↦
    transitionLaw_ae s _ _ _ (fun _ ↦ rfl) (fun v hv ↦ absurd hv (by simp [hs]))

/-- A transition with a legal choice changes the state: attaching adds the fresh vertex
`n + 1`, and freezing removes an active vertex. -/
theorem forward_step_ne_self {n : ℕ} {s : State} (hs : ValidAt n s) (sign : Bool) {v : ℕ}
    (hv : v ∈ s.active) : step s (n + 1) sign v ≠ s := by
  intro heq
  unfold step at heq
  rw [ite_eq_left hv] at heq
  cases sign
  · have h := congrArg State.active heq
    simp only [Bool.false_eq_true, ↓reduceIte, freeze] at h
    have := Finset.card_erase_of_mem hv
    rw [h] at this
    have := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  · have h := congrArg State.vertices heq
    simp only [↓reduceIte, attach] at h
    have hmem : n + 1 ∈ s.vertices := h ▸ Finset.mem_insert_self _ _
    have := hs.vertices_le _ hmem
    omega

/-- **U06 (L480), pathwise non-stationarity before `τ`.** If `n < τ`, the transition at time
`n + 1` almost surely changes the tree. -/
theorem forward_treeLaw_ae_transition_ne {x : Freezing1.SignSequence} {n : ℕ}
    (hτ : (n : ℕ∞) < Freezing1.extinctionTime x) :
    ∀ᵐ s ∂treeLaw x n, ∀ᵐ s' ∂transitionLaw s (n + 1) (x (n + 1)), s' ≠ s := by
  filter_upwards [treeLaw_valid x n, treeLaw_active_nonempty x n hτ] with s hs hne
  exact transitionLaw_ae s _ _ _ (fun he ↦ absurd he hne.ne_empty)
    (fun v hv ↦ forward_step_ne_self hs _ hv)

end ForwardTrees

/-! ### U29: the coalescent densities sum to one -/

section CoalescentNormalization

open CoalescentDensity

variable {g : ℝ → ℝ} {k : ℕ}

/-- The plane law is a probability measure. -/
theorem planeLaw_univ_eq_one (hg : Measurable g) (hg2 : LocSqIntegrable g) :
    planeLaw g k univ = 1 := by
  have h := map_forgetOrders_planeLaw (k := k) hg hg2
  rw [map_decodeHistory_criticalGenealogyLimit hg hg2] at h
  have h1 := congrArg (fun ν : Measure (HistorySpace k) ↦ ν univ) h
  rw [Measure.map_apply measurable_forgetOrders MeasurableSet.univ, preimage_univ,
    historyLaw_univ hg hg2] at h1
  exact h1

/-- The mass of the fibre `{𝓕 = F₀}` is the integral of `g_{r,k}(F₀, ·, ·)` over
`[0,1]^k × ℝ^{k-1-r}`. -/
theorem planeLaw_planeForest_fibre (hg : Measurable g) {r : ℕ} (hr : r < k)
    (F₀ : SourceForest r k) :
    planeLaw g k {h | planeForest h = some ⟨r, F₀⟩} =
      ∫⁻ p in CoalescentDensity.unitCube k ×ˢ univ, sourceDensity g F₀ p.1 p.2 := by
  have h := congrArg (fun ν : Measure ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ)) ↦ ν univ)
    (map_restrict_planeLaw hg hr F₀)
  rw [Measure.map_apply (measurable_birthUpper r) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h

/-- A forest of a plane history lies in some `𝔉⁺_{r,k}` with `r < k`. -/
theorem planeForest_some_lt {h : PlaneHistorySpace k} {r : ℕ} {F : SourceForest r k}
    (hF : planeForest h = some ⟨r, F⟩) : r < k := by
  have := patternForest_eq_some_imp ((planeForest_eq_some_iff h r F).mp hF)
  omega

/-- **U29 (L1419).** The densities of the coalescent sum to one:
`∑_{0 ≤ r ≤ k-1} ∑_{F₀ ∈ 𝔉⁺_{r,k}} ∫_{[0,1]^k × ℝ^{k-1-r}} g_{r,k}(F₀, b, c) db dc = 1`. -/
theorem sum_lintegral_sourceDensity_eq_one (hg : Measurable g) (hg2 : LocSqIntegrable g)
    (hk : 0 < k) :
    ∑ r ∈ Finset.range k, ∑ F₀ : SourceForest r k,
      ∫⁻ p in CoalescentDensity.unitCube k ×ˢ univ, sourceDensity g F₀ p.1 p.2 = 1 := by
  set μ := planeLaw g k with hμ
  set T : Finset (Σ r : ℕ, SourceForest r k) :=
    (Finset.range k).sigma fun _ ↦ Finset.univ with hT
  set S : (Σ r : ℕ, SourceForest r k) → Set (PlaneHistorySpace k) :=
    fun a ↦ {h | planeForest h = some a} with hS
  have hdisj : (T : Set (Σ r : ℕ, SourceForest r k)).PairwiseDisjoint S := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun h ha hb ↦ hab ?_
    simp only [hS, mem_ofPred_eq] at ha hb
    rw [ha] at hb
    exact Option.some_injective _ hb
  have hmeas : ∀ a ∈ T, MeasurableSet (S a) := by
    rintro ⟨r, F⟩ _
    exact measurableSet_planeForest_eq F
  have hunion : μ (⋃ a ∈ T, S a) = ∑ a ∈ T, μ (S a) := measure_biUnion_finset hdisj hmeas
  have hsum : ∑ a ∈ T, μ (S a) = ∑ r ∈ Finset.range k, ∑ F₀ : SourceForest r k,
      ∫⁻ p in CoalescentDensity.unitCube k ×ˢ univ, sourceDensity g F₀ p.1 p.2 := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r hr ↦ Finset.sum_congr rfl fun F₀ _ ↦ ?_
    exact planeLaw_planeForest_fibre hg (Finset.mem_range.mp hr) F₀
  rw [← hsum, ← hunion]
  have huniv : μ univ = 1 := planeLaw_univ_eq_one hg hg2
  apply le_antisymm
  · rw [← huniv]
    exact measure_mono (subset_univ _)
  · have hcover : univ ⊆ {h : PlaneHistorySpace k | planeForest h = none} ∪ ⋃ a ∈ T, S a := by
      intro h _
      rcases hpf : planeForest h with _ | ⟨r, F⟩
      · exact Or.inl hpf
      · refine Or.inr (mem_iUnion₂.mpr ⟨⟨r, F⟩, ?_, hpf⟩)
        simp [hT, planeForest_some_lt hpf]
    calc
      (1 : ℝ≥0∞) = μ univ := huniv.symm
      _ ≤ μ ({h : PlaneHistorySpace k | planeForest h = none} ∪ ⋃ a ∈ T, S a) :=
        measure_mono hcover
      _ ≤ μ {h : PlaneHistorySpace k | planeForest h = none} + μ (⋃ a ∈ T, S a) :=
        measure_union_le _ _
      _ = μ (⋃ a ∈ T, S a) := by
        rw [hμ, planeLaw_planeForest_eq_none hk, zero_add]

/-- **U29 (L1419), indicator form.**
`∑_{0 ≤ r ≤ k-1} ∑_{F₀ ∈ 𝔉⁺_{r,k}} ∫ 1_{[0,1]^k}(b) g_{r,k}(F₀, b, c) db dc = 1`. -/
theorem sum_lintegral_indicator_sourceDensity_eq_one (hg : Measurable g)
    (hg2 : LocSqIntegrable g) (hk : 0 < k) :
    ∑ r ∈ Finset.range k, ∑ F₀ : SourceForest r k,
      ∫⁻ p : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ),
        (CoalescentDensity.unitCube k).indicator 1 p.1 * sourceDensity g F₀ p.1 p.2 = 1 := by
  rw [← sum_lintegral_sourceDensity_eq_one hg hg2 hk]
  refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun F₀ _ ↦ ?_
  have hcube : MeasurableSet (CoalescentDensity.unitCube k) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  rw [← lintegral_indicator (hcube.prod MeasurableSet.univ)]
  refine lintegral_congr fun p ↦ ?_
  by_cases hp : p.1 ∈ CoalescentDensity.unitCube k
  · have hp' : p ∈ CoalescentDensity.unitCube k ×ˢ (univ : Set (Fin (k - 1 - r) → ℝ)) :=
      ⟨hp, mem_univ _⟩
    simp [hp, hp']
  · have hp' : p ∉ CoalescentDensity.unitCube k ×ˢ (univ : Set (Fin (k - 1 - r) → ℝ)) :=
      fun h ↦ hp h.1
    simp [hp, hp']

end CoalescentNormalization

/-! ### U20 / L1046: the `L^p` height limit under bounded population -/

/-- **U20 / L1046.** Under the hypotheses of `bounded_population_GH_limit` (`τ(Xⁿ) > n` and
`Sⁿ_k ≤ M` for all `k ≤ n`), `Height(𝒯_n) / h_n^+ → 1` in `L^p` for every real `p ≥ 1`. -/
theorem bounded_population_height_tendsto_Lp {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hM : ∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n ↦ eLpNorm
      (fun s : Freezing1.Forward.State ↦ (Freezing1.Forward.treeHeight s : ℝ) /
        Freezing1.heightScale (companionSchedule (x n)) n - 1)
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hM
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  set y := initialRowExtension x with hydef
  have hy := admissible_initialRowExtension hx
  have hyM : ∀ n k : ℕ, k ≤ n → activeCount (y n) k ≤ M := by
    intro n k hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rw [activeCount_zero]
      exact_mod_cast hM1
    · simp only [hydef, initialRowExtension, ite_eq_right (Nat.ne_of_gt hn)]
      exact hM n k hk
  have hτ (n : ℕ) : (n : ℕ∞) < Freezing1.extinctionTime (companionSchedule (y n)) :=
    companion_before_extinction (y n) (hy n).1 (hy n).2
  have hlog := tendsto_log_div_heightScale_of_bounded (y := y) (fun n _ ↦ hy n) hyM
  have hLp := Freezing1.maximum_height_tendsto_Lp (fun n ↦ companionSchedule (y n)) hτ hlog hp
  apply hLp.congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  simp only [freezingTreeLaw, ← hn, hydef]

/-- **U20 / L1046, integer-sign height scale.** The same `L^p` limit with
`h_n^+ = harmonicUpTotal x n`. -/
theorem bounded_population_height_tendsto_Lp_harmonic {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hM : ∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n ↦ eLpNorm
      (fun s : Freezing1.Forward.State ↦ (Freezing1.Forward.treeHeight s : ℝ) /
        harmonicUpTotal x n - 1)
      (ENNReal.ofReal p) (freezingTreeLaw x n)) atTop (𝓝 0) := by
  apply (bounded_population_height_tendsto_Lp hx hM hp).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [companion_heightScale (x n) (hx n hn).1 n]
  rfl

end Freezing2
