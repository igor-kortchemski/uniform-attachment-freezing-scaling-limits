# Manuscript recommendations

Source: [attachement-uniforme-2-final.tex](attachement-uniforme-2-final.tex),
unchanged SHA-256
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
The complete location-by-location review is the S01–S23 table in the
[source inventory](docs/source-inventory.md#source-issues-requiring-explicit-treatment).
These issues also affect coverage in [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md).
No manuscript edits have been made.

## Corrections with direct evidence

1. **Supercritical theorem, lines 406–414 and 1105–1109.** The matrix includes
   its diagonal, where distances are zero. The printed sum of two branch lengths
   is positive on non-root diagonal entries. The user approved zero diagonal,
   retaining the off-diagonal formula. Also use $U_1,\ldots,U_k$, not
   $U_1,\ldots,U_n$. [Obstructions.lean](Freezing2/Audit/Obstructions.lean)
   proves the general distributional obstruction and elementary corrected geometry.
2. **Coalescence law, lines 645–649.** Require distinct vertices. With a single
   attachment, self-coalescence occurs at birth time 1, whereas the displayed
   mass at time 0 would equal 1. The numerical/diagonal obstruction is formalized,
   and the corrected law for distinct vertices is proved
   (`sourceCoalescenceTime_probability`, report row N04).
3. **Auxiliary “distance”, lines 879–880.** The inclusive formula has
   $D^n(u,u)=1/S^n_{b_n(u)}>0$. Call it a surrogate, or alter and recheck the
   definition. Any comparison with the birth/coalescence metric must retain
   endpoint errors. The positive self-entry is formally proved.
4. **Interval pairing, line 808.** With a single upward step and $a=b=1$, its
   two sides are $1/2$ and 0. The starting height must be the pre-step height.
   [WeightedWalk.lean](Freezing2/Discrete/WeightedWalk.lean) gives a verified
   endpoint-potential replacement, specialized in
   [Estimates.lean](Freezing2/Discrete/Estimates.lean). This preserves the needed
   finite bound but does not establish the asymptotic lemma.
5. **CRT local formula, `eq:probalocale`, lines 1787–1791.** The factor
   $\frac{k-1}{i}P(S_i=k)$ counts paths that stay strictly above their starting
   level 1 rather than above 0, so the display forces $P(S^{2n+1}_i=1)=0$. For
   $n=1,i=2,k=1$ the left side is 1 and the right side is 0. This is
   machine-checked in
   [ExcursionCounterexamples.lean](Freezing2/Audit/ExcursionCounterexamples.lean)
   (`not_kempermanDisplay`, restricted to $n\ge1$, $k\ge1$). Replace the factor by
   $P(S_i=k)-P(S_i=k+2)=\frac{2k}{i+1}P(S_{i+1}=k+1)$ and restrict to
   $1\le i\le2n$, $k\ge1$ (the printed range includes $i=2n+1$, where $2n-i+1=0$).
   The corrected formula was checked by enumeration for $n\le6$, not in Lean.
   The subsequent bound $Ck^2/i^{3/2}$ is unaffected.
6. **CRT uniform estimate, `eq:borne`, lines 1781–1803.** With $C$ independent of
   $n,\delta,\varepsilon$, the bound $P(X_n(\delta)\ge\varepsilon)\le C\delta^2/\varepsilon$
   is false. For $n\ge2$ take $\delta=1/\sqrt n$ and $\varepsilon=1/(2\sqrt n)$: a
   return to 1 at time 2 has probability $(n+1)/(4n-2)>1/4$ and forces
   $X_n(\delta)\ge2\varepsilon$, while the bound is $2C/\sqrt n$. The final inequality
   on line 1801 also discards the unbounded factor $\sqrt n\sum_{i\le n}i^{-3/2}\ge\sqrt n$.
   Both are machine-checked in the same file (`not_uniform_smallValue_bound`,
   `not_bounded_sqrt_mul_sum_inv_rpow`), with the Catalan counting encoded in Lean.
   The counterexample lets $\varepsilon\to0$ with $n$, so it does not refute a
   version with $C=C(\varepsilon)$, which is all Step 2 uses. Suggested replacement:
   $P(X_n(\delta)\ge\varepsilon)\le C\delta/\varepsilon$, from
   $E[\frac1{S_i}\mathbb 1_{S_i\le\delta\sqrt n}]\le C\min(i^{-1/2},\delta^2n\,i^{-3/2})$,
   giving $E X_n(\delta)\le C\delta$ (a paper sketch, not Lean-checked). Neither
   finding refutes Corollary `cor:CRT`.

## Additional proof obligations

The inventory records the full details and distinguishes confirmed errors from
points requiring justification. In particular:

- Treat terminal extinction separately when assigning Bernoulli parameters;
  $1/S_n$ is not a parameter when $S_n=0$.
- Frozen birth times are freezing indices minus one. Treat coincident iid samples
  when invoking a distinct-vertex coalescence formula.
- Restrict the one-block tightness estimate to valid forest times, correct its
  binomial constants, and handle the shared birth time of active vertices.
- The one-block estimate is now proved for positive block indices. A root
  correspondence transports the actual uniform pair kernels and justifies
  the oldest-vertex isolation comparison. Exact step counting gives the
  stronger denominator $\delta-M_n$; treating absorption before taking
  reciprocals avoids division by zero. The printed coefficient follows once
  $M\sqrt{k}\geq12$, with one threshold depending only on $M$.
- In the proof of Proposition `tightness time estimate`, the occupancy step
  needs a longer block or different constants: the available binomial mean is
  about $1.5M\sqrt k$ for blocks of length $4\lceil Mn/\sqrt k\rceil$, not the
  $6M\sqrt k$ used with threshold $4M\sqrt k$. The formal proof uses blocks of
  length $16\lceil Mn/\sqrt k\rceil$ and Bennett's $g(1/4)$. Count fourfold
  birth collisions only among frozen vertices, since all active vertices share
  birth time $n$.
- At line 1677 the events $A_i$ need not be conditionally independent as
  stated. A conditional bound suffices: given the whole reverse history up to
  the start of an alternating block, the isolation probability is at most
  $3/4$, and the tower property iterates this. The final bound is
  $O((3/4)^{(p_k-1)/2})$, which is $o(k^{-4})$ by the choice of $p_k$.
- In Step 2 of the tightness proof, the comparison of $d^n/\sqrt n$ with a
  truncated harmonic sum plus $\Delta^n/(n\delta)$ needs the inclusive
  endpoint terms. The formal proof instead uses a uniform modulus for short
  harmonic intervals together with Proposition `height=ok`.
- Fix component ordering/conditioning conventions in the critical coalescent
  density and its discrete approximation.
  The formal construction uses increasing chronological root labels to order
  residual components. Allowing all component permutations would require a
  factor $1/(r+1)!$ in the printed density; for two unmerged particles, the
  two possible singleton-root orders already expose the mismatch. The early
  prose should also use $r+1$ residual clusters, consistently with Proposition
  `loi du coalescent généralisé` and its convention for zero merger times.
- In the discrete local-density argument, distinguish iid samples from samples
  conditioned to be frozen and distinct. For a prescribed legal vector, the
  iid mass is $N^{-k}$; the conditional mass is $1/(F)_k$, where $F$ is the
  frozen-vertex count and $(F)_k=F(F-1)\cdots(F-k+1)$. Events forcing this
  support satisfy an exact multiplicative correction $(F)_k/N^k\to1$.
  An additive vanishing collision bound alone does not justify rescaled local
  probabilities.
- For merely measurable $1/f^2$, a Skorokhod coupling of the times alone does
  not imply convergence of their profile values. Prove joint time-and-mark
  convergence first: jitter the sign index inside its mesh cell, use the
  derived bounded density relative to Lebesgue measure and local $L^1$
  convergence, then recover the exact discrete index. Any subsequent
  Skorokhod representation must include that joint pair.
- Reconcile the CRT argument's strict survival assumption, extinction horizon,
  half/full time intervals, and scaling normalization.
- Use a projection from GHP classes to GP classes; without full support it is
  not an inclusion of the underlying entire-space isometry classes.
- Qualify the Introduction's claim that recursive trees have no GHP scaling
  limits by specifying nontrivial limits and the intended normalization.
  Sufficiently strong shrinking permits a one-point limit. The corresponding
  negative assertion and bounded-population nonuniversality claim remain
  separate obligations in the inventory.
- In the proof of `thm:properties`, the second proof is headed "Proof of Theorem
  `thm:properties` (3)" although the theorem has only items (1) and (2); it
  proves item (2). The same proof calls branch points "binary" (two children);
  stating that this means degree three in the metric sense, and that "the root
  has degree 1" refers to the rooted tree, would avoid ambiguity for unrooted
  limits.

## Citations, heuristics and minor slips

These come from the [omission scan](docs/omission-scan-2026-10-30.md) of
30 October 2026. None affects the coverage of a stated result.

- **Companion numbering (S20), lines 259 and 1744.** "[BBKK23+, Theorem 2]" is
  cited for the uniform-plane-tree law. In the local companion version,
  Theorem 2 is `thm:BGW` (geometric Bienaymé tree) and the uniform-plane-tree
  statement is the Examples paragraph; "Theorem 8" (`thm:samelaw`) is correct.
  The published numbering was not checked. The dependency statement at line 294
  should also list this use of the companion.
- **Excursion indexing (S23), lines 282–284.** With $\mathcal T_n=\mathcal T_n(\mathbf x^n)$,
  an excursion of length $2n+1$ is read only up to time $n$, so the profile
  would be $\sqrt2\,e(t/2)$ rather than $e$. Index the example as in the proof
  of `cor:CRT`, or say that it is heuristic.
- **Heuristic at line 312 (S21).** In Algorithm 1 the forward probability is
  $\mathbf 1_{\{x_i=1\}}/S_{i-1}$; $\mathbf 1_{\{x_i=1\}}/S_i$ is the reverse
  increment probability of Lemma `lem:accroissementH`.
- **Heuristic at line 1512 (S22).** The non-coalescence probability should be
  "bounded away from one", not "strictly positive".
- Line 587 (caption): the pair is chosen in $\mathcal F^5_4$, not $\mathcal F^5_3$.
- Line 614: "$b_n(v)=n$" should be $b_n(u)=n$.
- Line 707: $h_n(a,b)$ is defined only for $a\ge1$, but lines 880 and 898 use
  $a=c_n(u,v)$, which can be $0$. This is harmless since $S_0=1$; define it for
  $a\ge0$.
- Line 1432: $\mathfrak F_{r,k}$ should be $\mathfrak F^+_{r,k}$.
- Line 1566: write "pairwise distinct $v_1,\ldots,v_K$" for
  "$v_1\neq\ldots\neq v_K$".
- Lines 1583 and 1594: $\{v_0,\ldots,v_k\}$ should be $\{v_0,\ldots,v_K\}$
  (compare S11, which records the index slip at line 1584).
- Line 1623: "$1\le j\le n$" should be $1\le j\le k$.
- Line 1681 conditions on the tree of $\mathcal F^n_{i\delta_{k,n}}$, whereas
  $A_i$ (line 1675) and the bound at line 1683 use
  $\mathcal F^n_{(i-1)\delta_{k,n}}$.
- Line 1698: "full support to the leaves" should read "full measure to the
  leaves", as in the statement at line 377.

These recommendations do not certify the remaining mathematical arguments.
The detailed report keeps the affected original claims and replacement-proof
obligations visible.
