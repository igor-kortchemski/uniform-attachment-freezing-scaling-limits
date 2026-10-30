# Whole-source omission scan, 30 October 2026

Source: [attachement-uniforme-2-final.tex](../attachement-uniforme-2-final.tex),
1,921 lines, SHA-256
`23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf` (recomputed
for this scan; it matches the inventory and the report). Compared against
[the source inventory](source-inventory.md),
[FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md) (status authority) and
[coverage-gaps.md](coverage-gaps.md) (classification of residual items).

This scan was read-only. No Lean or Lake command was run, and no other file was
edited. It was carried out by an agent and is not a human review. It repeats the
whole-scope omission scan required by `lean-statement-audit` and by report item 8
(report L646). Line numbers prefixed "L" refer to the TeX source unless another
file is named.

## 1. Summary

**Reading.** The source was read in order from L1 to L1921. This covers the
abstract (L216–L219), the Introduction (L241–L301), Sections 2–5 (L305–L1834),
both remarks (`rem:timechange`, L1299–L1303; the remark at L1829–L1834), the
Definition (L1272–L1274), Appendix A (L1845–L1888) and Appendix B
(L1890–L1916). The source has no `\footnote`; the `\thanks` entries
(L192–L206) are affiliations only. Two passages are inactive: the commented-out
proof at L1048–L1050 and the struck-out expression at L1531. The environment
census matches the inventory: 7 theorems, 10 lemmas, 5 propositions and
1 corollary, plus 2 remarks and 1 definition. There is no `open` or `conjecture`
environment.

**Coverage.** Every named environment and every labelled display has a covering
inventory row. So does every proof step on which a stated result depends. The
scan found **6 claims that no row covers** and **2 claims that lie inside a row's
line range but are missing from its description** (§2). None of them is a
theorem or lemma, and no main-result proof depends on any of them:

- four are heuristic, motivational or bibliographic (#1, #3, #4, #5);
- one is a specialization that can be derived from proved results (#2);
- one is a location of the known S14/S17 excursion mismatch that the inventory
  does not list (#6).

Repetitions in the abstract (L217–L218) and the Introduction (L271–L273, L282,
the last sentence of L292, L382) map to M02, M03, M04b–c, M06, U24 and U43,
following the inventory's convention.

**Line ranges.** All M, N, U, S and O ranges and labels match the text. One
E-row reference is off by one line (E02; see §3.1). Description gaps are listed
in §3.

**Row status.** The report is the status authority and coverage-gaps gives the
classification of residual items. All 116 inventory rows were reconciled.

- *Proved:*
  - main results M01, M02, M03, M04a, M04b, M04c (unpointed form) and M06
    (with the authorized zero diagonal);
  - numbered results N01–N17. These are qualified forms: N04 for distinct
    vertices, N11 under the S09 interpretation, N12a in corrected tracked-chain
    form, N12b in an equivalent form, N13 with repaired constants and N14 for
    positive blocks. N15 and N17 use different routes.
- *Unproved:* M05.
- *Unnumbered claims, proved or covered:* U03, U05, U07, U09–U19, U20 (new
  formulation), U21, U22, U23 (in law), U25, U26, U30, U31, U33, U35–U39, U41,
  U49 and U50–U52. U12–U13, U19, U26, U37, U39 and U50–U52 use routes that differ
  from the paper's proofs.
- *Partly open:*
  - U01: the second clause (E02);
  - U02, U06, U08: the unnamed prose subclaims (§3.5);
  - U04a: the dimension bounds;
  - U04b: the long dendron;
  - U24: the Aldous time change;
  - U27: the finite decoding;
  - U28: the source route is bypassed;
  - U29: the normalization corollary is not exported;
  - U32: the intermediate displays are bypassed;
  - U34: the count that includes unborn vertices;
  - U40: the root-degree-one clause.
- *Not covered:* U42, U43 and U46–U48. For U44 and U45 the literal claims are
  refuted in Lean.
- *External dependencies:*
  - covered: E01, E03, E06, E09, E10;
  - partly covered: E04, E05;
  - not covered: E02, E07, E08;
  - background: E11.
- S01–S19 are source issues with recorded dispositions. O01–O02 are open
  questions, not targets.

**Declaration spot-check.** The report, coverage-gaps and the inventory contain
280 distinct backticked identifier-like tokens. Of these, 214 resolve to
declarations in `Freezing2/` outside comments. Dotted names were also checked
against their enclosing namespace.

The remaining 66 tokens are not missing project declarations:

- bibliography keys and source labels;
- Mathlib names, confirmed in the pinned `.lake/packages/mathlib`. Examples are
  `ghDist_le_of_approx_subsets`, `tendsto_Lp_finite_of_tendstoInMeasure`,
  `uniformOfFinset`, `Measure.support`, `dimH`, `DyckWord`, `catalan` and
  `IsBrownianReal`;
- module names, whose files exist;
- a structure field, `frozenAt`;
- a suffix fragment, `_of_real`, standing for
  `not_uniform_smallValue_bound_of_real`, which is present;
- companion names, confirmed in `../freezing1/Freezing1/MainGeometricLimit.lean`
  at L70 and L88.

Every headline theorem cited for a proved M or N row was found in the file that
the report links for it. Every link to a Lean file in the report resolves.

All 283 modules are in the transitive import closure of `Freezing2.lean`.
Of these, 261 are imported directly. The other 22 are imported only
transitively: 21 `Companion` modules and `Probability/ReverseHeightIncrements`.
A text search found no `sorry`, `admit` or `axiom` declaration outside comments.
This text search is not an axiom audit.

**No row that the report claims as proved lacks its declaration.**

**Conclusion.** The scan supports no claim of whole-paper completion. M05, U04a,
U42–U48 and the partly open items listed above remain open. §3 lists document
inconsistencies to resolve before any coverage claim.

## 2. Omitted or uncovered claims

Items 1–6 have no covering row. Items 7–8 lie inside a row's line range but are
absent from its description.

| # | Source location | Claim | Current coverage | Suggested row or classification |
| --- | --- | --- | --- | --- |
| 1 | L281 (also L246) | In the infection tree of a stochastic SIR dynamics, $S_n$ is the number of infected vertices at time $n$. L246, citing BBKK23+, says that infection tracing of an SIR epidemic "falls within this framework". | None at L281. L246 lies inside U01's range (245–259), but U01's description omits it. | Add it to U01 as a companion-paper modelling claim, classification (d), background from BBKK23+. It carries no Lean obligation unless modelling claims are in scope. |
| 2 | L292, L570 | Algorithm 2 "extends" or "generalizes" the DR76 connection between random recursive trees and Kingman's coalescent, in the union-find setting. The mathematical content: with all signs $+1$, Algorithm 2 is the Kingman-coalescent construction of the uniform recursive tree. | None. | Add a new U-row or extend U01. The claim can be derived from the proved N01 (`forward_reverse_same_law`) and the first clause of U01 (`treeLaw_allPlus_eq_urtLaw`), but no theorem states it. Otherwise classify it as (d), literature background. |
| 3 | L294 | The scaling-limit results "only rely on" the reverse construction and its consequences (companion Theorem 8 and the lemmas at L622–L649) together with companion Theorem 3 (3). | None. Taken literally the claim is incomplete: `cor:CRT` (L1744) and L259 also use "[BBKK23+, Theorem 2]" (E02). | Record a new S-row stating that the dependency statement is incomplete, cross-referenced to E01–E03 and E02. No Lean obligation. |
| 4 | L312 | Heuristic: $\mathbf{1}_{\{x_i=1\}}/S_i$ "represents the probability that at step $i$ the degree of a given active vertex changes". In Algorithm 1 (L472–L475) the vertex is chosen uniformly among the $S_{i-1}$ active vertices of $\mathcal{T}_{i-1}$, so the forward probability is $\mathbf{1}_{\{x_i=1\}}/S_{i-1}$. The quantity $\mathbf{1}_{\{x_i=1\}}/S_i$ is the reverse height-increment probability of N02 (L626). | None. The source hedges with "essentially". | Classify as a heuristic mapped to N02, with no obligation. Optionally add the $S_{i-1}$ remark to MANUSCRIPT_RECOMMENDATIONS.md. |
| 5 | L1512 | Heuristic for `tightness time estimate`: each window of length $n/\sqrt k$ contains about $\sqrt k$ sampled vertices, and "the probability that $\sqrt k$ vertices do not coalesce with a given vertex during $n/\sqrt k$ time steps is strictly positive". The argument needs this non-coalescence probability to be bounded away from $1$, as N14 (L1568) and the bound $3/4$ at L1677 show. As written, the wording appears inverted. | None. N13 ends at L1510 and U31 starts at L1517. | Classify as a heuristic mapped to N14 and U37, with no obligation. Record the wording in MANUSCRIPT_RECOMMENDATIONS.md. |
| 6 | L282, L284 | The hypotheses "include" the case where $(S_k(\mathbf{x}^n))_{0\le k\le 2n+1}$ is a simple-random-walk excursion of length $2n+1$, with $\alpha=1/2$ and $f$ a normalized Brownian excursion. With the paper's indexing $\mathcal{T}_n=\mathcal{T}_n(\mathbf{x}^n)$ (L309), the horizon $n$ covers only the first half of the excursion. Heuristically, by the scaling in `eq:limexc` (L1748), the reciprocal-profile limit would then be $\sqrt2\,e(t/2)$ in law rather than $e$. The full-horizon reading at L1742 runs into the strict-survival problem S14 instead. | Implicitly a repetition of U43 and M05. However, L282–L284 is not among the listed locations of S14 (L1742, L1759–L1770) or S17 (L1764–L1776, L1808–L1813). | Add L282–L284 to the locations of S14 and S17 and map them to U43. No new obligation beyond M05. |
| 7 | L254 | "Our results can then be applied in the context of a random sequence": the quenched results transfer to annealed ones. | Inside U01's range but absent from its description. Only M05 exercises it substantively, through the mixture identity (L393–L397) and the random array (L1742). | Note it under M05. Two measurability facts are needed: the quenched law must be measurable in the random sequence, and so must $f\mapsto$ `criticalTreeLaw (1/f)`. No separate row is needed. |
| 8 | L1786 | The local-limit proof of `eq:borne` "gives a slightly better upper bound" than CMY00 Lemma 3.6. | Inside U44's range but absent from its description. The point is moot, because the uniform bound is refuted (S16). | Add a note to U44, or classify the claim as superseded by S16. |

## 3. Inconsistencies

1. **E02 and U01: line reference and companion attribution.**
   - E02 (inventory L161) cites source line 258, which is blank. The citation
     "[BBKK23+, Theorem 2]" is at L259 (and again at L1744).
   - The inventory's E02 and U01 rows (L99) describe companion Theorem 2 as the
     uniform-plane-tree law. Coverage-gaps E02 (L51) states instead that
     companion Theorem 2 is `thm:BGW` and that the uniform-plane-tree statement is
     the companion's Examples paragraph.
   - This was confirmed in `../freezing1/attachement-uniforme-1-final.tex`. All
     theorem-like environments share one counter (L63–L76). The second numbered
     environment is `thm:BGW` (L277–L280, the geometric Bienaymé theorem). The
     uniform-plane-tree statement is in the Examples paragraph (L271–L274).
     `thm:samelaw` is the eighth environment (L661), which matches the source's
     "Theorem 8".
   - The source's citations at L259 and L1744 are therefore misattributed with
     respect to the local companion version. The published numbering was not
     checked.
   - This finding appears neither in the inventory's S-list nor in
     MANUSCRIPT_RECOMMENDATIONS.md.

2. **The report header overstates U32 and U40.** The header (report L13) lists
   "U31–U32 … U36–U41" among the proved unnumbered claims, but the rows are
   narrower:
   - U32 (report L97) states that `16/01/11h` (L1539), `eq:delta` (L1542–L1549)
     and the uniform-integrability argument are bypassed and not certified. Only
     `eq:GH` and the transfer are proved.
   - U40 (report L94) states that the source's "root degree one" (L1723) is not
     claimed.

   M04c is likewise proved only in unpointed form (report L38). The header
   should qualify U32 and U40, as it already qualifies U20 and U23.

3. **The list of remaining obligations is incomplete.** The report's closing
   list (report L602–L646) begins "The remaining source obligations are", but it
   omits items that the report's own rows record as uncertified or unexported:
   - U28's source route: `eq:cv locale bis`, Fatou with mass conservation, and
     Scheffé (L1390–L1458; row L87);
   - U29's corollary that the densities sum to one (L1419; row L103);
   - U32's intermediate displays (row L97);
   - U24's claim that "$g_{0,k}$ determines the law" (L1302; row L89, "not
     stated separately");
   - the unnamed "other prose subclaims" of U02, U06 and U08 (row L74) and of
     U03 (row L78);
   - U27's "full local genealogy density" (row L104);
   - U20's unexported array with no GHP limit (row L82);
   - the $L^p$ form at L1046 (§3.6).

   Under the inventory's rule (inventory L92–L94), a different proof of a later
   theorem does not discharge these items. The report should either list them
   or state explicitly that the alternative routes close the bypassed
   intermediate claims.

4. **E11 has two classifications.** Report L118–L121 lists E11 among the items
   "still open in whole or in part". Coverage-gaps L60 classifies E11 as (d),
   "None needed", and report item 3 (L626–L629) calls the comparisons external.
   One classification should be chosen.

5. **U02, U06 and U08 have no declarations and unnamed residual subclaims.**
   Report row L74 cites no declaration and does not name its "other prose
   subclaims". Coverage-gaps does not cover these rows.
   - `treeLaw_counts` (`Freezing2/Companion/ForwardLaw.lean` L127) gives an
     active count of $S_n$ and a vertex count of (number of up-steps) $+1$ for
     $n\le\tau$. This covers U02 and the vertex count in U06 (L478).
   - A name search found no declaration for two claims: U06's monotonicity and
     stationarity clause (L480: the sequence of trees is non-decreasing, and it
     becomes stationary if and only if $\tau<\infty$, first at time $\tau$), and
     the claim that "the law depends only on the first $n$ signs".

   The documents leave the status of these clauses undetermined.

6. **U20's description omits the $L^p$ mode.** The U20 row (inventory L119)
   says "height asymptotics". The text at L1046 asserts that
   $\mathrm{Height}(\mathcal{T}_n)/h_n^+\to1$ in $L^p$ for every $p\ge1$. The
   report's row (L82) and coverage-gaps E01 (L50) state that the formal route
   uses convergence in probability instead. The literal $L^p$ claim for bounded
   populations is not exported, although the vendored
   `Freezing1.maximum_height_tendsto_Lp` would apply. This is minor. Either
   record the mode in U20 or mark the $L^p$ form as bypassed.

7. **README.md is out of date relative to the report.**
   - Its bold headline (README L5) names only the height, subcritical and
     supercritical theorems as proved.
   - L8 says that development is paused.
   - L84–L86 describe the 2,159-declaration, 246-module run as the latest
     checkpoint.

   The report records M03, M04 and N01–N17 as proved, and its latest all-source
   check covers 3,524 declarations in 283 modules (report L356–L362).
   publication-readiness.md (L25) agrees with the report.

8. **The inventory now records status in addition to the report.** The
   inventory header (L6, L19–L24, L239) presents it as an initial inventory
   dated 29 October that certifies nothing. Yet rows S09, S15, S16, S18 and S19
   (L193–L203) carry dispositions dated 30 October that cite Lean declarations.
   No status conflict was found, but status is now recorded in two places.

9. **E05's line list is incomplete.** E05 (inventory L163) names Fatou's lemma,
   the convergence-together argument and uniqueness. Its line list omits their
   uses at L1419, L1816–L1820 and L1915.

10. **The inventory's environment count omits the Definition.** Inventory L10
    counts the named result environments and "the two remarks" but not the
    Definition at L1272–L1274 (admissibility). U24's range and description cover
    it, so no obligation is missing.

11. **Minor source slips that no S-row records.** None affects coverage.
    - L587: the caption chooses the pair "in $\mathcal{F}^5_3$"; it should be
      $\mathcal{F}^5_4$.
    - L614: "$b_n(v)=n$" should be $b_n(u)$.
    - L707 defines $h_n(a,b)$ only for $a\ge1$, but L880 and L898 use
      $a=c_n(u,v)$, which can be $0$. This is harmless because $S_0=1$.
    - L1432 writes $\mathfrak{F}_{r,k}$ where $\mathfrak{F}^+_{r,k}$ is meant.
    - L1566: "$v_1\neq\ldots\neq v_K$" is read as pairwise distinctness (in the
      inventory's and the report's N14 rows), but the reading is not recorded.
    - L1583 and L1594 write $\{v_0,\ldots,v_k\}$ for $\{v_0,\ldots,v_K\}$. S11
      records only the index slip at L1584.
    - L1623: "$1\le j\le n$" should be $1\le j\le k$.
    - L1681 conditions on the tree of $\mathcal{F}^n_{i\delta_{k,n}}$, whereas
      $A_i$ (L1675) and the bound at L1683 use
      $\mathcal{F}^n_{(i-1)\delta_{k,n}}$.
    - L1698: "full support to the leaves" should read "full measure". The
      theorem statement at L377 is correct.
