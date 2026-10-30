# Source inventory and initial statement audit

Source: [attachement-uniforme-2-final.tex](../attachement-uniforme-2-final.tex),
*Uniform attachment with freezing: Scaling limits*, 1,921 source lines.
SHA-256: `23a485d5a5dfaca01a05db28377d015fb1456c194a543d0cbf56f77619ad0cbf`.
Audit date: 29 October 2026. This inventory was reconstructed independently of
Lean implementations using the local `lean-statement-audit` skill.

The active manuscript was read from its Introduction through both appendices.
A mechanical environment scan found **23 named result environments: 7 theorems,
10 lemmas, 5 propositions, and 1 corollary**, plus two remarks and one
definition (admissibility, 1272–1274, covered by U24). The remarks, the
definition and mathematical assertions outside environments are included below.
Multipart results are split
where their obligations differ. Proof steps are grouped only when they belong
to one explicitly described argument; their source ranges retain all intermediate
claims. Repetitions in the abstract and Introduction map to the corresponding
result rather than creating duplicate obligations. Mathematical claims quoted
from other work remain dependency obligations, not assumed truths.

This is an **initial source inventory**, not a certificate of complete Lean
coverage. Every row initially represents an unresolved formalization obligation.
The maintained [formalization report](../FORMALIZATION_REPORT.md) records later
Lean correspondence and proof status. `Issue Sxx` below means the literal source
or its argument needs the specified treatment; it does not erase the obligation.
No existing theorem has been certified by this document.

**Status note (30 October 2026).** Several S-rows (S09, S15, S16, S18, S19)
now record dispositions from 30 October 2026 that cite Lean declarations, and
rows U53–U58 and S20–S23 were added from the
[whole-source omission scan](omission-scan-2026-10-30.md) of that date. These
additions do not make this file a status record.
[FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md) remains the authority for
proof status, and [coverage-gaps.md](coverage-gaps.md) classifies the items that
have no report row.

## Standing meanings and scope

- `A`: a deterministic triangular array of signs, with $S^n_0=1$,
  $S^n_j=1+\sum_{i=1}^j x_i^n$, and $\tau(x^n)>n$ for every positive $n$.
  Thus $S^n_j>0$ for $0\leq j\leq n$. At a finite horizon of a single path,
  statements allowing $n=\tau$ must treat the zero terminal population separately.
- `L1(alpha)`: $0<\alpha<1$; $f$ measurable; reciprocal profile integrable on
  $[0,1]$; $n^\alpha/S^n_{\lfloor nt\rfloor}\to1/f(t)$ in $L^1([0,1])$.
- `L2(alpha)`: $1/f^2$ locally integrable on $(0,1)$ and, for every
  $0<a<b<1$, the integrals of $(n^\alpha/S^n_{\lfloor nt\rfloor})^2$ over
  $[a,b]$ converge to those of $1/f^2$. This is the manuscript's moment condition,
  not an assumed pointwise convergence or assumed uniform rate.
- `C`: `A`, `L1(1/2)`, `L2(1/2)`, and one deterministic constant $M$ with
  $\max_{j\leq n}S^n_j\leq M\sqrt n$ eventually. Extending an eventual bound
  to every positive $n$ is a separate elementary finite-prefix step.
- The random finite tree carries its uniform vertex probability measure in
  measured convergence statements. Scaling multiplies distances, not measures.
  Random sampled vertices are conditionally independent given the tree.
- $f$ may vanish at endpoints, as in the Brownian-excursion application. A Lean
  total inverse must not silently make a positive-measure zero set admissible.
  The intended positive finite reciprocal almost everywhere, endpoint conventions,
  and the equivalence of representations require explicit treatment.
- A main result's dependence on a companion-paper theorem is an obligation to
  prove or import an already verified theorem with matching hypotheses. The
  independent project `../freezing1` is not an axiom source.

## Main results and named environments

The source labels, rather than typeset theorem numbers, are stable identifiers.
Source locations refer to the unmodified TeX above.

| ID | Environment, source lines, label | Exact mathematical obligation and principal dependencies |
| --- | --- | --- |
| M01 | Theorem 330–337, `thm:heightalpha` | Under `A`, `L1(alpha)`, `L2(alpha)`, for every real $p\geq1$, height divided by $n^{1-\alpha}$ converges in $L^p$ to $\int_0^1(2f)^{-1}$. Depends on N06(iii), the companion paper's Theorem 3(3), and its hypotheses. Proof is only the explanation at 338. |
| M02 | Theorem 345–352, `thm:sous-critique` | For $0<\alpha<1/2$, under `A`, `L1(alpha)`, `L2(alpha)`, the scaled measured tree converges in distribution in GHP to $[0,H(1)]$, with $H(t)=\int_0^t(2f)^{-1}$ and measure $H_{\ast}\mathrm{Leb}$. Depends on N06, N07, N08, N15, N16, and U17–U19. |
| M03 | Theorem 360–365, `thm:critique` | Under `C`, $n^{-1/2}T_n$ converges in distribution in GHP to a random compact measured real tree $T(f)$. The limit must be constructed and shown independent of the approximating array. Depends on N11–N14, N17, U25, U30–U37, and real-tree closure U26. |
| M04a | Theorem 373–380, `thm:properties` (1) | The mass measure of $T(f)$ has full support and assigns mass one to its leaves, almost surely. Depends on M03/N17, U25, U38; full support on the whole tree and full measure of the leaf set are distinct claims. |
| M04b | Same, (2), first assertion | Almost surely $T(f)$ is binary iff $\int_0^{1/2}f^{-2}=\infty$. Depends on U39–U41; rooted branching versus unrooted degree needs a fixed convention. |
| M04c | Same, (2), second assertion | In the finite-integral case the root has infinite degree and every other branchpoint is binary, almost surely. Same dependencies; see S13. |
| M05 | Corollary 389–392, `cor:CRT` | The annealed law of $T(e)$ for normalized Brownian excursion $e$ equals the Brownian CRT law. Includes measurable dependence of the law on $f$ and the mixture identity at 393–397. Depends on M03, U42–U47, the companion's uniform-plane-tree statement (cited as "Theorem 2"; E02, S20), and CRT normalization. See S14–S17. |
| M06 | Theorem 406–414, `thm:sur-critique` | For $1/2<\alpha<1$, under `A`, `L1(alpha)`, `L2(alpha)`, for every fixed $k\geq2$, the rooted sampled distance matrix divided by $n^{1-\alpha}$ converges in distribution to the star matrix: entry $H(U_i)+H(U_j)$ when $i\ne j$, and zero when $i=j$, with $U_0=0$ and $U_1,\ldots,U_k$ independent uniform. **User-approved correction:** zero diagonal; the original all-pairs formula is false (S01). Depends on N06, N07, N10 and U21. |
| N01 | Theorem 595–598, `thm:samelaw` | For a sign path and $0\leq n\leq\tau$, Algorithm 1 tree and Algorithm 2 tree with active labels collapsed to $a$ have equal distributions as rooted edge/vertex-labelled trees. Companion Theorem 8; construction/well-definedness U05–U08. |
| N02 | Lemma 622–628, `lem:accroissementH` | For $1\leq n\leq\tau$, fixed labelled vertex $v$, and $1\leq i\leq b_n(v)$, the conditional probability of a height increment given the entire exposed reverse forest history is $S_i^{-1}\mathbf1_{x_i=1}$. Companion §2.3; conditional-law kernel must genuinely describe Algorithm 2. |
| N03 | Lemma 637–643, `lem:bunif` | For $1\leq n\leq\tau$, uniform vertex $V$, every $1\leq m\leq n$, $P(b_n(V)<m)=(m+1-S_m)/(n+1+S_n)$. Depends on exact frozen-label counts and total vertex count U06/U08. |
| N04 | Lemma 645–649, `loi du temps de coalescence` | Pairwise coalescence mass equals the displayed hazard times survival product, for $0\leq c<b_n(u)\wedge b_n(v)$ and $x_{c+1}=1$. **Literal source omits $u\ne v$ and is false** (S02); retain original and corrected obligations separately. Companion §2.3. |
| N05 | Proposition 679–684, `prop:bennett` | Independent Bernoulli variables with parameters in $[0,1]$, positive total mean $m$: both strict upper and lower deviations of size every $t>0$ are bounded by $\exp(-m g(t/m))$, $g(u)=(1+u)\log(1+u)-u$. Includes the lower-tail case $t\geq m$. |
| N06(i) | Lemma 718–752, `lem:hnalpha`, lines 722, 757–766 | Under `A`, `L1(alpha)`, `L2(alpha)`, for every fixed $a\in(0,1]$, $S^n_{\lfloor na\rfloor}=o(n)$. Proof's interval choice needs repair S05. |
| N06(ii) | Same, 723–730, 768–773 | Both finite measures $(2/n)\sum_{i\leq n}\mathbf1_{x_i=\pm1}\delta_{i/n}$ converge weakly to Lebesgue measure on $[0,1]$. Depends on N06(i), exact signed-step counts, and Portmanteau. |
| N06(iii) | Same, 731–734, 775–804 | $2n^{\alpha-1}h_n^+\sim n^{\alpha-1}h_n\sim\int_0^1f^{-1}$. Requires positive limit and asymptotic-equivalence meaning, not just equality of arbitrary limits. Depends on U12–U13. |
| N06(iv) | Same, 735–738, 806–826 | $n^{\alpha-1}\max_{1\leq a\leq b\leq n}|h_n^+(a,b)-h_n(a,b)/2|\to0$, with one error uniform over both endpoints. Depends on U14; printed pairing identity is false (S06). |
| N06(v) | Same, 739–750, 828–874 | For every interior cutoff, the maximum over integer $\varepsilon n\leq a\leq b\leq(1-\varepsilon)n$ of the difference between $(1/n)\sum_{i=a}^bn^{2\alpha}\mathbf1_{x_i=1}/(S_i(S_i-1))$ and $\int_{a/n}^{b/n}(2f^2)^{-1}$ tends to zero. Handle empty ranges when $\varepsilon\geq1/2$ without changing substantive content. Depends on U15 and `L2`. |
| N07 | Proposition 882–888, `height=ok` | Under `A`, `L1(alpha)`, `L2(alpha)`, every $\varepsilon>0$, probability of $\max_{u,v}|d^n(u,v)-D^n(u,v)|>\varepsilon n^{1-\alpha}$ tends to zero. $D^n$ is the inclusive-sum surrogate defined at 880; not itself a metric (S03). Depends on N02, N05, N06(iii–iv), U16. |
| N08 | Lemma 933–938, `lemme ça coalesce vite` | Under subcritical hypotheses, $n^{-1}\max_{u,v}(b_n(u)\wedge b_n(v)-c_n(u,v))\to0$ in probability. The repeated declaration of $\alpha$ at 934 is a typo; use $0<\alpha<1/2$. Depends on N04, N06(v), uniform interval lower bounds U17. |
| N09 | Theorem 1036–1043, `thm:alpha0` | Uniformly bounded positive active population, one constant $M$ valid for all $n,k\leq n$: $(h_n^+)^{-1}T_n\to[0,1]$ in probability in GH. No universal limiting measure is claimed. Depends on companion Theorem 3(3), N04, U20. |
| N10 | Lemma 1076–1082, `lemme ça coalesce en zéro` | Under supercritical hypotheses, for two independent uniform vertices, $c_n(V_1,V_2)/n\to0$ in probability. Coincident samples must be treated, not discarded in an exact inequality (S07). Depends on N03, corrected N04, N06(i,v). |
| N11 | Proposition 1279–1290, `loi du coalescent généralisé` | For every $k>r\geq0$, each admissible forest and distinct ordered positive coalescence times, joint forest/birth/coalescence law has density $g_{r,k}$ of 1282 against product Lebesgue measure, with $C_1=\cdots=C_r=0$. Includes mass on every possible number of components. Depends on continuous hazard construction U23, Aldous density, planar-order factors. Root ordering ambiguity S09. |
| N12a | Lemma 1318–1336, `eq:cv locale` | In critical scaling, for every $k>r\geq0$ and fixed forest, the displayed conditional discrete probabilities, multiplied by $(n/2)^{2k-1-r}$, converge in the ordered limits $n\to\infty$, then $\varepsilon\downarrow0$, to $g_{r,k}$ evaluated at independent uniform times. Depends on N06, N11, U27–U29. Conditioning-index and sampling issues S10. |
| N12b | Same, `cv coalescent`, 1331–1335 | Joint convergence of all scaled sampled birth times and pairwise coalescence times to the continuous coalescent. Requires diagonal convention $C_{i,i}=B_i$ and treatment of repeated finite samples. Depends on N12a and U28–U29. |
| N13 | Proposition 1506–1510, `tightness time estimate` | Under `C`, for every sufficiently large $k,n$ with $k\leq n^{1/3}$, $P(\Delta^n(V,\{V_1,\ldots,V_k\})>n\log^2k/\sqrt k)\leq k^{-4}$. The thresholds may depend on the fixed array/bound $M$, not on vertices or $k,n$ individually. Depends on N14, U33–U37; proof constants need repair S12. |
| N14 | Lemma 1565–1570, `OneStepTightness` | Uniformly for sufficiently large $k,n$ with $k\leq n^{1/3}$, admissible block index $i$, vertex $v_0$ born after $(i+1)\delta$, and pairwise distinct $v_1,\ldots,v_K$ born in $(i\delta,(i+1)\delta]$, noncollision by $(i-1)\delta$ has probability at most $3M\sqrt k/(4K)$. $\delta=4\lceil Mn/\sqrt k\rceil$, $K\geq1$. **Source permits $i=0$, an undefined negative time** (S11). Depends on U34–U35. |
| N15 | Lemma 1863–1864, `equivGP` | For deterministic GP classes of Polish measured spaces, GP convergence iff convergence in distribution of infinite iid sampled distance matrices. Cited dependency `Loh13`; random-space extension used later must be justified. |
| N16 | Lemma 1885–1886, `GP+GH=GHP` | For GHP-measurable random compact measured spaces with almost surely full-support candidate limit, weak GP convergence to that limit and weak GH convergence of projections imply weak GHP convergence. Cited `Bla21`, Lemma 4. |
| N17 | Proposition 1896–1899, `C.1` | Weak convergence of infinite sampled distance matrices plus the exact leaf-tightness iterated-limit criterion implies weak GHP convergence to a random compact measured space, whose sample matrix has the prescribed law and whose measure almost surely has full support. Depends on N15, N16, U50–U52, and ADH compactness/tightness. |

## Substantive claims outside the named statements

These obligations include intermediate steps of the paper's proof strategy.
Checking a later theorem by a different argument does not automatically check
these arguments. “Definition” below includes the existence/well-definedness and
characterization needed to justify using that construction.

| ID | Source lines / labels | Obligation and dependencies |
| --- | --- | --- |
| U01 | 245–259, 295 | The model specializes to recursive trees for all $+1$ signs; an iid symmetric sign path yields the specified uniform-plane-tree law (with correct stopping/size conditioning). Companion "Theorem 2" as cited at 259; in the local companion this statement is the Examples paragraph, not Theorem 2 (S20). Introduction's $\alpha=1$ logarithmic-distance/bush description and universal height bounds are companion-paper dependencies. The SIR infection-tracing remark at 246 is U53. The sentence at 254 ("Our results can then be applied in the context of a random sequence") asserts that the quenched results transfer to annealed ones. Only M05 exercises it substantively (mixture identity 393–397, random array 1742), where it needs the quenched law to be measurable in the random sequence and $f\mapsto$ `criticalTreeLaw (1/f)` to be measurable; no separate row. |
| U02 | 263–266, `eq:defintro` | Until extinction, $S_n$ equals the active vertex count; extinction is first zero and the process thereafter stops. The unrestricted sentence “$S_n$ represents the number” needs the stopped-time restriction. |
| U03 | 319–325 | Under `L1`, `L2` is equivalent to local $L^1$ convergence of squared reciprocal profiles; for $\alpha\geq1/2$ it implies local minimum population divergence. Scheffé/uniform integrability and skip-free path estimates; N06(v)/U15. |
| U04a | 367, 385 | Critical finite-dimensional convergence does not need the $O(\sqrt n)$ maximum assumption; almost surely each Minkowski, packing, and Hausdorff dimension of $T(f)$ is at least 2. The dimension claim has no supplied proof and remains a separate substantial obligation. |
| U04b | 280, 382, 415 | The Introduction asserts that recursive trees without freezing have no GHP scaling limits; the intended normalization and exclusion of trivial collapsed limits must be specified (S19). Comparative claims for stable, nongeneric Bienaymé, Cauchy-Bienaymé and superexponential simply generated trees; supercritical failure of GHP tightness via covering numbers; convergence to the specified long dendron in the cited alternative topology. External sources LGLJ98/DLG02, JS11/Jan12/Kor15, KR19, JJS11, ET21/Jan21. The covering-number claim needs “sufficiently small radius”, not every positive radius (S08). |
| U05 | 464–477, Algorithm 1 | Construct the random rooted double-labelled tree recursively, with uniform active-vertex choice at each step; verify the probability kernel, finite carrier, tree invariant, root and labels. Conditional choices, not independent vertices on a fixed carrier. |
| U06 | 478–480 | Exact vertex count $N_n=(S_n+n+1)/2$ for $n\leq\tau$; law depends only on the first $n$ signs; trees increase; eventual stationarity iff finite extinction, with first extinct/stationary state at $\tau$. |
| U07 | 574–582, Algorithm 2 | Reverse forest construction is well-defined, has $S_i$ components at time $i$, has a legal ordered distinct pair at every attachment step, and ends with one rooted tree. Prove relabelling characterization used by N01. |
| U08 | 607–618 | Deterministic disjoint active/frozen label carrier; exact cardinalities; $b_n(a_j)=n$, $b_n(i)=i-1$ for frozen $i$; coalescence maximum exists, is at most both birth times, has the diagonal value $c_n(u,u)=b_n(u)$, and is determined by nested forest membership. |
| U09 | 630–633, `eq:H0`; 901–903 | Fixed-vertex height, and each partial height, has the law of the corresponding sum of independent Bernoulli variables. Conditional increment formula N02 must imply independence for that vertex. Terminal $S_n=0$ must not be used as a Bernoulli parameter (S04). |
| U10 | 655–656 | N01 implies equality in law of underlying graph/metric/measure structures, so all main results transfer from the reverse tree to the forward tree. |
| U11 | 758–773, `eq:pn` | Skip-free/Lipschitz path estimates, exact counts of positive and negative steps on any integer interval, and their macroscopic interval asymptotics. Includes endpoints $a=0$ and rounding errors. |
| U12 | 775–797 | Reciprocal sum equals positive plus negative contributions; exact global pairing identity $h_n^+=\sum_{x_i=-1}(S_i+1)^{-1}+\sum_{s=2}^{S_n}s^{-1}$; expansion into reciprocal correction and logarithmic remainder; uniform bound $S_n\leq n+1$. |
| U13 | 798–804, `eq:lemme hnalpha convergence somme vers 0` | $n^{\alpha-1}\sum_{i\leq n}[S_i(S_i+1)]^{-1}\to0$ using uniform integrability plus convergence in probability. Verify the sum/integral endpoint shift. |
| U14 | 806–826 | Interval pairing, logarithmic boundary bound, and uniform reciprocal-half-sum error. Printed exact identity is false (S06); retain corrected proof route distinctly. |
| U15 | 828–874, `eq:lemme h point cinq1`, `eq:cvminSinfini`, `eq:lemme h point cinq2` | Uniform interior pairing for $1/[S(S-1)]$; $1/\min S=o(n^{1-2\alpha})$ via a shrinking-interval integral; replacement of $S-1$ by $S+1$ on positive steps; local integral approximation uniformly over endpoints. Quantifier order of every error is uniform in $a,b$. |
| U16 | 879–916, `4/9/10h`, `4/9/14h` | Surrogate $D^n$ characterization; common-ancestor height identity; maximum error bound; $x\mapsto xg(t/x)$ decreasing for each $t>0$; union bound over vertices/times; exponential decay dominates $n^2$; inclusive/exclusive endpoints contribute negligible scaled error. See S03. |
| U17 | 939–950 | Uniform coalescence-survival product estimate over all vertex pairs and intervals, conversion to exponential, and positive lower bound for integrals over fixed-width subintervals. N06(v) is only interior: boundary intervals need explicit reduction. |
| U18 | 954–973, `eq thm sous-critique` | Joint sampled birth-time convergence to independent uniforms; frozen samples occur with probability tending to one; signed reciprocal-sum decomposition; coalescence-near-minimum yields limiting segment distance matrices. Frozen birth times are freezing indices minus one (S07). |
| U19 | 974–1031, `cv distorsion`, three distortion labels | The displayed relation is a correspondence onto both spaces; its distortion has the three-term bound and tends to zero; sampled birth-time mesh tends uniformly to zero; absolute continuity of the integral handles small intervals. Endpoint integrals extending past 1 need a harmless explicit convention or bound. |
| U20 | 1034, 1046–1068 | Bounded-active-population $h_n^+=\Theta(n)$; height asymptotics (1046: $\mathrm{Height}(\mathcal T_n)/h_n^+\to1$ in $L^p$ for every $p\geq1$, via companion Theorem 3(3)); side-subtree/branch characterization of GH closeness to a segment; descendant distances bounded by birth/coalescence differences; uniform exponentially small chance of macroscopic side branches. The explicit assertion at 1034 that there is no universal GHP behavior is also retained: it requires a precise formulation and examples establishing nonuniversality, rather than merely noting that N09 does not state a measured limit. |
| U21 | 1084–1112 | Supercritical coalescence tail split and its $O(n^{1-2\alpha})$ hazard bound; sampled height convergence; joint corrected star-matrix convergence. Exact split must account for repeated samples and its birth cutoff (S07). |
| U22 | 1144–1160, `eq:GP`, `eq:GH` | Finite-dimensional distance limits plus leaf-tightness construct a unique-in-law compact measured limit with full support; matrix characterization identifies it. N17, not an assumed existence of $T(f)$. |
| U23 | 1168–1175, `condition3f` | Existence of finite-particle continuous inhomogeneous coalescent with independent uniform births and pairwise rate $f^{-2}$; distinct positive merger times; divergent integrated rate forces final merger; finite integrated rate gives positive nonmerger probability. Correct number of zero merger times versus remaining clusters (S09). |
| U24 | 1262–1276; 1291–1303, `rem:timechange` | Genealogy is an increasing binary plane forest; admissibility characterization; survival factor for unmerged clusters; planar factor $2^{-(k-1-r)}$; $H$ continuous increasing and invertible onto its range; time change to Aldous's coalescent with $\ell(t)=2f(H^{-1}(t))$; in divergent case $g_{0,k}$ determines the law. |
| U25 | 1473–1490, `eq:cvdn` | Critical sampled graph distances converge jointly to $\int_{C_{ij}}^{B_i}(2f)^{-1}+\int_{C_{ij}}^{B_j}(2f)^{-1}$. Derive from N12b, N07, reciprocal-profile convergence; zero diagonal via $C_{ii}=B_i$. |
| U26 | 1160 | The metric limit is a real tree because GH limits of real trees are real trees. Finite vertex sets are not geodesic real trees: explicitly pass to edge-realizations and bound their GH distance to the vertex sets after scaling. |
| U27 | 1308–1316, 1338–1388 | Finite sampled genealogy construction (condition away from repeated samples); frozen sampling reduction; Skorokhod coupling of auxiliary uniform times; active-cluster count; exact event-product calculation and asymptotic density including survival at zero. See S10. |
| U28 | 1390–1458, `eq:cv locale bis`, `eq:cv loi foret et temps` | Truncation count $R^n(\varepsilon)$, normalized finite-density representation, Fatou plus conservation-of-mass argument, Scheffé upgrade to $L^1$, convergence of bounded test integrals, generalized dominated convergence with $L^1$-converging dominating variables. Definition/index and normalized-input errors S10. |
| U29 | 1430, 1457, 1460–1468 | Finite-family nonnegative random variables: almost-sure coordinate convergence plus conserved total expectation 1 implies each expectation converges; variable-domination convergence theorem; recovery of pairwise merger times continuously from forest and labelled births. Diagonal recovery must use birth times, not an internal-node label. |
| U30 | 1496–1502 | $\Delta^n(u,v)=(b_n(u)+b_n(v)-2c_n(u,v))/2$ is nonnegative, symmetric, zero on diagonal, and satisfies triangle inequality; the set-distance minimum exists for nonempty sampled sets. Does not imply separation for distinct vertices without checking zero-time mergers. |
| U31 | 1517–1534, `eq:stepone` | Dyadic chaining: one-point N13 plus union bounds yields sample-net tightness in $\Delta^n/n$; finite final net controls all vertices; tail sum $\sum_{i\geq k}i^2 2^{-i/2}\leq c2^{-k/3}$ with one constant; probabilities and the ordered $k,n$ limits. |
| U32 | 1537–1553, `16/01/11h`, `eq:delta` | Uniform integrability gives small-population reciprocal tail bounds; compare $D^n/\sqrt n$ with tail plus $\Delta^n/(n\delta)$; transfer to graph-distance leaf-tightness. Inclusive endpoints require an extra negligible term (S03). |
| U33 | 1562 | Existence of fixed $M$, growth/rounding bounds for $\delta_{k,n}=4\lceil Mn/\sqrt k\rceil$, and $\delta_{k,n}>M_n$ uniformly over large $k\leq n^{1/3}$. |
| U34 | 1573–1585, `eq:step1Delta` | Marked-component count including unborn vertices; oldest marked vertex minimizes singleton-survival probability; expected-component bound for its singleton probability. A coupling or exchangeability argument for the oldest-vertex comparison is needed, not a new assumption. Correct sum upper index is $K$ (S11). |
| U35 | 1588–1614, `eq:step2Delta` | Exact one-step expectation decrement, Jensen/variance bound, reciprocal telescoping, signed-step lower bound, and final $3M\sqrt k/(4K)$ estimate. Treat the absorbing case $E[N_t]=1$ before division by $E[N_t]-1$. |
| U36 | 1623–1652, `eq:check1` | Each full block has many frozen birth indices; binomial lower-tail estimates imply occupancy of every block; collision estimates turn sample multiplicities into distinct vertices; $P(E^c)=o(k^{-4})$ uniformly over large $k\leq n^{1/3}$. Constants and active repeated births in the printed proof are defective (S12). |
| U37 | 1655–1689, `eq:tocheck` | Under block occupancy, small birth times give a nearby sample; for large birth time, alternating-block nonmerger probabilities multiply or satisfy a sufficient conditional upper bound; geometric decay with $p_k=\lfloor100\log k\rfloor$ is $o(k^{-4})$; $2p_k\delta\leq n\log^2k/\sqrt k$ eventually. The printed independence assertion needs proof. |
| U38 | 1697–1699 | Continuous pairwise merger time is strictly below both births; sampled points are almost surely not ancestor-related; together with full support this entails measure-one leaves. Justify the last implication for random measured real trees. |
| U39 | 1701–1719 | Finite integrated coalescence rate near zero: construct a summably controlled decreasing cutoff sequence, select infinitely many uniform births in its intervals, and obtain infinitely many nonmerging clusters almost surely. Interval placement in the product estimate needs repair (S13). |
| U40 | 1720–1723 | Infinite integrated rate near zero implies every sampled pair merges above zero and root degree one almost surely; extend from countably many sampled particles using full support. |
| U41 | 1723 | All other branchpoints are binary because merger times/heights are distinct; justify reduction of arbitrary branchpoints to the countable sampled skeleton, and clarify child count versus metric degree. |
| U42 | 1742–1759, `eq:limexc` | Conditioned simple-walk first-hitting excursion encoding; equality in law to uniform plane tree; scaled plane tree converges to Brownian CRT with exact normalization; excursion functional limit in $J_1$ and uniform topology; Skorokhod realization. External dependencies: the companion's uniform-plane-tree statement (cited as "Theorem 2"; E02, S20), Ald93, Kai76. |
| U43 | 1761–1779, `eq:alphatight` | Excursion positivity on compact interior sets implies `L2` and maximum bound; reciprocal uniform-integrability criterion gives `L1`; chosen coupling realizes the needed almost-sure assertion. Horizon, scaling and endpoint problems S14/S17. |
| U44 | 1781–1791, `eq:borne`, `eq:probalocale` | Uniform estimate $P(X_n(\delta)\geq\varepsilon)\leq C\delta^2/\varepsilon$ with one $C$ independent of $n,\delta,\varepsilon$; proposed Kemperman local formula. The displayed exact formula is false (S15), and the proposed uniform power of $\delta$ in the probability estimate is itself false (S16). The remark at 1786 that the local-limit proof "gives a slightly better upper bound" than CMY00 Lemma 3.6 is superseded by S16 and carries no separate obligation. |
| U45 | 1792–1803 | Local-limit upper bound $P(S_i^{2n+1}=k)\leq Ck^2/i^{3/2}$; reciprocal expectation bound; summation and Markov proof of U44. The last summation bound is false (S16), so this route is not checked. |
| U46 | 1806–1820, `eq:cvloi` | Joint convergence of truncated reciprocal functionals with the excursion; convergence-together argument as lower truncation goes to zero. Threshold discontinuity and level-set measure zero require proof; scaling needs correction S17. |
| U47 | 1824 | Joint Skorokhod coupling for excursion and a countable cofinal collection of truncations, then almost-sure uniform integrability. A single arbitrarily chosen truncation's coupling is insufficient for a random threshold without the simultaneous construction. |
| U48 | Remark 1829–1834 | Distributional identity $(1/2)\int_0^1e(t)^{-1}\,dt=^{(d)}\sup e$, with Brownian-excursion/CRT height normalization reconciled. Depends on M01, M05 and continuity/identification of limiting height. |
| U49 | 1851–1883 | GP/GH/GHP equivalence relations, quotient constructions and well-defined distances; each stated space is Polish; natural GHP-to-GH/GP projections are continuous and measurable. GP identifies only measure supports; GHP identifies entire compact spaces. Printed inclusion of GHP classes in GP classes is not literal without full support (S18). |
| U50 | 1891–1907, `eq:leaf-tight` | Conditional iid samples, leaf-tightness criterion, tightness of diameters and every fixed-radius covering number, and implication to GHP tightness (ADH13 Theorem 2.4). Preserve order $\delta\downarrow0$, $k\to\infty$, $\limsup_n$. |
| U51 | 1909–1914 | Subsequential limits admit coupled equal sampled matrices; sample sets are dense under leaf-tightness; distance-preserving map extends to an isometry of completions. A GH expression on noncompact countable subsets must be interpreted through completion/closure. |
| U52 | 1915 | Equality in law of full-support subsequential measured limits and uniqueness imply convergence; limiting sampled matrix has the prescribed law; full support follows. Matching only separate marginal laws is not by itself a proof; use N16 with its full hypotheses or reconstruction. |
| U53 | 246, 281 | Modelling remarks. Infection tracing of an SIR epidemic "falls within this framework" (246, citing BBKK23+); in the infection tree of a stochastic SIR dynamics, $S_n$ is the number of infected vertices at time $n$ (281). No statement about this paper's model is made. **Classification: companion background** (BBKK23+). No Lean obligation unless modelling claims are brought into scope. |
| U54 | 282–284 | The assumptions "include" the case where $(S_k(\mathbf x^n))_{0\le k\le 2n+1}$ is a simple-random-walk excursion of length $2n+1$, with $\alpha=1/2$ and $f$ a normalized Brownian excursion. With the paper's indexing $\mathcal T_n=\mathcal T_n(\mathbf x^n)$ (309), the horizon $n$ covers only the first half of the excursion; heuristically, by `eq:limexc` (1748), the profile would then be $f(t)=\sqrt2\,e(t/2)$ in law, not $e$. The full-horizon reading at 1742 runs into S14 instead. **Classification: source slip** (S23); otherwise a repetition of U43 and M05. No obligation beyond M05. |
| U55 | 292, 570 | Algorithm 2 "extends" (292) or "is a generalization of" (570) the DR76 connection between random recursive trees and Kingman's coalescent, in the union-find setting. Mathematical content: with all signs $+1$, Algorithm 2 starts from $n+1$ singletons and at each step joins a uniform ordered pair of distinct trees, and its tree, with active labels collapsed, has the uniform recursive tree law. **Classification: follows from proved items**, namely N01 (`forward_reverse_same_law`) and the first clause of U01 (`treeLaw_allPlus_eq_urtLaw`); no theorem states it. The attribution to DR76 and the cited applications are literature background. |
| U56 | 294 | Dependency statement: the scaling-limit results "only rely on" the reverse construction and its consequences (`thm:samelaw` and Lemmas N02–N04, recalled from companion Theorem 8 and §2.3) together with companion Theorem 3 (3). Read literally the list is incomplete: 259 and `cor:CRT` (1744) also use the companion's uniform-plane-tree statement (E02). **Classification: source slip** (S20), cross-referenced to E01–E03. No Lean obligation. |
| U57 | 312 | Heuristic: $\mathbf 1_{\{x_i=1\}}/S_i$ "essentially" represents the probability that at step $i$ the degree of a given active vertex changes. In Algorithm 1 (472–475) the vertex is chosen uniformly among the $S_{i-1}$ active vertices of $\mathcal T_{i-1}$, so the forward probability is $\mathbf 1_{\{x_i=1\}}/S_{i-1}$. The quantity $\mathbf 1_{\{x_i=1\}}/S_i$ is the reverse height-increment probability of N02 (626). **Classification: heuristic**, with the index slip S21; mapped to N02. No obligation. |
| U58 | 1512 | Heuristic for `tightness time estimate` (N13): each window of length $n/\sqrt k$ contains about $\sqrt k$ of the sampled vertices, and the probability that $\sqrt k$ vertices do not coalesce with a given vertex during $n/\sqrt k$ time steps is "strictly positive". The argument needs this non-coalescence probability to be bounded away from one, as in N14 (1568) and the bound $3/4$ at 1677. **Classification: heuristic**, with the wording slip S22; mapped to N14 and U37. No obligation. |

Rows U53–U58 were added on 30 October 2026 from the
[whole-source omission scan](omission-scan-2026-10-30.md), which found no
uncovered theorem, lemma, or proof step on which a stated result depends. None
of these rows adds a Lean obligation beyond M05; U55 can be derived from proved
results but is not stated as a theorem. The scan's two description gaps, at 254
and 1786, are recorded in U01 and U44.

## External dependencies retained

These are source references, not currently established Lean imports.

| ID | Source use | Required dependency |
| --- | --- | --- |
| E01 | 338, 1046 | Companion `BBKK23+`, Theorem 3(3): $L^p$ height asymptotics with its growth hypotheses. |
| E02 | 259, 1744 | Companion uniform-plane-tree law for stopped symmetric walks, including size and root conventions. The source cites it as "Theorem 2"; in the local companion it is the Examples paragraph, and Theorem 2 is `thm:BGW` (S20). |
| E03 | 595–649 | Companion Theorem 8 and §2.3: reverse-law identity and height/birth/coalescence laws. |
| E04 | 1291, 1301–1302; alternative 399 | Aldous `A98` density (2), time-changed coalescent and Theorem 2. |
| E05 | 773, 1338, 1419, 1431, 1457, 1759, 1816–1820, 1824, 1911, 1915 | Portmanteau, Skorokhod representation, Scheffé, Fatou, dominated/variable-domination convergence, probability convergence-together and uniqueness. These may use matching Mathlib theorems. |
| E06 | 978 | `BBI01`, Theorem 7.3.25: GH distance bounded by half a correspondence distortion. |
| E07 | 1744–1750 | `Ald93` uniform-plane-tree CRT limit and `Kai76` excursion invariance principle. |
| E08 | 1786–1794 | `CMY00` Lemma 3.6, `Pit06` §6.1 Kemperman formula, `IL71` Theorem 4.2.1 local limit bounds. The manuscript's claimed consequences are not certified by citation alone. |
| E09 | 1859, 1872, 1881, 1907 | `ADH13`: Polish metric-space quotients and GHP compactness/tightness criterion. |
| E10 | 1863, 1885 | `Loh13` matrix characterization; `Bla21` Lemma 4, combining GP and GH weak convergence. |
| E11 | 382, 415 | Comparative random-tree facts and long dendron convergence (`LGLJ98`, `DLG02`, `JS11`, `Jan12`, `Kor15`, `KR19`, `JJS11`, `ET21`, `Jan21`). |

The supplied directory has no `bibli.bib` or referenced figure files. Bibliography
keys therefore identify dependencies but do not provide enough local bibliographic
metadata for a verified publication citation. This is a source-packaging limitation,
not permission to invent references or licensing.

## Source issues requiring explicit treatment

The manuscript itself was not edited. The approved M06 correction is the only
user decision incorporated here; all other proposed corrections require explicit
recording as departures if adopted. A false intermediate equality does not by
itself prove its final theorem false.

| ID | Source location | Finding and disposition |
| --- | --- | --- |
| S01 | 409–411, 1107–1109 | **False all-pairs limit.** Every graph-distance diagonal is zero, but the stated limit at $i=j>0$ is $2H(U_i)$, positive almost surely for a positive reciprocal profile. User authorized retaining the intended off-diagonal formula and setting the diagonal to zero. Also replace the accidental $U_1,\ldots,U_n$ by $U_1,\ldots,U_k$ in the statement description. The proof display `eq2 thm sur-critique` needs the same diagonal correction: for an identical coordinate, coalescence equals its birth and N10 does not give a zero normalized limit. This is a changed statement, not a proof of the literal formula. |
| S02 | 647–648 | **Missing distinctness.** With $n=1$, $x_1=+1$, any active $u=v$ has birth and self-coalescence time 1. At $c=0$ the displayed left probability is 0 and right side $1/\binom22=1$. Add $u\ne v$ to the corrected law; retain the original defect. |
| S03 | 667, 879–880, 1547–1552 | **Surrogate is not a distance.** Inclusive endpoints give $D^n(u,u)=1/S^n_{b_n(u)}>0$. Its use in approximation N07 can survive bounded endpoint errors. The direct $D$-versus-$\Delta$ inequality at 1552 also lacks endpoint terms: for $u=v$ outside the reciprocal tail its RHS can be zero while LHS is positive. Derive a corrected inequality with explicit negligible endpoint contribution. |
| S04 | 630–633 | **Terminal Bernoulli parameter.** The preceding range permits $n=\tau$, so $1/S_n$ is undefined. Only positive-step/actually used indices need Bernoulli variables; formulate accordingly or restrict this display to $n<\tau$. |
| S05 | 758–766 | **Insufficient displayed bound.** The lower bound $S_{an-k}\geq\varepsilon n-k$ need not stay of order $n$ on the printed range ending at $k=\varepsilon n$. Use a shorter interval bounded away from that endpoint; this repairs the argument without changing N06(i). |
| S06 | 806–808 | **False exact interval pairing.** For one $+1$ step and $a=b=1$, left side is $1/2$, all right sums vanish. The left boundary must use $S_{a-1}$ and the relevant minimum must include the starting height. The global identity at 794 is unaffected. |
| S07 | 972, 1085–1094, 1111 | **Sampling details.** Frozen birth time is freezing label minus one. N04 does not apply to coincident iid sampled vertices; its exact use needs the $P(V_1=V_2)$ contribution or conditioning on distinctness. The first displayed tail bound at 1087 also needs checking when only one birth exceeds $(1-\delta)n$: coalescence is bounded by the minimum, so its early/late decomposition must match this minimum. |
| S08 | 415 | **Covering-number quantifier.** Divergence cannot hold for every positive radius, since sufficiently large radius covers a bounded-diameter limit-scale tree by one ball with high probability. State a sufficiently small fixed radius with positive limiting branch-length tail; retain non-tightness as the intended claim. |
| S09 | 1175, 1267–1288 | **Component indexing and order.** With $r+1$ remaining components there are $r$ zero merger times, whereas 1175 says $r$ components. “Ordered forest” also needs a convention for ordering components: random order of children does not order roots, and arbitrary root orders would need an additional combinatorial factor in N11. Resolve before certifying the density. **Disposition (30 October 2026):** resolved by the documented working interpretation (trees ordered by root label, no extra factor; children ordered uniformly), under which N11 is proved in source form (`CoalescentForests.lean`); the interpretation is not a user ruling. |
| S10 | 1310–1468 | **Local-limit proof interfaces.** The statement conditions on only $r$ birth variables at 1327 but the proof conditions on all $k$ at 1353. Iid sampling may collide, while 1358/1366 use distinct-sampling factorial denominators and inconsistent inclusion of active vertices. At 1390 $R$ is defined as the first index above the cutoff rather than the number at/below it, and $C_0$ is undefined. Inputs at 1411/1440 are scaled although the preceding discrete density was defined on integer inputs. The asserted probability convergence at 1383 needs a coupling compatible with the merely measurable reciprocal profile; convergence of locations alone is insufficient. These are proof obligations, not justified by writing the density symbol. |
| S11 | 1566–1585 | **Negative time and indices.** $i=0$ makes $(i-1)\delta<0$, outside the forest definition. Intended applications use positive blocks. The sum over $v_i$ in 1584 goes through $K+1$ although only $v_0,\ldots,v_K$ exist. Reciprocals in 1600 require an absorbing-case split. |
| S12 | 1633–1652, 1677–1687 | **Tightness proof gaps.** The available binomial mean lower bound is roughly $1.5M\sqrt k$, but 1642 uses mean $6M\sqrt k$ and threshold $4M\sqrt k$; those constants do not follow. The bound for four equal births at 1652 ignores the shared birth time $n$ of all active vertices, so the stated uniform-vertex bound cannot follow from distinct-vertex probabilities. Restrict collisions to relevant frozen births or change the argument. At 1677 the asserted conditional independence needs proof; conditional probability bounds may suffice. At 1687 the preceding bound proves $O((3/4)^{(p_k-1)/2})$, not the stated little-$o$ of that same quantity. |
| S13 | 1701–1723 | **Condensation argument indexing.** Proof heading refers to nonexistent part (3), presumably part (2). Denominator $\binom k2$ requires starting at $k\geq2$. For births chosen in consecutive cutoff intervals, $[B_{i_{k+1}},B_{i_k}]$ is not contained in $[\varepsilon_{k+1},\varepsilon_k]$, so the displayed integral comparison needs control over adjacent intervals or a revised choice. “Degree two” at other branchpoints must mean two children, not metric degree two. |
| S14 | 1742, 1759–1770 | **Extinction boundary.** Brownian excursion array has $\tau=2n+1$, but M03 assumes $\tau>n$ at its horizon. Apply to a pre-extinction horizon and compare trees/scalings, or establish a terminal-time extension. Endpoint reciprocal convention alone does not discharge the strict survival hypothesis. See also S23 (Introduction, 282–284). |
| S15 | 1787–1791 | **False displayed local formula.** The factor $\frac{k-1}{i}P(S_i=k)$ is the ballot count for paths from 1 staying strictly above level 1, not above 0, so the display gives $P(S^{2n+1}_i=1)=0$. For $n=1,i=2,k=1$ the only excursion is $1,2,1,0$: left side 1, right side 0; for every $n\ge1$ the left side at $i=2,k=1$ is $(n+1)/(4n-2)>0$. Lean: `not_kempermanDisplay` (arbitrary unconditioned probabilities, domain $n\ge1$, $k\ge1$) and `not_kempermanDisplay_srw` in `Freezing2/Audit/ExcursionCounterexamples.lean`; `excursionLaw_eq_cond` identifies the model with the conditioned walk. The range also includes $i=2n+1$, where $2n-i+1=0$. Correction for $1\le i\le2n$, $k\ge1$: factor $P(S_i=k)-P(S_i=k+2)=\frac{2k}{i+1}P(S_{i+1}=k+1)$ (checked by enumeration for $n\le6$, not in Lean); the bound $Ck^2/i^{3/2}$ for $i\le n$ is unaffected. |
| S16 | 1781–1785, 1799–1803 | **False uniform estimate and false summation step.** (a) `eq:borne` with one $C>0$ independent of $n,\delta,\varepsilon$ is false: for $n\ge2$, $\delta=1/\sqrt n$, $\varepsilon=1/(2\sqrt n)$, on $\{S^{2n+1}_2=1\}$ (probability $C_{n-1}/C_n=(n+1)/(4n-2)>1/4$) one has $X_n(\delta)\ge2\varepsilon$, while $C\delta^2/\varepsilon=2C/\sqrt n\to0$. Lean: `not_uniform_smallValue_bound` (and `_of_real`), via `excursionEquivDyckWord`, `card_excursionPaths`, `excursionLaw_real_second_eq_one`. The counterexample lets $\varepsilon\to0$ with $n$, so it does not refute a version with $C=C(\varepsilon)$, which is all Step 2 uses; it also shows no uniform bound $C\delta^a/\varepsilon$ for $a>1$. (b) The last inequality of line 1801 needs $\sqrt n\sum_{i\le n}i^{-3/2}$ bounded, but it is at least $\sqrt n$ (`not_bounded_sqrt_mul_sum_inv_rpow`). |
| S17 | 1764–1776, 1808–1813 | **Half-horizon/full-horizon mismatch.** The sum only runs $1\leq i\leq n$ on an excursion of length $2n+1$, with scale $\sqrt n$, but the claimed limit is the full-excursion integral with scale $\sqrt{2n+1}$. Time reversal may control the missing half for uniform integrability, but cannot make the stated equality or convergence literal. Several displayed sum/integral identities also shift from indices $1,\ldots,n$ to $0,\ldots,n-1$. See also S23 (Introduction, 282–284). |
| S18 | 1876–1877 | **Quotient inclusion.** Full compact measured spaces modulo measure-preserving isometry do not inject into GP classes when support is not full: adding a point of zero measure changes the GHP class and not the GP class. Use the natural projection rather than a literal subset assertion, or restrict to full-support spaces and state that restriction. **Disposition (30 October 2026):** resolved by the projection reading: `MeasuredGHSpace.gpProjection` (1-Lipschitz) with `not_injective_gpProjection` proving it is not an inclusion (`GromovProkhorov.lean`). |
| S19 | 280 | **Unqualified absence of GHP scaling limits.** The introductory assertion about recursive trees cannot mean the absence of every scaled limit: the diameter after $n$ attachments is at most $n$, so sufficiently fast deterministic shrinking collapses the uniformly measured tree to a point. The intended nondegenerate normalization and no-limit/non-tightness formulation must be specified before formalizing this clause. The claim remains in U04b; it is not discarded as motivation or counted as proved by M06. The collapse observation is now a Lean theorem (`tendsto_urtMeasuredLaw_onePoint`, sharp threshold $\log n$), and the qualified clause (no nondegenerate GHP limit) is proved in `MainResults/RecursiveNoLimit.lean`. |
| S20 | 259, 1744; 294 | **Companion numbering.** The source cites "[BBKK23+, Theorem 2]" for the uniform-plane-tree law (259) and for the equality in law of $\mathcal T_{2n+1}$ with a uniform plane tree with $n+1$ vertices (1744). In the local companion `../freezing1/attachement-uniforme-1-final.tex`, all theorem-like environments share one counter: Theorem 2 is `thm:BGW` (its lines 277–280, the geometric Bienaymé tree), while the uniform-plane-tree statement is the Examples paragraph (its lines 268–274). `thm:samelaw` is the eighth environment (its line 661), which matches the source's "Theorem 8". The published companion's numbering was not checked. The dependency statement at 294 also omits this use of the companion (U56). Disposition: a citation correction; it affects E02, U01, U42, U56 and M05 only through the reference. |
| S21 | 312 | **Forward-step index in a heuristic.** The source says that $\mathbf 1_{\{x_i=1\}}/S_i$ "essentially" represents the probability that the degree of a given active vertex changes at step $i$. In Algorithm 1 (472–475) the vertex is uniform among the $S_{i-1}$ active vertices of $\mathcal T_{i-1}$, so this forward probability is $\mathbf 1_{\{x_i=1\}}/S_{i-1}$; $1/S_i$ is the reverse increment probability of N02. Disposition: heuristic only (U57); no obligation. |
| S22 | 1512 | **Inverted wording.** The heuristic says that the probability that $\sqrt k$ vertices do not coalesce with a given vertex during $n/\sqrt k$ time steps is "strictly positive". The argument needs this probability to be bounded away from one, as in N14 (1568) and the bound $3/4$ at 1677. Disposition: heuristic only (U58); N13 and N14 are certified from their own statements. |
| S23 | 282–284 | **Excursion indexing in the Introduction.** The example in which $(S_k(\mathbf x^n))_{0\le k\le 2n+1}$ is a simple-random-walk excursion of length $2n+1$, with $\alpha=1/2$ and $f$ a normalized Brownian excursion, does not match the indexing $\mathcal T_n=\mathcal T_n(\mathbf x^n)$ (309): the horizon $n$ covers only the first half of the excursion. Heuristically, by `eq:limexc` (1748), $S^n_{\lfloor nt\rfloor}/\sqrt n$ then behaves like $\sqrt2\,e(t/2)$, so the profile would be $f(t)=\sqrt2\,e(t/2)$ in law rather than $e$. The full-horizon reading used at 1742 runs into the strict-survival problem S14. Related to S14 and S17; maps to U54, U43 and M05. Disposition: no obligation beyond M05. |

S20–S23 were added on 30 October 2026 from the
[whole-source omission scan](omission-scan-2026-10-30.md). Further minor slips
found by that scan affect no coverage and have no S-row: lines 587, 614,
707/880, 1432, 1566, 1583/1594, 1623, 1681 and 1698. They are listed in
[MANUSCRIPT_RECOMMENDATIONS.md](../MANUSCRIPT_RECOMMENDATIONS.md).

## Open questions and future work

These are not theorems to prove in the current paper and are retained separately:

- O01, line 367: whether the maximum-population hypothesis in the critical GHP
  theorem can be removed. The finite-dimensional result without it remains U04a.
- O02, line 385: upper dimensions and their dependence on fine behavior near zero
  are deferred to future work. The asserted lower bounds remain in U04a.

No active `open` or `conjecture` environment occurs. The superseded proof at
1048–1050 is TeX-commented and is not an additional active mathematical claim.
The struck-out probability expression at 1531 is superseded by the adjacent
active correction; it is not independently advertised. Figures, prose motivation,
and bibliography boilerplate carry no additional proof obligations beyond the
mapped examples and comparisons.

## Main dependency priorities

1. Establish finite sign-path counts, valid forward/reverse probability models,
   and corrected N01–N04. Prove companion dependencies rather than postulating
   them. These support every regime.
2. Establish the five parts of N06, including uniform endpoint errors, and N05/N07.
   N06(iii) plus the verified companion height theorem yields M01.
3. Prove N08 and the GH correspondence argument for M02; prove N10 and the
   user-corrected matrix limit for M06. These use the common finite model and
   deterministic estimates without the critical forest machinery.
4. Construct the continuous coalescent and its actual law, resolve N11/N12
   interfaces, establish N13/N14 with corrected proof details, and formalize the
   metric-measure compactness criterion to obtain M03 and M04.
5. Resolve the Brownian-excursion argument issues before using it for M05/U48.
   Keep dimensions, long dendrons, comparison claims, bounded-population theorem,
   and appendix foundations visible as unresolved coverage even while prioritizing
   the Introduction's results.

The source has not changed during this initial inventory. Before claiming full
coverage, reconcile every row with current declarations and repeat an omission
scan of the source, including substantive prose, remarks, appendices, and any
newly adopted source corrections. Such a scan was carried out on 30 October 2026
([omission-scan-2026-10-30.md](omission-scan-2026-10-30.md)). It was done by an
agent, not a human reviewer, and must be repeated if the source or the claimed
coverage changes.
