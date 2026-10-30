# Companion source snapshot

The initial snapshot is the minimal whole-module import closure of `Freezing1.MainMaximum` from the local companion project, copied into `Freezing2/Companion` to make the dependency self-contained. It comprises 16 Lean modules and 3243 original source lines. A separate six-module reverse-process extension is recorded below. `MainHeight`, the companion root entry point, the reverse-forest development, and unrelated companion results are not needed by this closure and were not copied.

Copy time: `2026-10-29T11:50:12+01:00` (`Europe/Paris`). Source checkout: `../freezing1`. Source Git identity: No HEAD commit exists in the source checkout at snapshot time.

All source bytes were read before writing any destination module. Every module and the auxiliary files listed below were reread and compared byte for byte both before and after the copy; all comparisons passed. The SHA-256 identities below, rather than an older report or a sibling build artifact, identify this snapshot.

## Permitted modifications and license

Each Lean file has one short provenance comment after `module`, and each `public import Freezing1.X` is relocated to `public import Freezing2.Companion.X`. All namespaces remain `Freezing1`; all other statements and proof bodies are unchanged. No proof weakening or unproved dependency was introduced by copying.

The complete original Apache-2.0 `LICENSE` and `NOTICE` are preserved verbatim in `Freezing2/Companion/`. They apply to the copied original code and notices. This copying does not select or change the license of the rest of this project and does not relicense either manuscript. The preserved notice refers to skill materials in the original project; those materials are not part of this source snapshot.

## Source theorem and semantics

The mathematical source is `attachement-uniforme-1-final.tex`, Theorem `thm:height` (III), lines 293–309, used by `attachement-uniforme-2-final.tex`, Theorem `thm:heightalpha`, lines 331–338. The source assumes survival through each horizon and $\log(n)/h_n^+\to0$ and concludes convergence of the maximum height divided by $h_n^+$ to one in every real $L^p$, $p\ge1$.

`Freezing1.maximum_height_tendsto_Lp` in `MainMaximum.lean` has exactly these assumptions and expresses the conclusion as convergence of the error `eLpNorm` under the actual forward tree laws. The measures may vary with the horizon; no common coupling is required for convergence to a constant. It does not assume concentration, moment bounds, a Bernoulli representation, or reverse/forward equivalence.

`Forward.State` keeps persistent vertex IDs, a rooted graph, the active subset, parents, heights, and freezing labels. `Forward.transitionLaw` pushes uniform measure on the active vertices through an attachment or freezing step; `Forward.treeLaw` iterates this conditional transition by measure bind. `treeLaw_valid` proves the invariants almost surely. `ValidAt.height_eq_tree_dist` identifies each stored height with distance from the root in the finite induced tree. `Forward.treeHeight` is the maximum stored height over exactly that finite vertex set, including frozen vertices. Thus the random variable is the maximum graph height of Algorithm 1, not a surrogate height law.

## Proof correspondence and unresolved integration

The dependency follows the direct forward process: uniform active-height averaging gives a sub-Poisson moment-generating-function bound; total exponential weight over all vertices gives the maximum bound with its finite $n+1$ factor and one-edge shift. Bennett tails yield convergence in probability. Jensen and exponential moment bounds yield a uniform higher moment, and a cutoff/Hölder argument upgrades this to each finite real $L^p$. The positive height-scale lower bound and logarithmic estimates are proved within the closure. This verifies the companion height result by a substantive alternative route; it does not check the manuscript’s reverse-forest construction, equality in law, or its Bernoulli representation. Those remain separate source obligations.

At copying time, the current `MainMaximum` had no emitted `.olean`, and the `MaximumMGFLimits` source was newer than its emitted `.olean`. Other closure modules had newer emitted `.olean` files, but their presence was not used as proof evidence for this destination snapshot. The parent subsequently reported a successful fresh destination build of `Freezing2.Companion.MainMaximum` and its full closure: exit 0, 3,788 jobs, no warnings. No Lean or Lake command was run in the sibling project. The subsequent M01/N06 integration checkpoint built 54 modules and checked the transitive axioms of 535 explicit declarations, including the final integer-sign/model bridges and height wrappers, with only `propext`, `Classical.choice`, and `Quot.sound`. That checkpoint is recorded in `docs/milestone-audit.md` and the project evidence files. It does not cover later dependency extensions; current integration evidence is never inferred from lexical scans or the sibling's artifacts.

## Pinned environment and auxiliary identities

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib input revision: `v4.35.0`; locked commit: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- The Lean toolchain bytes and every dependency name/revision in the two projects’ manifests agree.

| Original absolute source path | SHA-256 |
| --- | --- |
| `../freezing1/LICENSE` | `cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30` |
| `../freezing1/NOTICE` | `c9ad867a1df7a14a7b38f2c55a5e17b4ad294816e0334fcde8a095a053308454` |
| `../freezing1/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `../freezing1/lakefile.toml` | `b73f24c99b2289d0a1e062e77ea16c40fd0c19621572d11cd1ad98fc03104c83` |
| `../freezing1/lake-manifest.json` | `e0c8045c1dbf910e9a1cb575269748534232a21b9cf3df1fc36c1c21d001344a` |
| `../freezing1/attachement-uniforme-1-final.tex` | `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df` |

## Module identities

The destination for each row is `Freezing2/Companion/<module>.lean`; the original source path is given explicitly. Line counts describe the unmodified source bytes.

| Original absolute source path | Lines | Original SHA-256 | Vendored SHA-256 |
| --- | ---: | --- | --- |
| `../freezing1/Freezing1/BernoulliArrayLimits.lean` | 168 | `df99d39f04f8d229ff13ee2c939cff77a36100cb44629bd08196bf608fdc9ec8` | `170510aaaeb53cd2b84e44697c377702570aab22c6cd467bfb6b2383742e5f4d` |
| `../freezing1/Freezing1/BernoulliConcentration.lean` | 155 | `1318fdd06cae3b71f4fede4fdbfca460c31cb83c167bec2da6efd2a315051036` | `42bfbc723044e5abb9963b8155ab4d1b86697d93cd9118167424ef9f7084a4a9` |
| `../freezing1/Freezing1/BernoulliLimits.lean` | 302 | `0a376d25aa7735fd6ea45368202aa45e8dae3e621b96e0e7a1c257464d27ce99` | `43758d2c09dfe46673a9362975301382963826e570f820728c6a5e27c1f3a23b` |
| `../freezing1/Freezing1/Extinction.lean` | 99 | `74da01e5cccd85cd3b55032a5afa4c8ca0fd5c6b5c3dc3770fed869291706d76` | `4dd94a7e7e6a746402659fd3c7dd25544f2ba7ae6ca6f274cab304cd4afae75b` |
| `../freezing1/Freezing1/ForwardHeight.lean` | 372 | `9cce14224a672919fc61de2d697644eebcb7b1a5ac66954b9f5fdaf20b2b562c` | `84965075fda93cee546b03cedfb7c6b445a36b31212507eb70cfa7bed1eeb3c6` |
| `../freezing1/Freezing1/ForwardLaw.lean` | 182 | `cf76862efe85d37936a225df1aeaec5fd4176ae555b21e9e3e382b771e43c124` | `f478f1a65ee69ff915a2525644dcdaca8266c59cd5f37ffed80cac40c8b4641b` |
| `../freezing1/Freezing1/ForwardMaximum.lean` | 308 | `9475945570b7d97ab8709acec6f824cee652106e1a12ed346ed7f0c89f4d04c1` | `5e9a625ef13553b255a1e295bdea7777a34e23906d7132df0d8014f9e0debc6e` |
| `../freezing1/Freezing1/ForwardTree.lean` | 343 | `71af521f6cd0322ca8370514f5e0e71aa425ce63d04036e5f6bb0c5e8e0c1317` | `98314d55efbd52a72c8d962cc4ab8c8d1df67ad9d5b0291c6fbbf6b3944cfcc8` |
| `../freezing1/Freezing1/HeightAsymptotics.lean` | 90 | `ae2f8c0d617bee6db785852c16bc6730b94362c0508c6b2ac6b0957368c40a98` | `205132a98d145aa2d922e78a7ebd0a3b0ecf7bc106916724945c05512038a833` |
| `../freezing1/Freezing1/HeightScale.lean` | 125 | `b05953b141a3e164b868d2f7c9a72ea30b55f598da45fb6ebcdd3883222fa1be` | `1d0bd081613fad224e5f6260b2bd3fc6167132eb1fdd67f172d895b154d83215` |
| `../freezing1/Freezing1/HeightTailBounds.lean` | 213 | `aebce79a57e5490bcf72b2fe3c6dcba0c7e5fee9fb18a84e6e4552034a0f0f6a` | `70f9fd795928b2bf0aff809e980161b255cc992a7fd6b714a351add3f8dc04c8` |
| `../freezing1/Freezing1/MGFLimits.lean` | 244 | `d032302835691d582a427ae5bb8dae286fda760fdb0db7a6b363c3a4f9344c92` | `7b94463a57535bf2c3b919ae6443273d22c50cf602030a9a0c2e2c39da395e94` |
| `../freezing1/Freezing1/MainMaximum.lean` | 173 | `acb4d8811b54abb1fea6ec04a55500eaaaa71c9eb964f6460a1ce52ae841e1c1` | `75676dda3861029a9e89b351a0e945fbea30054ea52f980d7825e6d0fc398f85` |
| `../freezing1/Freezing1/MaximumMGFLimits.lean` | 159 | `bbe5f0e5d7eda88bd46acf2e633d591c23d2f9b69277565941b7e6933ff811e8` | `b9da9c5c27086350f489c42a24e4b9bf38102b478f57007f434698c435cb293a` |
| `../freezing1/Freezing1/Path.lean` | 93 | `b57e8e3cd4e87b80f2c15fe306ec9fe8482eda60592b5b946d7ab0464edf4fdb` | `897fcd16ceadc6594a98152a6dfc0719b8fb1cb94c8ce3aacb9f467adff0761f` |
| `../freezing1/Freezing1/RateFunction.lean` | 217 | `d4117c3fc3bd6f269d9c5de7c7a3a4b5be58deab2ccc002ec10e13ea171282c1` | `f556e2a4b83e0b933c32ea6ff022725b09b7ec769ba388424532c18175f503d7` |

## Import closure

Only local companion edges are listed; Mathlib imports are retained unchanged.

- `Freezing1.BernoulliArrayLimits`: `Freezing1.BernoulliLimits`.
- `Freezing1.BernoulliConcentration`: `Freezing1.RateFunction`.
- `Freezing1.BernoulliLimits`: `Freezing1.BernoulliConcentration`.
- `Freezing1.Extinction`: `Freezing1.Path`.
- `Freezing1.ForwardHeight`: `Freezing1.ForwardLaw`, `Freezing1.HeightScale`.
- `Freezing1.ForwardLaw`: `Freezing1.ForwardTree`.
- `Freezing1.ForwardMaximum`: `Freezing1.ForwardHeight`, `Freezing1.BernoulliConcentration`.
- `Freezing1.ForwardTree`: `Freezing1.Extinction`.
- `Freezing1.HeightAsymptotics`: `Freezing1.HeightTailBounds`.
- `Freezing1.HeightScale`: `Freezing1.Path`.
- `Freezing1.HeightTailBounds`: `Freezing1.BernoulliConcentration`.
- `Freezing1.MGFLimits`: `Freezing1.BernoulliArrayLimits`.
- `Freezing1.MainMaximum`: `Freezing1.ForwardMaximum`, `Freezing1.HeightAsymptotics`, `Freezing1.MaximumMGFLimits`.
- `Freezing1.MaximumMGFLimits`: `Freezing1.MGFLimits`.
- `Freezing1.Path`: no companion imports.
- `Freezing1.RateFunction`: no companion imports.

## Reverse-process dependency extension

Copy time: `2026-10-29T12:05:17+01:00` (`Europe/Paris`). Source checkout: `../freezing1`. Source Git identity: No HEAD commit exists in the source checkout at this second snapshot.

This second snapshot adds the minimal missing closure of `Freezing1.ReverseForest`: six Lean modules and 1273 original source lines. The two shared dependencies, `Path` and `Extinction`, were compared against the existing vendored files after exactly the original import/comment transformation and were identical. The original 16 Lean files were not edited. The combined snapshot now contains 22 Lean modules and 4516 original source lines.

All eight source modules in this closure were read before copying, then reread and compared byte for byte before and after the copy. The source manuscript, license, notice, toolchain, and manifest were likewise stable. Existing LICENSE and NOTICE remained byte-identical to their source and were not rewritten. The source manuscript hash remains `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`; the same toolchain and dependency pins apply. No sibling file was edited and no sibling build was run.

### Exact coverage and current limitations

The source was independently reread at scaling-paper Algorithm 2 (lines 572–584), the birth/coalescence definitions (lines 612–619), and N02–N04 (lines 622–649). These additions are concrete construction dependencies, not proofs of all these named source results.

- `RootedForest` constructs finite parent/root/depth forests, proves that joining distinct roots adds exactly their edge, and proves that stored depth is graph distance from the component root. Distinct roots are disconnected. `RootedForestLaw.joinLaw` samples the actual uniform ordered pair of distinct roots; legal reverse merge steps are proved to have at least two roots.
- `UniformRootPair` proves exact masses of one ordered pair, the second root, and either ordering of a fixed pair of distinct roots. The last probability is `2/[S(S-1)]`, equivalently `1/choose(S,2)`. This is the finite one-step hazard, not yet the law of an actual coalescence time.
- `ReverseForest.lawAfter` and `ReverseForest.treeLaw` construct marginal forest laws by iterated measure bind. Validity proves the deterministic label set, root/component count, acyclicity, and terminal finite tree, including the extinction endpoint. The states currently have no edge-time labels. No joint trajectory, conditional-history distribution, or forward/reverse equality in law is constructed by these modules.
- `ReverseForest.transitionLaw_height_increment` proves the exact one-step kernel probability for an existing vertex. Its reverse step indexed by `i` goes from source forest time `i+1` to time `i`, with denominator `S_(i+1)`. After the one-index shift it is the probability in N02, but a concrete joint-history construction and conditioning bridge are still required before claiming N02. `joinLaw_depth_support` additionally proves that increments are only zero or one.
- `BirthTime` uses `Sum.inl j` for active label `a_(j+1)` and `Sum.inr i` for frozen label `i+1`, whose reverse birth time is `i`. `ReverseForest.mem_phaseLabels_iff_birthTime` connects that deterministic map to actual forest presence. `uniformVertexLaw_eq` and `ReverseForest.uniform_birthTime_lt` connect conditional uniform vertex sampling in the terminal reverse forest to the exact birth-time probability.
- `HistoryProbability` proves only the deterministic factorial relation between products of reciprocal active counts. Its name does not certify a history law, a history-probability formula, or a bijection between forward and reverse histories. N01 remains unresolved.
- N04 still requires an actual history-based coalescence-time random variable, the distinct-vertex condition from source issue S02, the transition coalescence characterization, and the survival product. N07 still requires the joint height-increment/concentration argument and the uniform graph-distance comparison; none is silently imported as a hypothesis.

The parent’s fresh destination build of this extension through `Freezing2.Companion.ReverseForest` passed with exit 0, 3,665 jobs, and no warnings. The earlier 16-module height build alone did not cover this extension. A fresh transitive axiom audit including these six modules and their new history consumers remains a separate integration check; the earlier 54-module/535-declaration checkpoint must not be read as evidence for subsequently added files.

### Extension module identities

| Original absolute source path | Lines | Original SHA-256 | Vendored SHA-256 |
| --- | ---: | --- | --- |
| `../freezing1/Freezing1/BirthTime.lean` | 156 | `72cb5956ae5ff792ddbdb3a6d8c0c04f272f4d501fb21ee8658a319c9981bd31` | `7132e6e092415d80fac9cd4232ba9b569d9fbdae6b88d69e0a475f8b36690c31` |
| `../freezing1/Freezing1/HistoryProbability.lean` | 155 | `d1d8c59eb3a0d98fac0f63fcdd929a87f61739930e3b4e706395673ab4e4ba5f` | `edb323fab772d4d7a809d2bcfd803ba7964c0c6063563e3b34fe25f9b86b5274` |
| `../freezing1/Freezing1/ReverseForest.lean` | 268 | `f4fd35aa1289db05bca5bed3932257c0c0c07604fcf292d3d08b1f02a99aba10` | `7af5bc77923fccfb1943743b9ce5c2c27df1bf3942beccccd46334b7881bbdb8` |
| `../freezing1/Freezing1/RootedForest.lean` | 437 | `c54405f0cc53b7c7e4e80a84ac55ce4d0677bcffc3214106796ce7cb7c24fc23` | `fc6747f1491169b10cfd92fe622d4dbf0b1dcd7aaf2039a07a45bfef321861c9` |
| `../freezing1/Freezing1/RootedForestLaw.lean` | 127 | `3393676327c51f229255111e0d4afea49cff5de95254dd90aa7d9ecc94ec4c16` | `ba011ce53f5f5f734d3a97043424fa7a1e81f6759f8387b61b55b052d5ab767f` |
| `../freezing1/Freezing1/UniformRootPair.lean` | 130 | `82cab43f9470f4e0665088ba8f162fb9ccd8155e1b46b7a6719910d60aac8ee4` | `75b51b7c8e89c3e374990af3e673a7d6f69b103027185015f0210e0bc445886d` |

Only additional local import edges are listed; all Mathlib imports are unchanged.

- `Freezing1.BirthTime`: `Freezing1.Path`.
- `Freezing1.HistoryProbability`: `Freezing1.Extinction`.
- `Freezing1.ReverseForest`: `Freezing1.RootedForestLaw`, `Freezing1.HistoryProbability`, `Freezing1.BirthTime`.
- `Freezing1.RootedForest`: no companion imports.
- `Freezing1.RootedForestLaw`: `Freezing1.RootedForest`, `Freezing1.UniformRootPair`.
- `Freezing1.UniformRootPair`: no companion imports.

## Edge-timestamp dependency extension

Copy time: `2026-10-29T12:52:10.198215+01:00` (`Europe/Paris`). The copying
agent added one module, `Freezing1.ReverseStampedForest`, containing 169
original source lines. The complete snapshot now comprises 23 modules and
4685 original source lines. Its only companion import is `Freezing1.ReverseForest`;
the already copied closure is unchanged.

| Original absolute source path | Lines | Original SHA-256 | Vendored SHA-256 |
| --- | ---: | --- | --- |
| `../freezing1/Freezing1/ReverseStampedForest.lean` | 169 | `7f18e235b648bb2add43c5f1e59e41bcc62b5860408571d62b20d480d076cd0c` | `ae4812b4bcc3cfeb507b930efc5f44e58cca5411cf914fa687a470bb38e2e0f9` |

The copying agent reports stable byte reads before and after copying, equality
of all eight existing closure modules after the documented transformation,
unchanged LICENSE/NOTICE/toolchain bytes, and identical manifest dependency
lists. A separate read by the provenance reviewer verified both hashes, the
169-line source count, stability on rereading, and exact equality after only
the import relocation and provenance comment. The companion manuscript hash
remains `88953dd87165a14b0e643c5b3d0075d8ce5ec39cdcfc0c25d313570fc3ab00df`.
No sibling edit or build was performed by either agent.

The new forest records the creation time on the child endpoint of each parent
edge. Joining the ordered roots at source step `i+1` writes timestamp `i+1`
on the second root; insertion writes zero on the new isolated root. The
uniform ordered-root-pair law and the sign-controlled transitions are lifted
without changing their probabilities. `map_transitionLaw`, `map_lawAfter`,
and `map_treeLaw` prove exact projection to the existing graph-valued reverse
laws, and projected validity and the terminal finite-tree property follow.
This is a concrete timestamped construction and projection theorem. It is
not a forward/reverse equality-in-law theorem, a history-fibre count, or a
proof of N01. The copying agent's focused check passed without warnings, and
the parent reported the destination build passed with exit 0, 3,861 jobs.
A fresh transitive axiom audit remains separate; earlier evidence does not
certify this extension.

## Timestamp-support dependency extension

Copy time: `2026-10-29T13:00:14.938278+01:00` (`Europe/Paris`). One additional
whole module, `Freezing1.ReverseTimestampSupport`, contains 322 original lines.
Its only companion import is `Freezing1.ReverseStampedForest`. The snapshot
now comprises 24 modules and 5007 original source lines.

| Original absolute source path | Lines | Original SHA-256 | Vendored SHA-256 |
| --- | ---: | --- | --- |
| `../freezing1/Freezing1/ReverseTimestampSupport.lean` | 322 | `eca2f2dbb9e598626c7f699ecddfb7ba29c4735efdb2f4faf0dd9ee0aea40013` | `c39f245963da94d130a8bf274eb322ff2b4e47906c75a54be4d270b440262a50` |

The copying agent read the complete module and verified source bytes before
and after copying, unchanged auxiliary/license/pin files, and exact equality
of all nine shared closure modules after the permitted transformation. The
provenance reviewer separately checked both hashes, line count, stable reread,
and that only import relocation and the same provenance comment differ.
Neither agent edited or built the sibling checkout.

The added results establish timestamp support and the canonical vertex
bijection required to compare reverse and forward labelled objects. They do
not prove equality of the forward and reverse laws. The copying agent's
focused check passed without warnings, and the parent subsequently reported a
successful destination build. The current transitive axiom audit remains
separate; N01 is still an independent mathematical obligation.
