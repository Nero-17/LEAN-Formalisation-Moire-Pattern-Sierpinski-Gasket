# Lean formalization: verified components and manuscript obstructions

**This is a partial formalization, not a complete verification of Sections 2
and 3 or of the paper.** The two principal dimension theorems still lack
complete formal proofs. The repository contains twenty-six Lean modules, pinned
dependencies, build instructions and the historical audit records.

Repository: <https://github.com/Nero-17/LEAN-Formalisation-Moire-Pattern-Sierpinski-Gasket>
(private at the time of upload).

The historical audit concerns manuscript commit `f88d4e4`. It identified false
assertions, including an unlabelled survivor-count identity and an unrestricted
endpoint Mattila theorem. Those statements and other unsupported lower-bound
claims were removed in the subsequent English manuscript revision `f884f00`.
The audit files are retained as a record of what was checked at that earlier
revision; deleting a false manuscript claim does not fill the remaining Lean
proof gaps.

A theorem-sized analytic assumption is not an established result simply
because Lean accepts an implication taking it as input. See
[the audit summary](audit/STATUS.md), [independent review](audit/REVIEW.md),
and [external-source audit](audit/EVIDENCE.md).

## Concrete mathematical coverage

| File | Established content | Scope limit |
| --- | --- | --- |
| `MoireGeometry.lean` | Concrete complex vertices; convergent infinite address sums defining the gasket; self-similarity proved from that definition; actual rotations; Lemma 2.1 | No dimension formula |
| `MoireLatticeWords.lean` | Injectivity on all finite words, including different lengths; path construction; finite-live-reachable converse | Generic coordinate embedding and self-similar set |
| `MoireEisenstein.lean` | Concrete omega equals exp((2*pi/3)*I); injective integer coordinates; exact Z[omega] and Q(omega) | Integrated with the gasket in `MoireConcrete` |
| `MoireConcrete.lean` | Actual gasket finite-type converse; actual zero-fibre Hausdorff dimension; actual first-level intersection count 9 versus 7 distinct legal displacements at zero angle | Neither principal dimension theorem |
| `MoireEndpoint.lean` | Convex backward step; endpoint iff all prefixes legal | Convexity and negative-digit membership explicit; filling lemma missing |
| `MoireFibre.lean` | Equality of actual mathlib Hausdorff dimensions of zero fibre and intersection | Maximum product metric; no box-dimension development |
| `MoireCounting.lean` | Labelled/unlabelled certificates; closed forms and alternating ratios for a specified two-step graph-count recurrence | Recurrence not identified in Lean with actual geometric Q_n(pi/3) |
| `MoireSection2.lean` | Generic displacement algebra, set recursion, repetition, exact four-carry transition checks | Candidate carries not proved exactly live geometric carries |
| `MoireSection3.lean` | Generic union bounds and Borel–Cantelli, labelled counting/probability identity, scalar implications and error removal | Lq and box dimensions are scalar parameters; actual analytic theorem not instantiated |
| `MoireAngles.lean` | Concrete Eisenstein-field, rational half-angle, and coprime integer parametrisation equivalences on [0, pi/3] | Density is supplied in `MoireDensity` |
| `MoireDimension.lean` | Actual gasket norm bound, compactness, corner similarities, and Hausdorff-dimension recursion | No spectral-radius dimension formula |
| `MoireFiniteType.lean` | Integer denominator clearing, finite bounded lattice sets, resonant forward finiteness, finite-type iff resonant for a nonempty initial intersection | Nonemptiness remains an explicit hypothesis in the iff |
| `MoireDeterminization.lean` | Live subset states, deterministic blue-labelled transitions, adjacency definition, actual set recursion, and finite reachable graph | Exact pi/3 enumeration is supplied in `MoirePiThirdTable` |
| `MoireSection2Results.lean` | Original rotated-lattice inclusion, finite deterministic graph at resonant angles, countability of resonant angles | Does not assert completion of Section 2 |
| `MoireDensity.lean`, `MoireNonempty.lean`, `MoireCharacterisation.lean` | Density including interval endpoints; triangle edges in the actual gasket; explicit common point at every angle in [0, pi/3]; complete finite-type/resonance equivalence, countability and density | Corollary 2.8 has no unproved nonemptiness premise |
| `MoireTriangle.lean`, `MoireTriangleBounds.lean`, `MoireGraphGeometry.lean` | Barycentric geometry; actual gasket containment; compact nonempty state sets; open set condition for distinct actual graph edges | No dimension formula follows from these lemmas alone |
| `MoirePiThirdGeometry.lean`, `MoirePiThirdTable.lean`, `MoirePiThirdSpectrum.lean` | Exact actual live reachable displacements; all four states and all transitions; original adjacency matrix after explicit state reindexing; complex spectrum and spectral radius sqrt(6) | The dimension conclusion still depends on Theorem 2.4 |
| `MoireSpectralWeights.lean` | Nonnegative weights from a maximal-modulus complex eigenvector; normalized outgoing rows; finite-product path weight bound | Not a Hausdorff measure estimate |
| `MoirePathMeasure.lean`, `MoireGraphCoding.lean` | Actual countably additive probability measure on infinite state paths; every legal infinite geometric path codes a point of the represented gasket intersection | Probability cylinder bounds, geometric pushforward estimates and dimension conclusions remain to be connected |

`MoireConcrete.finite_type_implies_commensurable` has the paper's structural
hypotheses: nonempty initial intersection and finitely many actual live
reachable displacements. Self-similarity, coordinate injectivity, repetition,
and the nonzero denominator are proved internally.

`MoireConcrete.manuscript_unlabelled_count_is_false` uses **actual gasket set
intersections**. Each first-level pair meets at a midpoint of vertices, giving
9 pairs. There are 7 distinct differences, all in the actual difference set.
Retaining ordered digit-pair labels, or multiplicities, repairs this error.

## Missing mathematics

- Theorem 2.4's graph-directed Hausdorff formula and matching box dimension,
  hence Example 2.5. This needs the probability/cylinder and geometric mass
  estimates, spectral covering growth and a genuine box-dimension development.
- The filling lemma for rotated gasket difference sets.
- Actual uniform gasket and difference measures, Lq dimensions, separation
  estimates, directional dichotomy, convolution inequalities, and the
  Corso–Shmerkin theorem underlying the a.e. upper bound.
- Covering/count comparisons and the analytic arguments needed for a matching
  lower bound. The old Mattila statement and Frostman transfer certificate
  discussed in the historical audit are no longer asserted in Section 4.
- Numerical tables are not proof certificates. The final non-resonant
  dimension statement remains a **conjecture**, as in the manuscript.

## Build and trust boundary

Pinned versions: Lean and mathlib `v4.32.1` (committed manifest).

```powershell
lake exe cache get
lake build
lake env lean audit/ReviewAxioms.lean
```

With prebuilt dependency packages, avoid redownloading via:

```powershell
./CheckLocal.ps1 -LeanExecutable '<toolchain>/bin/lean.exe' -DependencyRoot '<packages>'
```

Each dependency directory (`mathlib`, `batteries`, etc.) must contain its
`.lake/build/lib/lean` artifacts. Build or fetch missing dependencies first.

Finite certificates use kernel `decide`, not `native_decide`. Representative
dependency closures are checked by `audit/ReviewAxioms.lean`; standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted. There must
be no `sorryAx`, custom mathematical axioms, or native-decision axioms.
Clean axiom checks do **not** establish full manuscript coverage.

The fresh upload build and axiom checks are documented in
[audit/UPLOAD.md](audit/UPLOAD.md), separately from the historical audit.

The subsequent Section 2 additions and their remaining gaps are listed in
[audit/SECTION2.md](audit/SECTION2.md).
