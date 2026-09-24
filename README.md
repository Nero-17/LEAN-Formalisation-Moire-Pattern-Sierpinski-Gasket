# Lean formalisation of the Sierpiński-gasket moiré intersection

**Sections 2 and 3 are formalised. Section 3 uses five explicitly cited literature axioms; Section 2 uses only standard Lean axioms.**
The development uses the actual complex address-series gasket, actual live
relative-displacement states, and the adjacency matrix of Definition 2.2.
It contains 79 Lean modules, pinned to Lean and mathlib `v4.32.1`.

Repository: <https://github.com/Nero-17/LEAN-Formalisation-Moire-Pattern-Sierpinski-Gasket>
This public repository contains Lean code, English documentation and verification
records only. The manuscript and its translations are not distributed here.

## Section 2 entry points

| Manuscript result | Lean entry point |
| --- | --- |
| Lemma 2.1: nine-child intersection recursion | `MoireGeometry.gasket_intersection_recursion` |
| Definition 2.2: live deterministic subset-state graph | `MoireDeterminization` |
| Example 2.3: exact four states, transitions, matrix and spectrum at pi/3 | `MoirePiThirdGeometry`, `MoirePiThirdTable`, `MoirePiThirdSpectrum` |
| Theorem 2.4: Hausdorff and box dimensions at resonant angles | `MoireSection2Complete.resonant_dimensions` |
| Example 2.5: all three dimensions at pi/3 equal log(6)/log(4) | `MoireSection2Complete.piThird_dimensions` |
| Proposition 2.6: four equivalent resonance conditions | `MoireAngles`, `MoireSection2Results.resonant_iff_rotated_lattice_inclusion` |
| Theorem 2.7: finite type implies resonance | `MoireConcrete.finite_type_implies_commensurable` |
| Corollary 2.8: finite type iff resonance, countability and density | `MoireCharacterisation` |

The final theorem constructs the finite state space from the resonance
hypothesis. It does not assume a graph-directed dimension theorem, a
Frostman estimate, or the desired dimension formula.

## Dimension proof

The upper bound uses explicit finite covers, the equality between their
list lengths and matrix-power row sums, and Gelfand's formula. The lower
bound uses absolute values of a maximal-modulus eigenvector, a genuine
countably additive Markov path measure, proved cylinder probabilities,
deterministic blue labels, a geometric pushforward, and a uniform lattice
packing estimate. A proved mass-distribution argument gives the actual
mathlib Hausdorff dimension. Reachability transfers the lower bound to the
initial state; no irreducibility assumption is imposed.

`MoireBoxDimension` defines upper and lower box dimension by the usual
critical exponents of dyadic closed-ball covering growth. The definitions
quantify over actual finite lists of Euclidean centers, with positive
multiplicative constants and all sufficiently fine scales. They are not
scalar placeholders or definitions in terms of the adjacency matrix.
`MoireBoxEquality.box_dimensions_eq` proves equality of both dimensions.

See [audit/SECTION2.md](audit/SECTION2.md) for the detailed coverage and
[audit/section2-axioms-2026-09-23.txt](audit/section2-axioms-2026-09-23.txt)
for the current dependency audit.

## Section 3 and the literature boundary

`MoireSection3Complete.ae_upper_box_dimension` proves the actual
almost-everywhere upper box bound with no remaining analytic input parameter.
`ae_full_lq_dimension` gives full Lq dimension of the actual difference measure
for almost every angle, simultaneously for every q > 1.

The paper-specific proofs include the actual self-similar measure identities,
both separation lemmas and their projected-system applications, the
polygon-filling lemma and exact support, directional-resonance arithmetic,
and the covering argument. They contain no custom axioms or proof holes.

The final Section 3 theorem depends on five explicitly named axioms in
`MoireLiterature.lean`: planar and line ambient bounds, the line convolution
inequality, and the one-dimensional and planar uniform half-scale instances
of Corso–Shmerkin. Sources are Corso–Shmerkin (arXiv:2409.04608v1), Section 1.2
and Corollary 4.2, and Rossi–Shmerkin (arXiv:1812.05660v2), Section 1 and (1.2).
Compact full-mass sets and real-axis concentration are checked in Lean at
every application. These external results are trusted, not proved in Lean.

See [audit/LITERATURE.md](audit/LITERATURE.md) for exact source locations,
representation conventions and the complete trust boundary. The lower-bound
conjecture remains a conjecture.

Internal manuscript-review reports are excluded from this repository.

## Build and trust boundary

```powershell
lake exe cache get
lake build
lake env lean audit/ReviewAxioms.lean
```

With prebuilt dependency packages:

```powershell
./CheckLocal.ps1 -LeanExecutable '<toolchain>/bin/lean.exe' -DependencyRoot '<packages>'
./CheckLocal.ps1 -LeanExecutable '<toolchain>/bin/lean.exe' -DependencyRoot '<packages>' -Modules @('audit/ReviewAxioms')
```

The manifest pins mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`.
Finite certificates use kernel `decide`, not `native_decide`. Section 2 and the paper-specific proofs use only `propext`, `Classical.choice`, and `Quot.sound`. The final Section 3 entry point additionally uses exactly the five cited axioms in `MoireLiterature`. No `sorryAx` is permitted. Run `./audit/CheckAxioms.ps1` after the combined audit to check these per-theorem dependency boundaries.
