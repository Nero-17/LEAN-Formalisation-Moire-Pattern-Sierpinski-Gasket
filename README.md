# Lean formalisation of the Sierpiński-gasket moiré intersection

**Section 2 is formalised. The rest of the paper is not fully formalised.**
The development uses the actual complex address-series gasket, actual live
relative-displacement states, and the adjacency matrix of Definition 2.2.
It contains 47 Lean modules, pinned to Lean and mathlib `v4.32.1`.

Repository: <https://github.com/Nero-17/LEAN-Formalisation-Moire-Pattern-Sierpinski-Gasket>
(private).

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

## Remaining scope outside Section 2

The Section 3 almost-everywhere upper bound remains incomplete. Existing
files contain generic Borel–Cantelli and counting arguments, but the actual
difference measure, its Lq-dimension estimates, the relevant analytic
results and their geometric application are not all formalised. The final
non-resonant dimension statement remains a conjecture.

The historical audit files describe manuscript revision `f88d4e4`, including
false assertions later removed from the English manuscript. They are retained
as historical records, not as current Section 2 coverage reports.

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
Finite certificates use kernel `decide`, not `native_decide`. The final
theorems' axiom dependencies must be confined to `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom axioms.
