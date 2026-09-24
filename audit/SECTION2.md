# Section 2 coverage — 2026-09-23

Section 2 is formalised for the actual gasket and graph in the English
manuscript. The main entry point is `MoireSection2Complete.lean`.
This does not assert completion of Section 3 or the rest of the paper.

| Manuscript item | Verified entry point | Remaining Section 2 work |
| --- | --- | --- |
| Lemma 2.1 | `MoireGeometry.gasket_intersection_recursion` | None |
| Definition 2.2 | `MoireDeterminization`: actual live subset states, deterministic labelled edges and adjacency matrix | None |
| Example 2.3 | `liveReachable_piThird_eq`, `reachableState_iff`, `geometric_table`, `adjacency_eq`, `piThird_actual_spectral_radius` | None |
| Theorem 2.4 | `MoireSection2Complete.resonant_dimensions` | None |
| Example 2.5 | `MoireSection2Complete.piThird_dimensions` | None |
| Proposition 2.6 | `MoireAngles` and `resonant_iff_rotated_lattice_inclusion` | None |
| Theorem 2.7 | `MoireConcrete.finite_type_implies_commensurable` | None |
| Corollary 2.8 | `finite_type_iff_resonant`, `finite_type_angles_countable`, `closure_finite_type_angles` | None |

The main theorem assumes exactly an angle in [0, pi/3] and membership of
exp(i theta) in Q(omega). Resonance supplies a finite state type internally.
Initial nonemptiness is proved, rather than retained as an additional
assumption of the main dimension theorem or Corollary 2.8.

## Proof interfaces

- `MoireGraphCovers`, `MoireSpectralGrowth`, `MoireHausdorffUpper`,
  `MoireActualUpper`: explicit geometric covers, matrix-power counting,
  spectral growth and actual Hausdorff upper bounds.
- `MoirePathCylinders`, `MoirePathSupport`, `MoireLabelledMeasure`,
  `MoireDeterministicPaths`, `MoireGeometricMeasure`: actual cylinder
  probabilities, almost-sure legal paths, parallel-edge labels, and a
  probability measure supported on the represented geometric intersection.
- `MoirePrefixGeometry`, `MoireWordPacking`, `MoireSmallBalls`,
  `MoireSpectralMass`: exact prefix lattice coordinates, a uniform packing
  bound, and spectral decay of Euclidean small-ball mass.
- `MoireMassDistribution`, `MoireHausdorffLower`,
  `MoireHausdorffEquality`: mass distribution including diameter-zero sets,
  actual Hausdorff lower bounds and the complete Hausdorff equality.
- `MoireBoxDimension`, `MoireBoxBounds`, `MoireBoxSimilarity`,
  `MoireBoxEquality`: upper/lower dyadic covering-growth dimensions,
  covering estimates, similarity and reachability transfer, and equality.
- `MoireSection2Complete`: the final resonance theorem, invariant matrix
  spectral radius under the pi/3 state reindexing, and its dimension example.

The box dimensions are defined via genuine Euclidean closed-ball covers:
upper exponents permit covers with O(2^(n s)) centers; lower exponents require
all covers to have at least a positive constant times 2^(n s) centers, at
all sufficiently fine dyadic scales. Their critical exponents are proved
equal. No dimension is defined using the spectral formula itself.

The lower-bound argument does not invoke an unproved graph-directed dimension
theorem. It uses spectral subeigenweights and a Markov measure, and allows
reducible graphs. A state carrying a positive spectral weight is reachable
from the initial state, which transfers both lower bounds to that state.

## Verification

`CheckLocal.ps1` and `lakefile.toml` list all 47 modules in dependency order.
The final full rebuild is recorded in `section2-full-build-2026-09-23.txt`.
`ReviewAxioms.lean` includes both final theorems; its output is recorded in
`section2-axioms-2026-09-23.txt`. Only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

This report describes the completed Section 2 development. Internal manuscript
reviews of earlier revisions are not distributed in this repository.
