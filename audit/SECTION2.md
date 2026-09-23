# Section 2 coverage, 2026-09-23

This update is not a complete formalisation of Section 2. All new theorems use
the existing complex address-series gasket and Eisenstein field; no new
mathematical axioms or theorem-sized dimension hypotheses are introduced.

| Manuscript item | Checked coverage | Remaining work |
| --- | --- | --- |
| Lemma 2.1 | `MoireGeometry.gasket_intersection_recursion` | None for the stated set recursion |
| Definition 2.2 | `MoireDeterminization`: finite-set states, live successors, one edge per blue label, adjacency matrix, actual union recursion | None for these definitions |
| Example 2.3 | `liveReachable_piThird_eq`, `geometric_table`, `reachableState_iff`, `adjacency_eq`, `geometric_matrix_spectral_radius` | None for the live-state table and spectral-radius calculation |
| Theorem 2.4 | Actual finite graph; compact nonempty state sets; open set condition; similarities; infinite-path coding; spectral weights; finite-product weight bound; an actual path probability measure | Probability cylinder estimates and geometric mass bound; spectral covering growth; Hausdorff and box dimension formula |
| Example 2.5 | Actual geometric matrix has spectral radius sqrt(6) | Actual dimension conclusion depends on Theorem 2.4 |
| Proposition 2.6 | Field iff rational half-angle; field iff coprime integer parametrisation; field iff rotated-lattice inclusion | None for the four stated characterisations on [0, pi/3] |
| Theorem 2.7 | `MoireConcrete.finite_type_implies_commensurable` | None with the theorem's explicit nonempty-intersection hypothesis |
| Corollary 2.8 | `MoireCharacterisation.finite_type_iff_resonant`, `finite_type_angles_countable`, `closure_finite_type_angles`; initial nonemptiness is proved internally | None for the stated equivalence, countability and density |

The lattice inclusion uses a positive integer `q : ℤ`, matching the positive
integer quantifier in the manuscript. The angle parametrisation uses integer
`IsCoprime`. The finite-state theorem does not assume a finite state space: it
derives one from a common integer denominator and the actual gasket norm bound.

`dimH_shiftedIntersection_recursion` is an identity for mathlib's actual
Hausdorff dimension. It is not a proof of the spectral-radius formula.

Run `CheckLocal.ps1` with its default module list, followed by
`-Modules @('audit/ReviewAxioms')` in the same dependency environment.
See `section2-axioms-2026-09-23.txt` for the current dependency audit.

`MoirePiThirdTable.geometric_matrix_spectral_radius` explicitly instantiates
the matrix algebra: it is not the spectrum of pointwise multiplication on
functions. `stateEquiv` proves that the displayed four-state indexing is a
bijection with all states reachable in Definition 2.2.

The new probability measure is a genuine mathlib measure. However, merely
constructing it does not prove the geometric mass bound or the dimension
formula. No statement here assumes the graph-directed dimension theorem as
an axiom or replaces Hausdorff dimension with a symbolic scalar.
