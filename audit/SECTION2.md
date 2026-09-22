# Section 2 coverage, 2026-09-22

This update is not a complete formalisation of Section 2. All new theorems use
the existing complex address-series gasket and Eisenstein field; no new
mathematical axioms or theorem-sized dimension hypotheses are introduced.

| Manuscript item | Checked coverage | Remaining work |
| --- | --- | --- |
| Lemma 2.1 | `MoireGeometry.gasket_intersection_recursion` | None for the stated set recursion |
| Definition 2.2 | `MoireDeterminization`: finite-set states, live successors, one edge per blue label, adjacency matrix, actual union recursion | None for these definitions; examples require additional geometry |
| Example 2.3 | Earlier candidate-displacement transition checks | Prove the candidates are the exact live geometric states and verify the spectral radius |
| Theorem 2.4 | `resonant_reachable_states_finite`; compactness and actual Hausdorff-dimension recursion | Open set condition, spectral growth, Hausdorff and box dimension formula |
| Example 2.5 | None beyond auxiliary arithmetic/counting | Actual dimension conclusion depends on Theorem 2.4 |
| Proposition 2.6 | Field iff rational half-angle; field iff coprime integer parametrisation; field iff rotated-lattice inclusion | None for the four stated characterisations on [0, pi/3] |
| Theorem 2.7 | `MoireConcrete.finite_type_implies_commensurable` | None with the theorem's explicit nonempty-intersection hypothesis |
| Corollary 2.8 | Resonant forward finiteness; iff with nonempty initial intersection; countability | Remove nonemptiness hypothesis by proving the geometry; density |

The lattice inclusion uses a positive integer `q : ℤ`, matching the positive
integer quantifier in the manuscript. The angle parametrisation uses integer
`IsCoprime`. The finite-state theorem does not assume a finite state space: it
derives one from a common integer denominator and the actual gasket norm bound.

`dimH_shiftedIntersection_recursion` is an identity for mathlib's actual
Hausdorff dimension. It is not a proof of the spectral-radius formula.

Reproduce the new checks using `CheckLocal.ps1` with modules `MoireAngles`,
`MoireDimension`, `MoireFiniteType`, `MoireDeterminization`, and
`MoireSection2Results`, followed by `audit/ReviewAxioms.lean` in the same Lean
environment. See `section2-axioms.txt` for the dependency audit.
