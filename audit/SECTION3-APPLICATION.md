# Section 3 application and geometry — 2026-09-24

The paper-specific Section 3 argument is now proved relative to explicitly
listed general analytic inputs. This is **not** an unconditional kernel proof
of the almost-everywhere upper bound: the `LiteratureInput` argument has not
been constructed or installed as a collection of external axioms.

## Newly checked results

| Manuscript content | Entry point |
| --- | --- |
| Splitting an independent Bernoulli address | `MoireBernoulliRecursion.prepend_law` |
| Three-map identity for the actual gasket probability measure | `MoireBernoulliRecursion.gasketMeasure_selfSimilar` |
| Nine-map identity for the actual difference measure | `MoireMeasureSimilarity.differenceMeasure_selfSimilar` |
| Linear images preserve the actual self-similar equation | `MoireMeasureSimilarity.mapped_gasket_selfSimilar` |
| Existing word centers agree with homogeneous-system cylinder sums | `MoireHomogeneousSystem.cylinderCenter_vertex`, `cylinderCenter_difference` |
| The actual difference system satisfies the general separation interface | `MoireHomogeneousSystem.difference_separation` |
| Both projected factors, including the reflected factor, satisfy the separation interface | `MoireProjectedSystems.projected_separation`, `reflected_separation` |
| Actual projected difference is the required convolution | `MoireProjectedSystems.projected_difference_convolution` |
| Projected difference has Lq dimension one, from general analytic inputs | `MoireLqApplication.projected_difference_full` |
| Difference measure has Lq dimension two, from those inputs | `MoireLqApplication.difference_full` |
| Almost-everywhere upper box bound, from those inputs | `MoireLqApplication.ae_upper_bound` |
| Directional resonance is equivalent to an extended rational slope | `MoireDirectionalArithmetic.directionallyResonant_iff_slope` |
| Directional resonances are countable and Lebesgue null | `MoireDirectionalResonance.countable_directionallyResonant`, `ae_not_directionallyResonant` |
| Pi/6 is directionally resonant but is not a resonant angle | `MoirePiSixthResonance.pi_sixth_directionallyResonant`, `pi_sixth_not_resonant` |
| Exact support of the actual gasket and difference measures | `MoireMeasureSupport.gasketMeasure_support`, `differenceMeasure_support` |
| The entire triangle perimeter belongs to the actual gasket | `MoireTriangleBoundary.boundary_subset_gasket` |
| Intersecting congruent triangles have a common boundary point | `MoirePolygonFilling.boundaries_meet` |
| Both polygon-filling identities | `MoirePolygonFilling.gasket_difference_eq_triangle_difference`, `negative_gasket_difference_eq` |
| Difference support is the triangle difference, is convex, and contains zero | `MoirePolygonFilling.differenceMeasure_support_polygon`, `support_convex`, `support_contains_zero` |

Compactness of the support is proved in
`MoireMeasureSupport.difference_support_compact`.

## Exact remaining analytic boundary

`MoireLqApplication.LiteratureInput` has five universally quantified fields.
None mentions a gasket, an angle, or an intersection:

1. Planar probability measures have Lq dimension at most two.
2. Probability measures concentrated on the real axis have Lq dimension at most one.
3. Convolution of two probability measures has Lq dimension at least that of either factor.
4. The uniform half-scale, one-dimensional specialisation of the Corso–Shmerkin formula,
   assuming exponential separation and Lq dimension less than one.
5. The uniform half-scale, planar specialisation of that formula, assuming exponential
   separation and unsaturation in every projection direction.

The formula fields correspond to [Corso–Shmerkin, arXiv:2409.04608,
Corollary 4.2](https://arxiv.org/html/2409.04608v1#S4.SS2).
Before providing a black-box implementation of the full record, precise source
attribution for the other three general facts must also be recorded. The user's
authorization permits documented literature black boxes; it does not itself
prove the five fields. No external axiom has been introduced in this change.

The original `analytic` premise about the particular difference measure has
been discharged **relative to these general inputs**. In particular, the code
checks both self-similar equations, the separation transfers, the real-axis
support conditions, the convolution identity, the unsaturation inequalities,
and both dimension-drop contradictions.

The real line is represented as the real axis in the complex plane. The dyadic
square definition then counts exactly the real dyadic intervals because all
mass has imaginary coordinate zero. A black-box implementation must respect
this representation and the actual `MoireLqDimension.lqDimension` definition.

## Proof choices

The reflected projected factor is treated directly as a separated three-map
self-similar measure. This avoids needing reflection invariance as an extra
analytic input.

For polygon filling, the Lean proof uses the triangle perimeter's connectedness
and the equal circumradius rather than equality of area. The sum of squared
norms of the three translated, rotated vertices is `3 + 3 * normSq shift`,
so they cannot all lie strictly inside the unit disk. The intermediate value
theorem then produces a common boundary point. The perimeter's inclusion in
the gasket follows from backward corner recursion and approximation by actual
gasket points. These are proved facts, not geometric axioms.

## Verification

The thirteen new modules are included in `CheckLocal.ps1` and `lakefile.toml`.
Build records are `section3-application-build-2026-09-24.txt` (twelve modules)
and `section3-pisixth-build-2026-09-24.txt` (the explanatory example).
The combined dependency audit is `section3-application-axioms-2026-09-24.txt`.
Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The analytic inputs remain theorem parameters and must be reported alongside
the axiom audit; a clean axiom list does not discharge those parameters.
