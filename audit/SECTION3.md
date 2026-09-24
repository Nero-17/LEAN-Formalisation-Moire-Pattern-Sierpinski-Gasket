> **Historical development record. Superseded by [LITERATURE.md](LITERATURE.md): all five inputs are now supplied as cited external axioms, and `MoireSection3Complete.ae_upper_box_dimension` has no remaining analytic parameter. Earlier standard-only audit claims below refer to the pre-integration revision.**

# Section 3 coverage — 2026-09-23

**Updated 2026-09-24: the paper-specific Section 3 argument is proved relative to general analytic inputs. Section 2 remains complete.**

See [SECTION3-APPLICATION.md](SECTION3-APPLICATION.md) for the new results and precise remaining literature interface. The earlier development below is retained as verification history.

The new development proves the geometric conclusion from an explicit
full-Lq-dimension hypothesis for the actual difference measure. It does
not prove that hypothesis for almost every angle.

## Verified objects and implications

| Manuscript step | Verified entry point |
| --- | --- |
| Independent uniform symbolic addresses | `MoireDifferenceMeasure.singleAddressMeasure`, `addressMeasure` |
| Uniform gasket law and difference law | `gasketMeasure`, `differenceMeasure`, `differenceMeasure_eq_product_law` |
| Difference measure is the stated convolution | `MoireDifferenceLaw.differenceMeasure_eq_convolution` |
| Gasket law has total mass one on the gasket | `MoireDifferenceLaw.gasketMeasure_gasket` |
| Every prescribed pair of n-prefixes has probability 9^(-n) | `MoireDifferenceMeasure.prefix_probability` |
| Unions of prefix events have exactly their counted probability | `prefix_event_probability` |
| Actual intersecting cylinder pairs and their number Q_n | `MoireIntersectionCounting.Intersects`, `intersectionCount` |
| Q_n / 9^n is bounded by a small-ball mass | `count_le_small_ball` |
| Q_n centers cover the actual intersection | `intersectionCenters_cover`, `intersectionCenters_length` |
| Genuine half-open dyadic squares and their q-moment | `MoireDyadicConcentration.dyadicCell`, `dyadicMoment` |
| Dyadic moment is positive and at most one for q >= 1 | `dyadicMoment_pos`, `dyadicMoment_le_one` |
| Small ball is covered by 81 dyadic squares | `small_ball_covered` |
| Small-ball mass is at most 81 times the q-moment's 1/q power | `small_ball_mass_le_moment` |
| Lq dimension is the lower limit of normalized logarithmic q-moments | `MoireLqDimension.lqDimension` |
| Below the lower limit, moment decay holds at every sufficiently fine scale | `eventually_moment_le_exp` |
| The resulting small-ball estimate | `eventually_ball_mass_le_exp` |
| Full Lq dimensions imply the actual upper box bound | `MoireUpperFromLq.upperBox_le_of_full_lq` |
| Almost-everywhere version, with the same explicit analytic hypothesis | `ae_upperBox_le_of_ae_full_lq` |
| Minimum nonzero Eisenstein-lattice norm is one | `MoireSeparationGeometry.one_le_norm_lattice` |
| Determinant controlled by the two directional projections | `determinant_le_projections` |
| Uniform Lebesgue measure bound for small sine values | `MoireAngularSublevel.sine_sublevel_volume` |
| Actual angular determinant sublevel bound | `MoireDeterminantSublevel.determinant_sublevel_volume` |
| Summable bad-scale estimates and almost-everywhere determinant separation | `MoireAlmostEveryProjection.ae_determinant_bound` |
| Almost-everywhere separation of the nine-map difference system, on all real angles | `MoireSeparationPeriodicity.ae_difference_exponential_separation` |
| Almost-everywhere projected-factor dichotomy, simultaneously for all unit directions | `MoireSeparationPeriodicity.ae_projection_dichotomy` |
| Actual gasket Hausdorff dimension is log(3)/log(2) | `MoireGasketDimension.gasket_dimH` |
| Conditional upper bound in terms of the actual gasket Hausdorff dimension | `MoireSection3GeometricResults.upperBox_le_codimension_of_full_lq` |

The main new implication concludes an upper box bound of log(9)/log(2)-2
for the actual set `shiftedIntersection gasket (rotation angle) 0`.
Its premise is exactly
`forall q > 1, lqDimension (differenceMeasure angle) q = 2`.
This premise must not be confused with a proved theorem.

The radius in the formal small-ball estimate is 4*2^(-n), using the
proved unit circumdisk bound for the gasket. This harmless larger radius
changes the covering constant, not the exponent. Symbolic prefixes are
counted separately even when geometric cells share boundary points.

The separation proof uses a deliberately less sharp exponential constant
than the manuscript. There are at most 81^n quadruples of length-n words.
The determinant bad-event estimate costs at most 9*pi*(81/128)^n in
Lebesgue measure, which is summable. Almost every angle eventually has
all nonzero paired cylinder determinants at least (1/512)^n. This gives
exponential separation with rate 1/4096. Zeros are included in the bad
events, so a separate directional-resonance exclusion is not needed for
these two lemmas. Periodicity then gives the statements on all of R.

`MoireSection3GeometricResults.ae_upper_bound_of_analytic_input` combines
the two proved separation lemmas and the proved geometric dimension
deduction. Its explicit `analytic` premise is still unproved; the theorem
must not be described as the unconditional main result.

## Remaining external inputs (updated 2026-09-24)

The polygon-filling lemma, exact support, directional-resonance arithmetic,
self-similar measure equations and the paper-specific analytic application
have now been proved. The earlier `analytic` premise is discharged relative
to `MoireLqApplication.LiteratureInput`, which contains five general Lq facts.
The record still needs a documented literature-backed implementation; it is
not an axiom and has not been inhabited. See SECTION3-APPLICATION.md.

## Verification

The seven new modules are listed in both `CheckLocal.ps1` and `lakefile.toml`.
Their final build is recorded in `section3-build-2026-09-23.txt`; the combined
Section 2 and Section 3 axiom audit is in `section3-axioms-2026-09-23.txt`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

The subsequent nine separation/dimension modules are rebuilt in
`section3-separation-build-2026-09-23.txt`. Their combined axiom audit,
including the previously verified results, is recorded in
`section3-separation-axioms-2026-09-23.txt`. The project now contains
63 modules. Earlier build logs are retained as historical verification.
