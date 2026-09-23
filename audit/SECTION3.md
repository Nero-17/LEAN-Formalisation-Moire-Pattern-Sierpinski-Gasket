# Section 3 coverage — 2026-09-23

**Section 3 is not yet completely formalised. Section 2 remains complete.**

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

The main new implication concludes an upper box bound of log(9)/log(2)-2
for the actual set `shiftedIntersection gasket (rotation angle) 0`.
Its premise is exactly
`forall q > 1, lqDimension (differenceMeasure angle) q = 2`.
This premise must not be confused with a proved theorem.

The radius in the formal small-ball estimate is 4*2^(-n), using the
proved unit circumdisk bound for the gasket. This harmless larger radius
changes the covering constant, not the exponent. Symbolic prefixes are
counted separately even when geometric cells share boundary points.

## Still required for completion

1. The polygon-filling lemma and the exact support statement.
2. The two almost-everywhere exponential-separation lemmas, including
   quantitative angular sublevel estimates and directional resonances.
3. The Lq projection/reflection/convolution inequalities and ambient
   dimension bounds used in the argument.
4. The invoked self-similar Corso–Shmerkin result, and its application to
   prove full Lq dimension of the actual difference measure.
5. The final identification with twice the actual gasket Hausdorff
   dimension minus two, rather than just the explicit logarithmic value.

The Bernoulli address construction specifies the intended uniform gasket
measure; a separate self-similarity identity for that measure is also still
needed for the self-similar-measure theorem interface.

The external source is [Corso–Shmerkin, Corollary 4.2](https://arxiv.org/html/2409.04608v1#S4.SS2).
It was checked against the manuscript, but has not been converted into a
Lean proof or installed as an axiom. The old scalar `CorsoShmerkinInput`
in `MoireSection3.lean` remains a hypothesis-only interface and is not used
by the seven new modules.

## Verification

The seven new modules are listed in both `CheckLocal.ps1` and `lakefile.toml`.
Their final build is recorded in `section3-build-2026-09-23.txt`; the combined
Section 2 and Section 3 axiom audit is in `section3-axioms-2026-09-23.txt`.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
