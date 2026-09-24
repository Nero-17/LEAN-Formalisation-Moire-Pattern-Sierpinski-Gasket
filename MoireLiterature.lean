import MoireLqApplication

/-!
# Explicitly trusted literature results

These five declarations are external axioms, authorized by the author. They are
NOT kernel proofs of the cited results. The specialisation/representation audit
and source locations are recorded in `audit/LITERATURE.md`.

CS: Corso--Shmerkin, arXiv:2409.04608v1, https://arxiv.org/html/2409.04608v1
RS: Rossi--Shmerkin, arXiv:1812.05660v2, https://arxiv.org/pdf/1812.05660v2

Every declaration concerns general measures. No gasket-specific conclusion is
assumed here; those applications are proved in `MoireLqApplication`.
-/
namespace MoireLiterature
open MeasureTheory MoireLqDimension MoireHomogeneousSystem MoireMeasureSimilarity MoireCompactLaws

/-- CS Section 1.2, inequality (1.2), with the rescaling invariance stated in
Section 2.2. The half-open dyadic square convention agrees with our definition. -/
axiom planar_ambient_bound (μ : Measure ℂ) [IsProbabilityMeasure μ] (q : ℝ)
    (q_gt_one : 1 < q) (compact : CompactlySupported μ) : lqDimension μ q ≤ 2

/-- RS Section 1, p. 2, the dimension range immediately before equation (1.1).
The real line is represented as the real axis, which has exactly the same dyadic moments. -/
axiom line_ambient_bound (μ : Measure ℂ) [IsProbabilityMeasure μ] (q : ℝ)
    (q_gt_one : 1 < q) (compact : CompactlySupported μ)
    (real_mass : μ {point : ℂ | point.im = 0} = 1) : lqDimension μ q ≤ 1

/-- RS Section 1, equation (1.2), for compactly supported probability measures on
the line. Commutativity gives the maximum of the two factor dimensions. -/
axiom line_convolution_bound (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (q : ℝ) (q_gt_one : 1 < q)
    (compact_μ : CompactlySupported μ) (compact_ν : CompactlySupported ν)
    (real_μ : μ {point : ℂ | point.im = 0} = 1)
    (real_ν : ν {point : ℂ | point.im = 0} = 1) :
    max (lqDimension μ q) (lqDimension ν q) ≤ lqDimension (μ.conv ν) q

/-- CS Corollary 4.2, d=1, lambda=1/2, uniform positive weights.
In dimension one, unsaturation is Dq < 1. See audit/LITERATURE.md for the
uniform-weight formula and the real-axis representation. -/
axiom corso_shmerkin_line {α : Type} [Fintype α]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (vertices : α → ℂ) (q : ℝ)
    (nonempty : 0 < Fintype.card α) (q_gt_one : 1 < q) (compact : CompactlySupported μ)
    (real_vertices : ∀ digit, (vertices digit).im = 0)
    (real_mass : μ {point : ℂ | point.im = 0} = 1)
    (self_similar : UniformSelfSimilar μ vertices) (separated : ExponentialSeparation vertices)
    (unsaturated : lqDimension μ q < 1) :
    lqDimension μ q = Real.log (Fintype.card α) / Real.log 2

/-- CS Corollary 4.2, d=2, lambda=1/2, uniform positive weights.
Unit directions enumerate all one-dimensional orthogonal projections. -/
axiom corso_shmerkin_plane {α : Type} [Fintype α]
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (vertices : α → ℂ) (q : ℝ)
    (nonempty : 0 < Fintype.card α) (q_gt_one : 1 < q) (compact : CompactlySupported μ)
    (self_similar : UniformSelfSimilar μ vertices) (separated : ExponentialSeparation vertices)
    (unsaturated : ∀ direction : ℂ, ‖direction‖ = 1 →
      lqDimension μ q - 1 < lqDimension (projectedMeasure direction μ) q) :
    lqDimension μ q = Real.log (Fintype.card α) / Real.log 2

/-- All five application inputs are now supplied by separately named literature axioms. -/
def inputs : MoireLqApplication.LiteratureInput where
  planar_bound := planar_ambient_bound
  line_bound := line_ambient_bound
  convolution_bound := line_convolution_bound
  line_formula := corso_shmerkin_line
  planar_formula := corso_shmerkin_plane

end MoireLiterature
