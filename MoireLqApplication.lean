import MoireCompactLaws
import MoireProjectedSystems
import MoireSection3GeometricResults

/-! The manuscript's application argument, separated from general analytic inputs.
`LiteratureInput` is a proposition, not an axiom or an asserted theorem.
The two formula fields are uniform half-scale specialisations of Corso--Shmerkin,
arXiv:2409.04608, Corollary 4.2. All five fields are supplied by the separately
documented external axioms in `MoireLiterature`; see `audit/LITERATURE.md`.
No field states a conclusion about a gasket or a moire intersection. -/
namespace MoireLqApplication

open MeasureTheory MoireGeometry MoireDifferenceMeasure MoireMeasureSimilarity
open MoireHomogeneousSystem MoireProjectedSystems MoireLqDimension
open MoireProjectionSeparation MoireAlmostEverySeparation MoireWordPacking
open MoireCompactLaws
open scoped ENNReal

structure LiteratureInput : Prop where
  planar_bound : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ] (q : ℝ),
    1 < q → CompactlySupported μ → lqDimension μ q ≤ 2
  line_bound : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ] (q : ℝ),
    1 < q → CompactlySupported μ → μ {point : ℂ | point.im = 0} = 1 → lqDimension μ q ≤ 1
  convolution_bound : ∀ (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (q : ℝ), 1 < q → CompactlySupported μ → CompactlySupported ν →
    μ {point : ℂ | point.im = 0} = 1 → ν {point : ℂ | point.im = 0} = 1 →
    max (lqDimension μ q) (lqDimension ν q) ≤ lqDimension (μ.conv ν) q
  line_formula : ∀ {α : Type} [Fintype α] (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (vertices : α → ℂ) (q : ℝ), 0 < Fintype.card α → 1 < q → CompactlySupported μ →
    (∀ digit, (vertices digit).im = 0) → μ {point : ℂ | point.im = 0} = 1 →
    UniformSelfSimilar μ vertices → ExponentialSeparation vertices → lqDimension μ q < 1 →
    lqDimension μ q = Real.log (Fintype.card α) / Real.log 2
  planar_formula : ∀ {α : Type} [Fintype α] (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (vertices : α → ℂ) (q : ℝ), 0 < Fintype.card α → 1 < q → CompactlySupported μ →
    UniformSelfSimilar μ vertices → ExponentialSeparation vertices →
    (∀ direction : ℂ, ‖direction‖ = 1 →
      lqDimension μ q - 1 < lqDimension (projectedMeasure direction μ) q) →
    lqDimension μ q = Real.log (Fintype.card α) / Real.log 2

theorem log_three_ratio_gt_one : 1 < Real.log 3 / Real.log 2 := by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num))).mpr
  simpa using Real.strictMonoOn_log (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (3 : ℝ) ∈ Set.Ioi 0) (by norm_num : (2 : ℝ) < 3)

theorem mapped_gasket_full_line (literature : LiteratureInput) (linear : ℂ →L[ℝ] ℂ)
    (real_image : ∀ point, (linear point).im = 0)
    (separated : ExponentialSeparation (fun digit => linear (vertex digit)))
    (q : ℝ) (q_gt_one : 1 < q) : lqDimension (gasketMeasure.map linear) q = 1 := by
  letI : IsProbabilityMeasure (gasketMeasure.map linear) :=
    Measure.isProbabilityMeasure_map linear.measurable.aemeasurable
  have real_mass := map_real_mass linear real_image
  have upper := literature.line_bound _ q q_gt_one (mapped_gasket_compact linear) real_mass
  apply le_antisymm upper
  by_contra lower
  have below : lqDimension (gasketMeasure.map linear) q < 1 := lt_of_not_ge lower
  have formula := literature.line_formula (gasketMeasure.map linear)
    (fun digit => linear (vertex digit)) q (by simp) q_gt_one
    (mapped_gasket_compact linear)
    (fun digit => real_image _) real_mass (mapped_selfSimilar linear) separated below
  simp only [Fintype.card_fin] at formula
  rw [formula] at below
  linarith [log_three_ratio_gt_one]

theorem projected_difference_full (literature : LiteratureInput) (angle : ℝ)
    (direction : ℂ)
    (separated : ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction)
    (q : ℝ) (q_gt_one : 1 < q) :
    lqDimension (projectedMeasure direction (differenceMeasure angle)) q = 1 := by
  have real_mass : projectedMeasure direction (differenceMeasure angle)
      {point : ℂ | point.im = 0} = 1 := by
    unfold projectedMeasure
    rw [Measure.map_apply (projectionMap direction).measurable (by measurability)]
    have preimage : projectionMap direction ⁻¹' {point : ℂ | point.im = 0} = Set.univ := by
      ext point; simp [projectionMap]
    rw [preimage, measure_univ]
  apply le_antisymm (literature.line_bound _ q q_gt_one (projected_difference_compact angle direction) real_mass)
  letI : IsProbabilityMeasure (gasketMeasure.map (projectionMap direction)) :=
    Measure.isProbabilityMeasure_map (projectionMap direction).measurable.aemeasurable
  letI : IsProbabilityMeasure (gasketMeasure.map (reflectedProjection angle direction)) :=
    Measure.isProbabilityMeasure_map (reflectedProjection angle direction).measurable.aemeasurable
  rw [projected_difference_convolution]
  have convolution := literature.convolution_bound
    (gasketMeasure.map (projectionMap direction))
    (gasketMeasure.map (reflectedProjection angle direction)) q q_gt_one
    (mapped_gasket_compact _) (mapped_gasket_compact _)
    (map_real_mass _ (projection_real direction))
    (map_real_mass _ (reflected_real angle direction))
  rcases separated with blue | red
  · have full := mapped_gasket_full_line literature (projectionMap direction)
      (projection_real direction) (projected_separation direction blue) q q_gt_one
    exact full ▸ (le_max_left _ _).trans convolution
  · have full := mapped_gasket_full_line literature (reflectedProjection angle direction)
      (reflected_real angle direction) (reflected_separation angle direction red) q q_gt_one
    exact full ▸ (le_max_right _ _).trans convolution

theorem difference_full (literature : LiteratureInput) (angle : ℝ)
    (separated : DifferenceExponentiallySeparated angle)
    (projections : ∀ direction : ℂ, ‖direction‖ = 1 →
      ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction)
    (q : ℝ) (q_gt_one : 1 < q) : lqDimension (differenceMeasure angle) q = 2 := by
  apply le_antisymm (literature.planar_bound _ q q_gt_one (difference_compact angle))
  by_contra lower
  have below : lqDimension (differenceMeasure angle) q < 2 := lt_of_not_ge lower
  have unsaturated : ∀ direction : ℂ, ‖direction‖ = 1 →
      lqDimension (differenceMeasure angle) q - 1 <
        lqDimension (projectedMeasure direction (differenceMeasure angle)) q := by
    intro direction unit
    rw [projected_difference_full literature angle direction (projections direction unit) q q_gt_one]
    linarith
  have formula := literature.planar_formula (differenceMeasure angle)
    (fun digit : Fin 3 × Fin 3 => vertex digit.1 - rotation angle (vertex digit.2)) q
    (by simp) q_gt_one (difference_compact angle) (difference_selfSimilar angle)
    (difference_separation angle separated) unsaturated
  have logarithm : Real.log 9 = 2 * Real.log 3 := by
    calc
      Real.log 9 = Real.log ((3 : ℝ) ^ 2) := congrArg Real.log (by norm_num)
      _ = _ := Real.log_pow (3 : ℝ) 2
  norm_num only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at formula
  norm_num only [show (3 : ℝ) * 3 = 9 by norm_num] at formula
  rw [formula, logarithm, mul_div_assoc] at below
  linarith [log_three_ratio_gt_one]

/-- The entire main-theorem application is proved relative only to general analytic inputs. -/
theorem ae_upper_bound (literature : LiteratureInput) :
    ∀ᵐ angle : ℝ,
      MoireBoxDimension.upperBoxDimension (MoireSection2.shiftedIntersection gasket (rotation angle) 0) ≤
        ENNReal.ofReal (2 * (dimH gasket).toReal - 2) := by
  apply MoireSection3GeometricResults.ae_upper_bound_of_analytic_input
  exact difference_full literature

end MoireLqApplication
