import MoireLiterature
import MoirePolygonFilling
import MoirePiSixthResonance

/-! Section 3 entry points with no remaining analytic theorem parameters.
The main theorem depends on the five explicitly cited axioms in MoireLiterature.
Its dependency audit must not be described as standard-axiom-only verification. -/
namespace MoireSection3Complete
open MeasureTheory MoireGeometry MoireDifferenceMeasure MoireLqDimension
open MoireAlmostEverySeparation MoireProjectionSeparation MoireWordPacking
open MoireMeasureSimilarity MoireBoxDimension MoireSection2
open scoped ENNReal

theorem projected_difference_full (angle : ℝ) (direction : ℂ)
    (separated : ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction)
    (q : ℝ) (q_gt_one : 1 < q) :
    lqDimension (projectedMeasure direction (differenceMeasure angle)) q = 1 :=
  MoireLqApplication.projected_difference_full MoireLiterature.inputs angle direction separated q q_gt_one

theorem difference_full (angle : ℝ) (separated : DifferenceExponentiallySeparated angle)
    (projections : ∀ direction : ℂ, ‖direction‖ = 1 →
      ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction)
    (q : ℝ) (q_gt_one : 1 < q) : lqDimension (differenceMeasure angle) q = 2 :=
  MoireLqApplication.difference_full MoireLiterature.inputs angle separated projections q q_gt_one

theorem ae_full_lq_dimension : ∀ᵐ angle : ℝ,
    ∀ q : ℝ, 1 < q → lqDimension (differenceMeasure angle) q = 2 := by
  filter_upwards [MoireSection3GeometricResults.ae_both_separation_lemmas] with angle hypotheses
  exact difference_full angle hypotheses.1 hypotheses.2

/-- The manuscript's almost-everywhere upper bound, relative to the documented
literature trust boundary and with no unfilled analytic hypothesis. -/
theorem ae_upper_box_dimension : ∀ᵐ angle : ℝ,
    upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) ≤
      ENNReal.ofReal (2 * (dimH gasket).toReal - 2) :=
  MoireLqApplication.ae_upper_bound MoireLiterature.inputs

end MoireSection3Complete
