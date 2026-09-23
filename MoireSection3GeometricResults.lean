import MoireSeparationPeriodicity
import MoireGasketDimension
import MoireUpperFromLq

namespace MoireSection3GeometricResults

open MoireGeometry MoireSection2 MoireDifferenceMeasure MoireLqDimension MoireBoxDimension
open MoireProjectionSeparation MoireAlmostEverySeparation MoireWordPacking MeasureTheory
open scoped ENNReal

/-- The codimension form of the upper bound, using the proved Hausdorff dimension
of the actual gasket. Full Lq dimension remains an explicit analytic hypothesis. -/
theorem upperBox_le_codimension_of_full_lq (angle : ℝ)
    (full : ∀ q : ℝ, 1 < q → lqDimension (differenceMeasure angle) q = 2) :
    upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) ≤
      ENNReal.ofReal (2 * (dimH gasket).toReal - 2) := by
  rw [MoireGasketDimension.gasket_dimH, ENNReal.toReal_ofReal
    (div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_pos (by norm_num)).le)]
  have logarithm : Real.log 9 = 2 * Real.log 3 := by
    calc
      Real.log 9 = Real.log ((3 : ℝ) ^ 2) := congrArg Real.log (by norm_num)
      _ = _ := Real.log_pow (3 : ℝ) 2
  have result := MoireUpperFromLq.upperBox_le_of_full_lq angle full
  rw [logarithm, mul_div_assoc] at result
  exact result

/-- Both almost-everywhere geometric hypotheses needed by the analytic argument
are established, with the universal direction quantifier inside one full-measure set. -/
theorem ae_both_separation_lemmas : ∀ᵐ angle : ℝ,
    DifferenceExponentiallySeparated angle ∧
      ∀ direction : ℂ, ‖direction‖ = 1 →
        ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
        ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction := by
  filter_upwards [MoireSeparationPeriodicity.ae_difference_exponential_separation,
    MoireSeparationPeriodicity.ae_projection_dichotomy] with angle separated projected
  exact ⟨separated, projected⟩

/-- This theorem records the exact unfinished analytic bridge. It must not be
reported as an unconditional formalisation of Section 3's main theorem. -/
theorem ae_upper_bound_of_analytic_input
    (analytic : ∀ angle : ℝ, DifferenceExponentiallySeparated angle →
      (∀ direction : ℂ, ‖direction‖ = 1 →
        ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
        ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction) →
      ∀ q : ℝ, 1 < q → lqDimension (differenceMeasure angle) q = 2) :
    ∀ᵐ angle : ℝ, upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) ≤
      ENNReal.ofReal (2 * (dimH gasket).toReal - 2) := by
  filter_upwards [ae_both_separation_lemmas] with angle hypotheses
  exact upperBox_le_codimension_of_full_lq angle (analytic angle hypotheses.1 hypotheses.2)

end MoireSection3GeometricResults
