import MoireBernoulliRecursion
import MoireSeparationGeometry

namespace MoireMeasureSimilarity

open MeasureTheory MoireGeometry MoireDifferenceMeasure MoireBernoulliRecursion
open scoped ENNReal
noncomputable section

def projectionMap (direction : ℂ) : ℂ →L[ℝ] ℂ where
  toFun point := ((star direction * point).re : ℂ)
  map_add' := by intros; simp [mul_add]
  map_smul' := by intros; simp [Complex.real_smul]; ring
  cont := by fun_prop

def projectedMeasure (direction : ℂ) (μ : Measure ℂ) : Measure ℂ :=
  μ.map (projectionMap direction)

instance (direction : ℂ) (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (projectedMeasure direction μ) :=
  Measure.isProbabilityMeasure_map (projectionMap direction).measurable.aemeasurable

theorem projection_convolution (direction : ℂ) (μ ν : Measure ℂ)
    [SFinite μ] [SFinite ν] :
    projectedMeasure direction (μ.conv ν) =
      (projectedMeasure direction μ).conv (projectedMeasure direction ν) :=
  Measure.map_conv_continuousLinearMap (projectionMap direction)

theorem projection_difference (angle : ℝ) (direction : ℂ) :
    projectedMeasure direction (differenceMeasure angle) =
      (projectedMeasure direction gasketMeasure).conv
        (projectedMeasure direction
          (gasketMeasure.map (fun point => -rotation angle point))) := by
  rw [MoireDifferenceLaw.differenceMeasure_eq_convolution, projection_convolution]

/-- Applying a real linear map transports the proved self-similar identity. -/
theorem mapped_gasket_selfSimilar (linear : ℂ →L[ℝ] ℂ) :
    gasketMeasure.map linear = Measure.sum (fun digit : Fin 3 =>
      (3 : ℝ≥0∞)⁻¹ • (gasketMeasure.map linear).map
        (fun point => (1 / 2 : ℝ) • (point + linear (vertex digit)))) := by
  conv_lhs => rw [gasketMeasure_selfSimilar]
  rw [Measure.map_sum linear.measurable.aemeasurable]
  congr 1
  funext digit
  rw [Measure.map_smul, Measure.map_map linear.measurable (by fun_prop),
    Measure.map_map (by fun_prop) linear.measurable]
  congr 2
  funext point
  simp only [Function.comp_apply, map_smul, map_add]

theorem differenceMeasure_selfSimilar (angle : ℝ) : differenceMeasure angle =
    Measure.sum (fun blue : Fin 3 => Measure.sum (fun red : Fin 3 =>
      (9 : ℝ≥0∞)⁻¹ • (differenceMeasure angle).map
        (fun point => (1 / 2 : ℝ) •
          (point + vertex blue - rotation angle (vertex red))))) := by
  have difference_measurable : Measurable
      (fun pair : ℂ × ℂ => pair.1 - rotation angle pair.2) :=
    measurable_fst.sub ((rotation_isometry angle).continuous.measurable.comp measurable_snd)
  conv_lhs => rw [differenceMeasure_eq_product_law, gasketMeasure_selfSimilar]
  rw [Measure.prod_sum_left, Measure.map_sum difference_measurable.aemeasurable]
  congr 1
  funext blue
  rw [Measure.prod_sum_right, Measure.map_sum difference_measurable.aemeasurable]
  congr 1
  funext red
  rw [Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.map_smul, Measure.map_smul, smul_smul]
  have weights : (3 : ℝ≥0∞)⁻¹ * 3⁻¹ = 9⁻¹ := by
    rw [← ENNReal.mul_inv] <;> norm_num
  rw [weights, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map difference_measurable (by fun_prop),
    differenceMeasure_eq_product_law, Measure.map_map (by fun_prop) difference_measurable]
  congr 2
  funext pair
  simp only [Function.comp_apply, Prod.map_apply]
  change (1 / 2 : ℝ) • (pair.1 + vertex blue) -
      Complex.exp ((angle : ℂ) * Complex.I) * ((1 / 2 : ℝ) • (pair.2 + vertex red)) =
    (1 / 2 : ℝ) • (pair.1 - Complex.exp ((angle : ℂ) * Complex.I) * pair.2 +
      vertex blue - Complex.exp ((angle : ℂ) * Complex.I) * vertex red)
  simp only [Complex.real_smul]
  ring

end
end MoireMeasureSimilarity
