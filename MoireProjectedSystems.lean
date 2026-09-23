import MoireHomogeneousSystem

namespace MoireProjectedSystems
open MeasureTheory Filter MoireGeometry MoireDifferenceMeasure MoireWordPacking
open MoireSeparationGeometry MoireProjectionSeparation MoireMeasureSimilarity MoireHomogeneousSystem
noncomputable section

def reflectedProjection (angle : ℝ) (direction : ℂ) : ℂ →L[ℝ] ℂ :=
  -((projectionMap direction).comp (rotationMap angle))

theorem norm_projection (direction point : ℂ) :
    ‖projectionMap direction point‖ = |projection direction point| := by
  change ‖((projection direction point : ℝ) : ℂ)‖ = |projection direction point|
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem mapped_selfSimilar (linear : ℂ →L[ℝ] ℂ) :
    UniformSelfSimilar (gasketMeasure.map linear) (fun digit => linear (vertex digit)) := by
  simpa only [UniformSelfSimilar, Fintype.card_fin, Nat.cast_ofNat] using mapped_gasket_selfSimilar linear

theorem projected_separation (direction : ℂ)
    (separated : ExponentiallySeparated (fun _ word => wordCenter word) direction) :
    ExponentialSeparation (fun digit => projectionMap direction (vertex digit)) := by
  obtain ⟨rate, positive, small, separated⟩ := separated
  refine ⟨rate, positive, small, separated.mono ?_⟩
  intro n bound first second different
  rw [cylinderCenter_linear, cylinderCenter_linear, cylinderCenter_vertex,
    cylinderCenter_vertex, ← map_sub, norm_projection]
  exact bound first second different

theorem reflected_separation (angle : ℝ) (direction : ℂ)
    (separated : ExponentiallySeparated
      (fun _ word => rotation angle (wordCenter word)) direction) :
    ExponentialSeparation (fun digit => reflectedProjection angle direction (vertex digit)) := by
  obtain ⟨rate, positive, small, separated⟩ := separated
  refine ⟨rate, positive, small, separated.mono ?_⟩
  intro n bound first second different
  rw [cylinderCenter_linear, cylinderCenter_linear, cylinderCenter_vertex,
    cylinderCenter_vertex, ← map_sub]
  change rate ^ n ≤ ‖-(projectionMap direction (rotationMap angle (wordCenter first - wordCenter second)))‖
  rw [norm_neg, norm_projection]
  exact (bound first second different).trans_eq (by rw [map_sub]; rfl)

theorem projection_real (direction point : ℂ) : (projectionMap direction point).im = 0 := rfl

theorem reflected_real (angle : ℝ) (direction point : ℂ) :
    (reflectedProjection angle direction point).im = 0 := by
  simp [reflectedProjection, projectionMap]

theorem map_real_mass (linear : ℂ →L[ℝ] ℂ) (real_image : ∀ point, (linear point).im = 0) :
    (gasketMeasure.map linear) {point : ℂ | point.im = 0} = 1 := by
  rw [Measure.map_apply linear.measurable (by measurability)]
  have preimage : linear ⁻¹' {point : ℂ | point.im = 0} = Set.univ := by
    ext point
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact real_image point
  rw [preimage, measure_univ]

theorem projected_difference_convolution (angle : ℝ) (direction : ℂ) :
    projectedMeasure direction (differenceMeasure angle) =
      (gasketMeasure.map (projectionMap direction)).conv
        (gasketMeasure.map (reflectedProjection angle direction)) := by
  rw [projection_difference]
  congr 1
  unfold projectedMeasure
  rw [Measure.map_map (projectionMap direction).measurable
    (show Measurable (fun point => -rotation angle point) from
      (rotation_isometry angle).continuous.measurable.neg)]
  congr 1
  funext point
  simp only [Function.comp_apply, map_neg, reflectedProjection,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
  rfl

end
end MoireProjectedSystems
