import MoireDifferenceMeasure
import Mathlib.MeasureTheory.Group.Convolution

namespace MoireDifferenceLaw

open MoireGeometry MoireDifferenceMeasure MeasureTheory

theorem gasketMeasure_gasket : gasketMeasure gasket = 1 := by
  rw [gasketMeasure, Measure.map_apply (MoireDimension.continuous_addressPoint vertex).measurable
    MoireDimension.isCompact_gasket.isClosed.measurableSet]
  have preimage : addressPoint vertex ⁻¹' gasket = Set.univ := by
    ext address
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact ⟨address, rfl⟩
  rw [preimage, measure_univ]

/-- The symbolic construction is exactly the convolution in Section 3's definition. -/
theorem differenceMeasure_eq_convolution (angle : ℝ) :
    differenceMeasure angle = gasketMeasure.conv
      (gasketMeasure.map (fun point => -rotation angle point)) := by
  have neg_rotation : Measurable (fun point => -rotation angle point) :=
    (rotation_isometry angle).continuous.measurable.neg
  have product_eq : gasketMeasure.prod (gasketMeasure.map (fun point => -rotation angle point)) =
      (gasketMeasure.prod gasketMeasure).map (Prod.map id (fun point => -rotation angle point)) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map gasketMeasure gasketMeasure measurable_id neg_rotation
  rw [differenceMeasure_eq_product_law, Measure.conv, product_eq,
    Measure.map_map measurable_add (measurable_id.prodMap neg_rotation)]
  congr 1

end MoireDifferenceLaw
