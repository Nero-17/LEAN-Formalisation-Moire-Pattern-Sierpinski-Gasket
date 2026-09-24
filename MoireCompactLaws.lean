import MoireMeasureSupport
import MoireProjectedSystems

/-! Compact full-mass sets for every measure used in the literature application. -/
namespace MoireCompactLaws
open MeasureTheory MoireGeometry MoireDifferenceMeasure MoireMeasureSimilarity

def CompactlySupported (μ : Measure ℂ) : Prop :=
  ∃ carrier : Set ℂ, IsCompact carrier ∧ μ carrier = 1

theorem map_compact (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (compact : CompactlySupported μ) (function : ℂ → ℂ) (continuous : Continuous function) :
    CompactlySupported (μ.map function) := by
  obtain ⟨carrier, compact, full⟩ := compact
  refine ⟨function '' carrier, compact.image continuous, ?_⟩
  rw [Measure.map_apply continuous.measurable (compact.image continuous).isClosed.measurableSet]
  apply le_antisymm (by
    have upper : μ (function ⁻¹' (function '' carrier)) ≤ μ Set.univ :=
      measure_mono (Set.subset_univ _)
    simpa using upper)
  rw [← full]
  exact measure_mono (Set.subset_preimage_image function carrier)

theorem gasket_compact : CompactlySupported gasketMeasure :=
  ⟨gasket, MoireDimension.isCompact_gasket, MoireDifferenceLaw.gasketMeasure_gasket⟩

theorem mapped_gasket_compact (linear : ℂ →L[ℝ] ℂ) :
    CompactlySupported (gasketMeasure.map linear) :=
  map_compact gasketMeasure gasket_compact linear linear.continuous

theorem difference_compact (angle : ℝ) : CompactlySupported (differenceMeasure angle) := by
  refine ⟨Set.range (differencePoint angle),
    isCompact_range (MoireMeasureSupport.differencePoint_continuous angle), ?_⟩
  rw [differenceMeasure, Measure.map_apply (differencePoint_measurable angle)
    (isCompact_range (MoireMeasureSupport.differencePoint_continuous angle)).isClosed.measurableSet]
  simp

theorem projected_difference_compact (angle : ℝ) (direction : ℂ) :
    CompactlySupported (projectedMeasure direction (differenceMeasure angle)) :=
  map_compact _ (difference_compact angle) _ (projectionMap direction).continuous

end MoireCompactLaws
