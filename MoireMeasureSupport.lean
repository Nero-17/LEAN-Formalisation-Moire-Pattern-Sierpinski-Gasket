import MoireDifferenceLaw
import Mathlib.MeasureTheory.Measure.Support

namespace MoireMeasureSupport
open MeasureTheory MoireGeometry MoireDifferenceMeasure Filter Topology
open scoped ENNReal

instance : Measure.IsOpenPosMeasure singleAddressMeasure := by
  classical
  constructor
  intro set is_open nonempty
  obtain ⟨address, member⟩ := nonempty
  have neighborhood := is_open.mem_nhds member
  rw [nhds_pi, Filter.mem_pi'] at neighborhood
  obtain ⟨indices, sets, neighborhoods, contained⟩ := neighborhood
  have singleton_box : Set.pi (↑indices) (fun n => {address n}) ⊆ set := by
    intro other same
    apply contained
    intro n hn
    rw [show other n = address n from same n hn]
    exact mem_of_mem_nhds (neighborhoods n)
  have positive : 0 < singleAddressMeasure (Set.pi (↑indices) (fun n => {address n})) := by
    rw [singleAddressMeasure, Measure.infinitePi_pi _ (by intros; measurability)]
    apply bot_lt_iff_ne_bot.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro n _
    simp [digitMeasure, PMF.uniformOfFintype_apply]
  exact ne_of_gt (positive.trans_le (measure_mono singleton_box))

instance : Measure.IsOpenPosMeasure addressMeasure := by
  apply Continuous.isOpenPosMeasure_map
  · unfold joinAddresses; fun_prop
  · intro address
    exact ⟨(fun n => (address n).1, fun n => (address n).2), rfl⟩

theorem support_map_eq_range {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X)
    [Measure.IsOpenPosMeasure μ] (function : X → ℂ) (continuous : Continuous function) :
    (μ.map function).support = Set.range function := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed (isCompact_range continuous).isClosed
    change μ.map function (Set.range function)ᶜ = 0
    rw [Measure.map_apply continuous.measurable (isCompact_range continuous).isClosed.measurableSet.compl]
    simp
  · rintro point ⟨preimage, rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro neighborhood member is_open
    rw [Measure.map_apply continuous.measurable is_open.measurableSet]
    exact (is_open.preimage continuous).measure_pos μ ⟨preimage, member⟩

theorem gasketMeasure_support : gasketMeasure.support = gasket :=
  support_map_eq_range singleAddressMeasure (addressPoint vertex)
    (MoireDimension.continuous_addressPoint vertex)

theorem differencePoint_continuous (angle : ℝ) : Continuous (differencePoint angle) := by
  apply Continuous.sub
  · exact (MoireDimension.continuous_addressPoint vertex).comp (by fun_prop)
  · exact (rotation_isometry angle).continuous.comp
      ((MoireDimension.continuous_addressPoint vertex).comp (by fun_prop))

theorem differenceMeasure_support (angle : ℝ) : (differenceMeasure angle).support =
    {point | ∃ blue ∈ gasket, ∃ red ∈ gasket, point = blue - rotation angle red} := by
  rw [differenceMeasure, support_map_eq_range addressMeasure _ (differencePoint_continuous angle)]
  ext point
  constructor
  · rintro ⟨address, rfl⟩
    exact ⟨_, ⟨fun n => (address n).1, rfl⟩,
      _, ⟨fun n => (address n).2, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨blue, rfl⟩, _, ⟨red, rfl⟩, rfl⟩
    exact ⟨fun n => (blue n, red n), rfl⟩

theorem difference_support_compact (angle : ℝ) : IsCompact (differenceMeasure angle).support := by
  rw [differenceMeasure, support_map_eq_range addressMeasure _ (differencePoint_continuous angle)]
  exact isCompact_range (differencePoint_continuous angle)

end MoireMeasureSupport
