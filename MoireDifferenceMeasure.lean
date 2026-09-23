import MoireSmallBalls
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform

/-! The actual symbolic probability space and its planar difference law.
Finite prefixes are events in the symbolic space, so boundary coincidences
of geometric cells cannot cause overcounting of their probabilities. -/

namespace MoireDifferenceMeasure

open MeasureTheory MoireGeometry
open scoped ENNReal

noncomputable section

def digitMeasure : Measure (Fin 3) :=
  (PMF.uniformOfFintype (Fin 3)).toMeasure

instance : IsProbabilityMeasure digitMeasure := inferInstanceAs
  (IsProbabilityMeasure (PMF.uniformOfFintype (Fin 3)).toMeasure)

def singleAddressMeasure : Measure (ℕ → Fin 3) :=
  Measure.infinitePi (fun _ => digitMeasure)

instance : IsProbabilityMeasure singleAddressMeasure := inferInstanceAs
  (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => digitMeasure)))

def joinAddresses (addresses : (ℕ → Fin 3) × (ℕ → Fin 3)) : ℕ → Fin 3 × Fin 3 :=
  fun n => (addresses.1 n, addresses.2 n)

theorem joinAddresses_measurable : Measurable joinAddresses := by unfold joinAddresses; fun_prop

def addressMeasure : Measure (ℕ → Fin 3 × Fin 3) :=
  (singleAddressMeasure.prod singleAddressMeasure).map joinAddresses

instance : IsProbabilityMeasure addressMeasure := by
  unfold addressMeasure
  exact Measure.isProbabilityMeasure_map joinAddresses_measurable.aemeasurable

def gasketMeasure : Measure ℂ :=
  singleAddressMeasure.map (addressPoint vertex)

instance : IsProbabilityMeasure gasketMeasure := by
  unfold gasketMeasure
  exact Measure.isProbabilityMeasure_map (MoireDimension.continuous_addressPoint vertex).measurable.aemeasurable

def differencePoint (angle : ℝ) (address : ℕ → Fin 3 × Fin 3) : ℂ :=
  addressPoint vertex (fun n => (address n).1) -
    rotation angle (addressPoint vertex (fun n => (address n).2))

theorem differencePoint_measurable (angle : ℝ) : Measurable (differencePoint angle) := by
  apply Measurable.sub
  · exact (MoireDimension.continuous_addressPoint vertex).measurable.comp (by fun_prop)
  · exact (rotation_isometry angle).continuous.measurable.comp
      ((MoireDimension.continuous_addressPoint vertex).measurable.comp (by fun_prop))

def differenceMeasure (angle : ℝ) : Measure ℂ :=
  addressMeasure.map (differencePoint angle)

instance (angle : ℝ) : IsProbabilityMeasure (differenceMeasure angle) := by
  unfold differenceMeasure
  exact Measure.isProbabilityMeasure_map (differencePoint_measurable angle).aemeasurable

def pairPrefix (length : ℕ) (address : ℕ → Fin 3 × Fin 3) : Fin length → Fin 3 × Fin 3 :=
  fun k => address k

theorem prefix_measurable (length : ℕ) : Measurable (pairPrefix length) := by
  unfold pairPrefix
  fun_prop

theorem single_prefix_probability (length : ℕ) (word : Fin length → Fin 3) :
    singleAddressMeasure {address | (fun k : Fin length => address k) = word} =
      (3 : ℝ≥0∞)⁻¹ ^ length := by
  have event_eq : {address | (fun k : Fin length => address k) = word} =
      Set.pi (Finset.range length) (fun k => if h : k < length then {word ⟨k, h⟩} else Set.univ) := by
    ext address
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
    constructor
    · intro equality k bound
      simp only [dif_pos bound, Set.mem_singleton_iff]
      exact congrFun equality ⟨k, bound⟩
    · intro equalities
      funext k
      simpa only [dif_pos k.isLt, Set.mem_singleton_iff] using equalities k k.isLt
  rw [event_eq]
  change Measure.infinitePi (fun _ : ℕ => digitMeasure) _ = _
  rw [Measure.infinitePi_pi (fun _ : ℕ => digitMeasure)
    (by intro k _; split_ifs <;> measurability)]
  calc
    _ = ∏ _k ∈ Finset.range length, (3 : ℝ≥0∞)⁻¹ := by
      apply Finset.prod_congr rfl
      intro k member
      rw [dif_pos (Finset.mem_range.mp member)]
      simp [digitMeasure, PMF.uniformOfFintype_apply]
    _ = _ := by simp

theorem prefix_probability (length : ℕ) (word : Fin length → Fin 3 × Fin 3) :
    addressMeasure {address | pairPrefix length address = word} = (9 : ℝ≥0∞)⁻¹ ^ length := by
  have event_measurable : MeasurableSet {address | pairPrefix length address = word} :=
    (prefix_measurable length) (measurableSet_singleton word)
  rw [addressMeasure, Measure.map_apply joinAddresses_measurable event_measurable]
  have event_eq : joinAddresses ⁻¹' {address | pairPrefix length address = word} =
      {address | (fun k : Fin length => address k) = fun k => (word k).1} ×ˢ
      {address | (fun k : Fin length => address k) = fun k => (word k).2} := by
    ext addresses
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod, funext_iff, pairPrefix, joinAddresses,
      Prod.ext_iff, forall_and]
  rw [event_eq, Measure.prod_prod, single_prefix_probability, single_prefix_probability, ← mul_pow]
  congr 1
  rw [← ENNReal.mul_inv] <;> norm_num

/-- This is precisely the law of X - Rθ Y for independent uniform gasket points. -/
theorem differenceMeasure_eq_product_law (angle : ℝ) :
    differenceMeasure angle = (gasketMeasure.prod gasketMeasure).map
      (fun points => points.1 - rotation angle points.2) := by
  have code_measurable := (MoireDimension.continuous_addressPoint vertex).measurable
  have difference_measurable : Measurable (fun points : ℂ × ℂ => points.1 - rotation angle points.2) :=
    measurable_fst.sub ((rotation_isometry angle).continuous.measurable.comp measurable_snd)
  rw [gasketMeasure, Measure.map_prod_map _ _
    (MoireDimension.continuous_addressPoint vertex).measurable
    (MoireDimension.continuous_addressPoint vertex).measurable,
    Measure.map_map difference_measurable (code_measurable.prodMap code_measurable), differenceMeasure, addressMeasure,
    Measure.map_map (differencePoint_measurable angle) joinAddresses_measurable]
  rfl

theorem prefix_event_probability (length : ℕ)
    (words : Finset (Fin length → Fin 3 × Fin 3)) :
    addressMeasure {address | pairPrefix length address ∈ words} =
      (words.card : ℝ≥0∞) * (9 : ℝ≥0∞)⁻¹ ^ length := by
  have event_eq : {address | pairPrefix length address ∈ words} =
      ⋃ word ∈ words, {address | pairPrefix length address = word} := by ext; simp
  rw [event_eq, measure_biUnion_finset]
  · simp only [prefix_probability, Finset.sum_const, nsmul_eq_mul]
  · intro first _ second _ different
    exact Set.disjoint_left.mpr (fun _ first_eq second_eq => different (first_eq.symm.trans second_eq))
  · intro word _
    exact (prefix_measurable length) (measurableSet_singleton word)

end
end MoireDifferenceMeasure
