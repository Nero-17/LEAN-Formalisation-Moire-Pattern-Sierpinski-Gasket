import MoireSpectralMass
import MoireMassDistribution

namespace MoireHausdorffLower

open MoireGeometry MoireSection2 MoireDeterminization MeasureTheory
open scoped ENNReal

theorem dyadic_spectral_power (growth : ℝ) (positive : 0 < growth) (length : ℕ) :
    ((1 / 2 : ℝ) ^ length) ^ (Real.log growth / Real.log 2) = (growth ^ length)⁻¹ := by
  have log_two_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have power : (2 : ℝ) ^ (Real.log growth / Real.log 2) = growth := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have exponent : Real.log 2 * (Real.log growth / Real.log 2) = Real.log growth := by
      field_simp
    rw [exponent, Real.exp_log positive]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_comm (length : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2),
    one_div, Real.inv_rpow (by norm_num), power, inv_pow]

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The lower bound is for the actual represented gasket intersection, obtained
from a probability measure and a proved Euclidean mass-distribution estimate. -/
theorem represented_dimH_lower (angle : ℝ) (represented : State → Finset ℂ)
    (injective : Function.Injective represented)
    (nonempty : ∀ state, (stateIntersection gasket (rotation angle) (represented state)).Nonempty)
    (weights : State → ℝ) (weights_nonneg : ∀ state, 0 ≤ weights state)
    (growth : ℝ) (growth_gt_one : 1 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (MoireGraphCovers.adjacency
        (fun source digit target => Edge vertex gasket (rotation angle)
          (represented source) digit (represented target)) source target : ℝ) * weights target)
    (initial : State × Fin 3) (positive : 0 < weights initial.1) :
    ENNReal.ofReal (Real.log growth / Real.log 2) ≤
      dimH (stateIntersection gasket (rotation angle) (represented initial.1)) := by
  letI : Nonempty State := ⟨initial.1⟩
  let edge : State → Fin 3 → State → Prop := fun source digit target =>
    Edge vertex gasket (rotation angle) (represented source) digit (represented target)
  let measure := MoireGeometricMeasure.geometricMeasure edge weights weights_nonneg initial
  have deterministic : ∀ source digit first second, edge source digit first → edge source digit second → first = second := by
    intro source digit first second first_edge second_edge
    exact injective (edge_deterministic vertex gasket (rotation angle) first_edge second_edge)
  have growth_pos : 0 < growth := lt_trans zero_lt_one growth_gt_one
  have sum_pos : 0 < ∑ state, weights state := positive.trans_le
    (Finset.single_le_sum (fun state _ => weights_nonneg state) (Finset.mem_univ initial.1))
  have exponent_pos : 0 < Real.log growth / Real.log 2 :=
    div_pos (Real.log_pos growth_gt_one) (Real.log_pos (by norm_num))
  have mass_one : measure (stateIntersection gasket (rotation angle) (represented initial.1)) = 1 := by
    have supported := MoireGeometricMeasure.ae_code_mem angle represented nonempty weights weights_nonneg
      growth growth_pos subeigen initial positive
    have measurable := (MoireGraphGeometry.stateIntersection_isCompact angle (represented initial.1)).measurableSet
    change (MoireGeometricMeasure.geometricMeasure edge weights weights_nonneg initial) _ = 1
    rw [MoireGeometricMeasure.geometricMeasure,
      Measure.map_apply MoireGeometricMeasure.code_measurable measurable]
    exact (mem_ae_iff_prob_eq_one (measurable.preimage MoireGeometricMeasure.code_measurable)).mp supported
  apply MoireMassDistribution.le_dimH_of_dyadic_mass measure
    (Real.log growth / Real.log 2) (289 * (∑ state, weights state) / weights initial.1)
    exponent_pos (by positivity) ?_ _ (by rw [mass_one]; exact one_ne_zero)
  intro length center
  have bound := MoireSpectralMass.geometric_dyadic_ball_mass edge deterministic weights weights_nonneg
    growth growth_pos subeigen initial positive length center
  apply bound.trans_eq
  rw [dyadic_spectral_power growth growth_pos length, ← ENNReal.ofReal_ofNat 289,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  field_simp

end MoireHausdorffLower
