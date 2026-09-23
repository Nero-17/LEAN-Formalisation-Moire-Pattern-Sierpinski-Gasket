import MoireSection2Results
import Mathlib.Topology.Order.DenselyOrdered

namespace MoireDensity

open MoireAngles MoireEisenstein

theorem arctan_parameter_mem_interval {parameter : ℝ}
    (nonneg : 0 ≤ parameter) (upper : parameter ≤ 1 / 3) :
    2 * Real.arctan (Real.sqrt 3 * parameter) ∈ Set.Icc 0 (Real.pi / 3) := by
  have lower := Real.arctan_mono
    (show (0 : ℝ) ≤ Real.sqrt 3 * parameter by positivity)
  rw [Real.arctan_zero] at lower
  have endpoint : Real.arctan (Real.sqrt 3 * (1 / 3)) = Real.pi / 6 := by
    have argument : Real.sqrt 3 * (1 / 3) = Real.tan (Real.pi / 6) := by
      rw [Real.tan_pi_div_six]
      have sqrt_pos : 0 < Real.sqrt 3 := by positivity
      apply (eq_div_iff (ne_of_gt sqrt_pos)).mpr
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [argument, Real.arctan_tan (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  have bound := Real.arctan_mono
    (mul_le_mul_of_nonneg_left upper (Real.sqrt_nonneg 3))
  rw [endpoint] at bound
  constructor <;> linarith

theorem rational_parameter_resonant (parameter : ℚ)
    (nonneg : 0 ≤ parameter) (upper : parameter ≤ 1 / 3) :
    Complex.exp ((2 * Real.arctan (Real.sqrt 3 * (parameter : ℝ)) : ℝ) * Complex.I)
      ∈ eisensteinField := by
  have bounds := arctan_parameter_mem_interval
    (show (0 : ℝ) ≤ (parameter : ℝ) by exact_mod_cast nonneg)
    (show (parameter : ℝ) ≤ 1 / 3 by
      have scaled : parameter * 3 ≤ (1 : ℚ) := by linarith
      have real_scaled : (parameter : ℝ) * 3 ≤ 1 := by exact_mod_cast scaled
      linarith)
  apply (exp_mem_eisensteinField_iff_rational_halfAngle _ bounds.1 bounds.2).mpr
  refine ⟨parameter, ?_⟩
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.tan_arctan]
  exact mul_div_cancel_left₀ _ (by positivity : Real.sqrt 3 ≠ 0)

/-- Closure equality expresses density in the closed angle interval, including endpoints. -/
theorem closure_resonant_angles :
    closure {angle : ℝ | 0 ≤ angle ∧ angle ≤ Real.pi / 3 ∧
      Complex.exp (angle * Complex.I) ∈ eisensteinField} = Set.Icc 0 (Real.pi / 3) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_Icc
    intro angle member
    exact ⟨member.1, member.2.1⟩
  · intro angle bounds
    have continuous_parameter : Continuous (fun parameter : ℝ =>
        2 * Real.arctan (Real.sqrt 3 * max 0 (min (1 / 3) parameter))) := by
      fun_prop
    have image_subset :
        (fun parameter : ℝ => 2 * Real.arctan
          (Real.sqrt 3 * max 0 (min (1 / 3) parameter))) '' Set.range (fun q : ℚ => (q : ℝ)) ⊆
          {angle : ℝ | 0 ≤ angle ∧ angle ≤ Real.pi / 3 ∧
            Complex.exp (angle * Complex.I) ∈ eisensteinField} := by
      rintro _ ⟨_, ⟨parameter, rfl⟩, rfl⟩
      have nonneg : (0 : ℚ) ≤ max 0 (min (1 / 3) parameter) := le_max_left _ _
      have upper : max 0 (min (1 / 3) parameter) ≤ (1 / 3 : ℚ) :=
        max_le (by norm_num) (min_le_left _ _)
      have cast_parameter : ((max 0 (min (1 / 3) parameter) : ℚ) : ℝ) =
          max 0 (min (1 / 3) (parameter : ℝ)) := by push_cast; rfl
      have interval := arctan_parameter_mem_interval
        (show (0 : ℝ) ≤ ((max 0 (min (1 / 3) parameter) : ℚ) : ℝ) by exact_mod_cast nonneg)
        (show ((max 0 (min (1 / 3) parameter) : ℚ) : ℝ) ≤ 1 / 3 by
          have scaled : max 0 (min (1 / 3) parameter) * 3 ≤ (1 : ℚ) := by linarith
          have real_scaled : ((max 0 (min (1 / 3) parameter) : ℚ) : ℝ) * 3 ≤ 1 :=
            by exact_mod_cast scaled
          linarith)
      have resonant := rational_parameter_resonant _ nonneg upper
      rw [cast_parameter] at interval resonant
      exact ⟨interval.1, interval.2, resonant⟩
    apply (closure_mono image_subset)
    apply image_closure_subset_closure_image continuous_parameter
    refine ⟨Real.tan (angle / 2) / Real.sqrt 3, ?_, ?_⟩
    · exact Rat.denseRange_cast _
    · have parameter_bounds := halfAngle_mem_interval angle bounds.1 bounds.2
      dsimp only
      rw [min_eq_right parameter_bounds.2, max_eq_right parameter_bounds.1]
      exact (angle_eq_arctan_halfAngle angle bounds.1 bounds.2).symm

end MoireDensity
