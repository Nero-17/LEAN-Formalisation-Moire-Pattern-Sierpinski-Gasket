import MoireAngles
import MoireDimension
import Mathlib.Analysis.Real.OfDigits

namespace MoireNonempty

open MoireGeometry MoireSection2

theorem edge_mem_gasket (firstDigit secondDigit : Fin 3) (parameter : ℝ)
    (nonneg : 0 ≤ parameter) (upper : parameter ≤ 1) :
    (1 - parameter) • vertex firstDigit + parameter • vertex secondDigit ∈ gasket := by
  obtain ⟨digits, _, digits_eq⟩ := Real.ofDigits_SurjOn (b := 2) (by norm_num)
    ⟨nonneg, upper⟩
  have weights_summable : Summable (fun level : ℕ => (1 / 2 : ℝ) ^ (level + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (1 / 2)
  have weights_sum : (∑' level : ℕ, (1 / 2 : ℝ) ^ (level + 1)) = 1 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
    norm_num
  refine ⟨fun level => if digits level = 0 then firstDigit else secondDigit, ?_⟩
  unfold addressPoint
  have term_eq : ∀ level : ℕ,
      (1 / 2 : ℝ) ^ (level + 1) • vertex (if digits level = 0 then firstDigit else secondDigit) =
        (1 / 2 : ℝ) ^ (level + 1) • vertex firstDigit +
          Real.ofDigitsTerm digits level • (vertex secondDigit - vertex firstDigit) := by
    intro level
    have cases : digits level = 0 ∨ digits level = 1 := by omega
    rcases cases with zero | one
    · simp [zero, Real.ofDigitsTerm]
    · simp only [one, one_ne_zero, ↓reduceIte, Real.ofDigitsTerm, Fin.val_one,
        Nat.cast_one, Nat.cast_ofNat, one_mul]
      rw [← inv_pow, ← one_div]
      module
  simp_rw [term_eq]
  rw [Summable.tsum_add (weights_summable.smul_const _) (Real.summable_ofDigitsTerm.smul_const _),
    weights_summable.tsum_smul_const,
    Real.summable_ofDigitsTerm.tsum_smul_const, weights_sum]
  change (1 : ℝ) • vertex firstDigit + Real.ofDigits digits •
    (vertex secondDigit - vertex firstDigit) = _
  rw [digits_eq]
  module

theorem initial_intersection_nonempty (angle : ℝ)
    (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3) :
    (shiftedIntersection gasket (rotation angle) 0).Nonempty := by
  let parameter := Real.tan (angle / 2) / Real.sqrt 3
  have bounds : parameter ∈ Set.Icc 0 (1 / 3 : ℝ) :=
    MoireAngles.halfAngle_mem_interval angle nonneg upper
  have denominator_pos : 0 < 1 + 3 * parameter := by linarith [bounds.1]
  have edge_parameter_nonneg : 0 ≤ 2 * parameter / (1 + 3 * parameter) :=
    div_nonneg (mul_nonneg (by norm_num) bounds.1) denominator_pos.le
  have edge_parameter_upper : 2 * parameter / (1 + 3 * parameter) ≤ 1 := by
    apply (div_le_iff₀ denominator_pos).mpr
    linarith [bounds.1]
  have blue_mem := edge_mem_gasket 0 1 _ edge_parameter_nonneg edge_parameter_upper
  have red_mem := edge_mem_gasket 0 2 _ edge_parameter_nonneg edge_parameter_upper
  refine ⟨_, blue_mem, _, red_mem, ?_⟩
  simp only [sub_zero]
  have sqrt_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have sqrt_ne : Real.sqrt 3 ≠ 0 := by positivity
  have tangent_eq : Real.tan (angle / 2) = parameter * Real.sqrt 3 := by
    dsimp [parameter]
    exact (div_mul_cancel₀ _ sqrt_ne).symm
  have tangent_sq : Real.tan (angle / 2) ^ 2 = 3 * parameter ^ 2 := by
    rw [tangent_eq, mul_pow, sqrt_sq]
    ring
  have cosine_eq : Real.cos angle = (1 - 3 * parameter ^ 2) / (1 + 3 * parameter ^ 2) := by
    have cosine_pos : 0 < Real.cos angle :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq angle (by linarith), tangent_sq]
  have sine_eq : Real.sin angle = 2 * parameter * Real.sqrt 3 / (1 + 3 * parameter ^ 2) := by
    rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq, tangent_sq, tangent_eq]
    ring
  have quadratic_ne : 1 + 3 * parameter ^ 2 ≠ 0 := by positivity
  apply Complex.ext <;>
    simp only [rotation, LinearMap.coe_mk, AddHom.coe_mk, Complex.mul_re, Complex.mul_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.add_re, Complex.add_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero, vertex, Complex.one_re, Complex.one_im,
      cosine_eq, sine_eq] <;>
    field_simp [ne_of_gt denominator_pos, quadratic_ne] <;>
    ring_nf <;> simp [sqrt_sq] <;>
    field_simp [show 1 + parameter * 3 ≠ 0 by nlinarith [bounds.1]] <;> ring

end MoireNonempty
