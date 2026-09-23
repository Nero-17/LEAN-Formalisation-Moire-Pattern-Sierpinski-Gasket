import MoireAngularSublevel
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace MoireDeterminantSublevel

open MoireGeometry MoireSeparationGeometry MoireAngularSublevel MeasureTheory
open scoped ENNReal

theorem determinant_rotation_sine (first second : ℂ) (angle : ℝ) :
    determinant first (rotation angle second) =
      (‖first‖ * ‖second‖) * Real.sin (angle + Complex.arg (star first * second)) := by
  have product_eq : Complex.exp ((angle : ℂ) * Complex.I) * (star first * second) =
      (‖star first * second‖ : ℂ) * Complex.exp
        (((angle + Complex.arg (star first * second) : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => arg 2; rw [← Complex.norm_mul_exp_arg_mul_I (star first * second)]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  have imaginary := congrArg Complex.im product_eq
  have left_eq : (Complex.exp ((angle : ℂ) * Complex.I) * (star first * second)).im =
      determinant first (rotation angle second) := by
    simp only [rotation, LinearMap.coe_mk, AddHom.coe_mk, Complex.star_def,
      determinant, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [left_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.exp_ofReal_mul_I_im, norm_mul, norm_star] at imaginary
  exact imaginary

theorem determinant_sublevel_volume (first second : ℂ) (scale threshold : ℝ)
    (scale_pos : 0 < scale) (amplitude : scale ≤ ‖first‖ * ‖second‖)
    (threshold_nonneg : 0 ≤ threshold) :
    volume {angle : ℝ | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧
      |determinant first (rotation angle second)| < scale * threshold} ≤
      ENNReal.ofReal (9 * Real.pi * threshold) := by
  apply (measure_mono (show {angle : ℝ | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧
      |determinant first (rotation angle second)| < scale * threshold} ⊆
      {angle : ℝ | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧
        |Real.sin (angle + Complex.arg (star first * second))| < threshold} from ?_)).trans
    (sine_sublevel_volume _ _ (by linarith [Complex.neg_pi_lt_arg (star first * second), Real.pi_pos])
      (by linarith [Complex.arg_le_pi (star first * second), Real.pi_pos]))
  rintro angle ⟨nonneg, upper, small⟩
  refine ⟨nonneg, upper, ?_⟩
  rw [determinant_rotation_sine, abs_mul, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at small
  have lower := mul_le_mul_of_nonneg_right amplitude
    (abs_nonneg (Real.sin (angle + Complex.arg (star first * second))))
  nlinarith

end MoireDeterminantSublevel
