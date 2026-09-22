import MoireEisenstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Arithmetic characterisations of resonant angles

This file proves the rational half-angle criterion in the concrete Eisenstein
field. All occurrences of trigonometric functions and field membership refer to
the real and complex models used by the manuscript.
-/

namespace MoireAngles

open MoireEisenstein

theorem mem_eisensteinField_iff_rational_parts (point : ℂ) :
    point ∈ eisensteinField ↔ ∃ realPart imaginaryCoefficient : ℚ,
      point.re = (realPart : ℝ) ∧
      point.im = (imaginaryCoefficient : ℝ) * Real.sqrt 3 := by
  have sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · intro point_mem
    change point ∈ Subfield.closure {omega} at point_mem
    induction point_mem using Subfield.closure_induction with
    | mem point point_mem =>
      have point_eq := Set.mem_singleton_iff.mp point_mem
      subst point
      refine ⟨-1 / 2, 1 / 2, ?_, ?_⟩ <;> norm_num [omega] <;> ring
    | one => exact ⟨1, 0, by simp, by simp⟩
    | add firstPoint secondPoint _ _ first_mem second_mem =>
      obtain ⟨firstReal, firstImaginary, first_re, first_im⟩ := first_mem
      obtain ⟨secondReal, secondImaginary, second_re, second_im⟩ := second_mem
      refine ⟨firstReal + secondReal, firstImaginary + secondImaginary, ?_, ?_⟩
      · simp [first_re, second_re]
      · simp [first_im, second_im]; ring
    | neg point _ point_mem =>
      obtain ⟨realPart, imaginaryCoefficient, point_re, point_im⟩ := point_mem
      exact ⟨-realPart, -imaginaryCoefficient, by simp [point_re], by simp [point_im]⟩
    | inv point _ point_mem =>
      obtain ⟨realPart, imaginaryCoefficient, point_re, point_im⟩ := point_mem
      have norm_sq : Complex.normSq point =
          ((realPart ^ 2 + 3 * imaginaryCoefficient ^ 2 : ℚ) : ℝ) := by
        simp only [Complex.normSq_apply, point_re, point_im, Rat.cast_add, Rat.cast_pow,
          Rat.cast_mul, Rat.cast_ofNat]
        linear_combination (imaginaryCoefficient : ℝ) ^ 2 * sqrt_three_sq
      refine ⟨realPart / (realPart ^ 2 + 3 * imaginaryCoefficient ^ 2),
        -imaginaryCoefficient / (realPart ^ 2 + 3 * imaginaryCoefficient ^ 2), ?_, ?_⟩
      · simp [Complex.inv_re, point_re, norm_sq]
      · simp [Complex.inv_im, point_im, norm_sq]; ring
    | mul firstPoint secondPoint _ _ first_mem second_mem =>
      obtain ⟨firstReal, firstImaginary, first_re, first_im⟩ := first_mem
      obtain ⟨secondReal, secondImaginary, second_re, second_im⟩ := second_mem
      refine ⟨firstReal * secondReal - 3 * firstImaginary * secondImaginary,
        firstReal * secondImaginary + firstImaginary * secondReal, ?_, ?_⟩
      · simp only [Complex.mul_re, first_re, second_re, first_im, second_im,
          Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
        linear_combination -(firstImaginary : ℝ) * (secondImaginary : ℝ) * sqrt_three_sq
      · simp only [Complex.mul_im, first_re, second_re, first_im, second_im,
          Rat.cast_add, Rat.cast_mul]
        ring
  · rintro ⟨realPart, imaginaryCoefficient, point_re, point_im⟩
    have point_eq : point = ((realPart + imaginaryCoefficient : ℚ) : ℂ) +
        ((2 * imaginaryCoefficient : ℚ) : ℂ) * omega := by
      apply Complex.ext <;>
        simp [point_re, point_im, omega, Complex.mul_re, Complex.mul_im] <;> ring
    rw [point_eq]
    exact eisensteinField.add_mem (SubfieldClass.ratCast_mem eisensteinField _)
      (eisensteinField.mul_mem (SubfieldClass.ratCast_mem eisensteinField _)
        (Subfield.subset_closure (Set.mem_singleton omega)))

theorem mem_eisensteinField_iff_rational_coordinates (point : ℂ) :
    point ∈ eisensteinField ↔ ∃ firstCoordinate secondCoordinate : ℚ,
      point = (firstCoordinate : ℂ) + (secondCoordinate : ℂ) * omega := by
  constructor
  · intro point_mem
    obtain ⟨realPart, imaginaryCoefficient, point_re, point_im⟩ :=
      (mem_eisensteinField_iff_rational_parts point).mp point_mem
    refine ⟨realPart + imaginaryCoefficient, 2 * imaginaryCoefficient, ?_⟩
    apply Complex.ext <;>
      simp [point_re, point_im, omega, Complex.mul_re, Complex.mul_im] <;> ring
  · rintro ⟨firstCoordinate, secondCoordinate, rfl⟩
    exact eisensteinField.add_mem (SubfieldClass.ratCast_mem eisensteinField _)
      (eisensteinField.mul_mem (SubfieldClass.ratCast_mem eisensteinField _)
        (Subfield.subset_closure (Set.mem_singleton omega)))

theorem exp_mem_eisensteinField_iff_rational_trigonometric (angle : ℝ) :
    Complex.exp ((angle : ℂ) * Complex.I) ∈ eisensteinField ↔
      (∃ cosine : ℚ, Real.cos angle = (cosine : ℝ)) ∧
      (∃ sineCoefficient : ℚ, Real.sin angle / Real.sqrt 3 = (sineCoefficient : ℝ)) := by
  rw [mem_eisensteinField_iff_rational_parts]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have sqrt_three_ne : Real.sqrt 3 ≠ 0 := by positivity
  constructor
  · rintro ⟨cosine, sineCoefficient, cosine_eq, sine_eq⟩
    exact ⟨⟨cosine, cosine_eq⟩, ⟨sineCoefficient, by rw [sine_eq]; field_simp⟩⟩
  · rintro ⟨⟨cosine, cosine_eq⟩, ⟨sineCoefficient, sine_eq⟩⟩
    exact ⟨cosine, sineCoefficient, cosine_eq, (div_eq_iff sqrt_three_ne).mp sine_eq⟩

theorem tan_half_eq_sin_div_one_add_cos (angle : ℝ)
    (angle_nonneg : 0 ≤ angle) (angle_le : angle ≤ Real.pi / 3) :
    Real.tan (angle / 2) = Real.sin angle / (1 + Real.cos angle) := by
  have half_cos_pos : 0 < Real.cos (angle / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have twice_half : 2 * (angle / 2) = angle := by ring
  have denominator_pos : 0 < 1 + Real.cos angle := by
    rw [← twice_half, Real.cos_two_mul]
    nlinarith [sq_pos_of_pos half_cos_pos]
  rw [Real.tan_eq_sin_div_cos, div_eq_div_iff (ne_of_gt half_cos_pos)
    (ne_of_gt denominator_pos)]
  rw [← twice_half, Real.sin_two_mul, Real.cos_two_mul]
  ring

theorem exp_mem_eisensteinField_iff_rational_halfAngle (angle : ℝ)
    (angle_nonneg : 0 ≤ angle) (angle_le : angle ≤ Real.pi / 3) :
    Complex.exp ((angle : ℂ) * Complex.I) ∈ eisensteinField ↔
      ∃ halfAngle : ℚ, Real.tan (angle / 2) / Real.sqrt 3 = (halfAngle : ℝ) := by
  have sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have sqrt_three_ne : Real.sqrt 3 ≠ 0 := by positivity
  have cosine_pos : 0 < Real.cos angle := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  rw [exp_mem_eisensteinField_iff_rational_trigonometric]
  constructor
  · rintro ⟨⟨cosine, cosine_eq⟩, ⟨sineCoefficient, sine_eq⟩⟩
    refine ⟨sineCoefficient / (1 + cosine), ?_⟩
    rw [tan_half_eq_sin_div_one_add_cos angle angle_nonneg angle_le]
    rw [div_right_comm, sine_eq, cosine_eq]
    push_cast
    rfl
  · rintro ⟨halfAngle, halfAngle_eq⟩
    have tangent_eq : Real.tan (angle / 2) = (halfAngle : ℝ) * Real.sqrt 3 :=
      (div_eq_iff sqrt_three_ne).mp halfAngle_eq
    have tangent_sq : Real.tan (angle / 2) ^ 2 = 3 * (halfAngle : ℝ) ^ 2 := by
      rw [tangent_eq, mul_pow, sqrt_three_sq]
      ring
    constructor
    · refine ⟨(1 - 3 * halfAngle ^ 2) / (1 + 3 * halfAngle ^ 2), ?_⟩
      rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq angle (by linarith)]
      rw [tangent_sq]
      push_cast
      rfl
    · refine ⟨2 * halfAngle / (1 + 3 * halfAngle ^ 2), ?_⟩
      rw [Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq, tangent_sq, tangent_eq]
      push_cast
      field_simp

theorem halfAngle_mem_interval (angle : ℝ)
    (angle_nonneg : 0 ≤ angle) (angle_le : angle ≤ Real.pi / 3) :
    Real.tan (angle / 2) / Real.sqrt 3 ∈ Set.Icc 0 (1 / 3 : ℝ) := by
  have sqrt_three_pos : 0 < Real.sqrt 3 := by positivity
  have sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · exact div_nonneg
      (Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith)
        (by linarith [Real.pi_pos])) (le_of_lt sqrt_three_pos)
  · have tangent_le : Real.tan (angle / 2) ≤ Real.tan (Real.pi / 6) := by
      apply Real.strictMonoOn_tan.monotoneOn
      · constructor <;> linarith [Real.pi_pos]
      · constructor <;> linarith [Real.pi_pos]
      · linarith
    rw [Real.tan_pi_div_six] at tangent_le
    apply (div_le_iff₀ sqrt_three_pos).mpr
    have inverse_eq : 1 / Real.sqrt 3 = (1 / 3 : ℝ) * Real.sqrt 3 := by
      apply (div_eq_iff (ne_of_gt sqrt_three_pos)).mpr
      nlinarith [sqrt_three_sq]
    rwa [← inverse_eq]

theorem angle_eq_arctan_halfAngle (angle : ℝ)
    (angle_nonneg : 0 ≤ angle) (angle_le : angle ≤ Real.pi / 3) :
    angle = 2 * Real.arctan
      (Real.sqrt 3 * (Real.tan (angle / 2) / Real.sqrt 3)) := by
  have sqrt_three_ne : Real.sqrt 3 ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ sqrt_three_ne]
  rw [Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  ring

/-- The coprime integer parametrisation uses precisely the bounds in the paper. -/
theorem rational_halfAngle_iff_coprime_parametrisation (angle : ℝ)
    (angle_nonneg : 0 ≤ angle) (angle_le : angle ≤ Real.pi / 3) :
    (∃ halfAngle : ℚ, Real.tan (angle / 2) / Real.sqrt 3 = (halfAngle : ℝ)) ↔
      ∃ firstCoordinate secondCoordinate : ℤ,
        IsCoprime firstCoordinate secondCoordinate ∧ 0 ≤ firstCoordinate ∧
        0 ≤ 2 * secondCoordinate ∧ 2 * secondCoordinate ≤ firstCoordinate ∧
        angle = 2 * Real.arctan
          (Real.sqrt 3 * (secondCoordinate : ℝ) /
            (2 * (firstCoordinate : ℝ) - (secondCoordinate : ℝ))) := by
  constructor
  · rintro ⟨halfAngle, halfAngle_eq⟩
    have halfAngle_bounds := halfAngle_mem_interval angle angle_nonneg angle_le
    rw [halfAngle_eq] at halfAngle_bounds
    have halfAngle_nonneg : (0 : ℚ) ≤ halfAngle := by exact_mod_cast halfAngle_bounds.1
    have halfAngle_le : halfAngle ≤ (1 / 3 : ℚ) := by
      have real_bound : (halfAngle : ℝ) * 3 ≤ 1 := by linarith [halfAngle_bounds.2]
      have rational_bound : halfAngle * 3 ≤ (1 : ℚ) := by exact_mod_cast real_bound
      linarith
    let slope : ℚ := 2 * halfAngle / (1 + halfAngle)
    have slope_nonneg : 0 ≤ slope := by dsimp [slope]; positivity
    have slope_le : slope ≤ 1 / 2 := by
      dsimp [slope]
      apply (div_le_iff₀ (by linarith : 0 < 1 + halfAngle)).mpr
      linarith
    have denominator_pos : (0 : ℚ) < slope.den := by exact_mod_cast slope.den_pos
    have numerator_eq : (slope.num : ℚ) = slope * slope.den :=
      (div_eq_iff (ne_of_gt denominator_pos)).mp slope.num_div_den
    have numerator_nonneg : 0 ≤ slope.num := Rat.num_nonneg.mpr slope_nonneg
    have numerator_le : 2 * slope.num ≤ (slope.den : ℤ) := by
      have scaled_bound := mul_le_mul_of_nonneg_right slope_le (le_of_lt denominator_pos)
      have : (2 : ℚ) * slope.num ≤ slope.den := by rw [numerator_eq]; linarith
      exact_mod_cast this
    have quotient_eq : (slope.num : ℚ) / (2 * (slope.den : ℚ) - slope.num) = halfAngle := by
      have divisor_pos : 0 < 2 * (slope.den : ℚ) - slope.num := by
        have : (2 : ℚ) * slope.num ≤ slope.den := by exact_mod_cast numerator_le
        linarith
      apply (div_eq_iff (ne_of_gt divisor_pos)).mpr
      have slope_eq : slope * (1 + halfAngle) = 2 * halfAngle := by
        dsimp [slope]
        exact div_mul_cancel₀ _ (by linarith)
      nlinarith [congrArg (fun value : ℚ => value * slope.den) slope_eq]
    refine ⟨slope.den, slope.num, ?_, by positivity, by omega, numerator_le, ?_⟩
    · apply Int.isCoprime_iff_nat_coprime.mpr
      simpa using slope.reduced.symm
    · rw [angle_eq_arctan_halfAngle angle angle_nonneg angle_le, halfAngle_eq]
      congr 2
      have quotient_real : (slope.num : ℝ) / (2 * (slope.den : ℝ) - slope.num) =
          (halfAngle : ℝ) := by exact_mod_cast quotient_eq
      simp only [Int.cast_natCast]
      rw [mul_div_assoc, quotient_real]
  · rintro ⟨firstCoordinate, secondCoordinate, _, _, _, _, angle_eq⟩
    refine ⟨(secondCoordinate : ℚ) / (2 * (firstCoordinate : ℚ) - secondCoordinate), ?_⟩
    rw [angle_eq]
    have half_eq : 2 * Real.arctan
        (Real.sqrt 3 * (secondCoordinate : ℝ) /
          (2 * (firstCoordinate : ℝ) - (secondCoordinate : ℝ))) / 2 =
        Real.arctan (Real.sqrt 3 * (secondCoordinate : ℝ) /
          (2 * (firstCoordinate : ℝ) - (secondCoordinate : ℝ))) := by ring
    rw [half_eq, Real.tan_arctan]
    push_cast
    have sqrt_three_ne : Real.sqrt 3 ≠ 0 := by positivity
    field_simp

theorem exp_mem_eisensteinField_iff_coprime_parametrisation (angle : ℝ)
    (angle_nonneg : 0 ≤ angle) (angle_le : angle ≤ Real.pi / 3) :
    Complex.exp ((angle : ℂ) * Complex.I) ∈ eisensteinField ↔
      ∃ firstCoordinate secondCoordinate : ℤ,
        IsCoprime firstCoordinate secondCoordinate ∧ 0 ≤ firstCoordinate ∧
        0 ≤ 2 * secondCoordinate ∧ 2 * secondCoordinate ≤ firstCoordinate ∧
        angle = 2 * Real.arctan
          (Real.sqrt 3 * (secondCoordinate : ℝ) /
            (2 * (firstCoordinate : ℝ) - (secondCoordinate : ℝ))) :=
  (exp_mem_eisensteinField_iff_rational_halfAngle angle angle_nonneg angle_le).trans
    (rational_halfAngle_iff_coprime_parametrisation angle angle_nonneg angle_le)

end MoireAngles
