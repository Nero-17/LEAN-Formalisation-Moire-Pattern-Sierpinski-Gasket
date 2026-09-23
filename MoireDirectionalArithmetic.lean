import MoireDirectionalResonance
import MoireAngles

namespace MoireDirectionalArithmetic
open MoireDirectionalResonance MoireGeometry MoireSeparationGeometry MoireEisenstein
open MoireAngles MoireSection2

theorem determinant_quotient (first second : ℂ) (nonzero : second ≠ 0) (angle : ℝ) :
    determinant first (rotation angle second) = 0 ↔
      determinant (first / second) (rotation angle 1) = 0 := by
  have identity := determinant_mul second (first / second) (rotation angle 1)
  have cancel : second * (first / second) = first := by field_simp
  have rotate : second * rotation angle 1 = rotation angle second := by
    change second * (Complex.exp _ * 1) = Complex.exp _ * second
    ring
  rw [cancel, rotate] at identity
  rw [identity, mul_eq_zero]
  simp [Complex.normSq_eq_zero, nonzero]

theorem directionallyResonant_iff_field_direction (angle : ℝ) :
    DirectionallyResonant angle ↔ ∃ point ∈ eisensteinField, point ≠ 0 ∧
      determinant point (rotation angle 1) = 0 := by
  constructor
  · rintro ⟨first, second, first_ne, second_ne, aligned⟩
    have first_nonzero : complexCoordinates first ≠ 0 := fun h =>
      first_ne (complexCoordinates_injective (h.trans (map_zero _).symm))
    have second_nonzero : complexCoordinates second ≠ 0 := fun h =>
      second_ne (complexCoordinates_injective (h.trans (map_zero _).symm))
    refine ⟨complexCoordinates first / complexCoordinates second,
      eisensteinField.div_mem
        (eisensteinLattice_le_eisensteinField (complexCoordinates_mem_eisensteinLattice first))
        (eisensteinLattice_le_eisensteinField (complexCoordinates_mem_eisensteinLattice second)),
      div_ne_zero first_nonzero second_nonzero, ?_⟩
    exact (determinant_quotient _ _ second_nonzero angle).mp aligned
  · rintro ⟨point, member, nonzero, aligned⟩
    change point ∈ (eisensteinField : Set ℂ) at member
    rw [← ratioClosure_eq_eisensteinField] at member
    obtain ⟨numerator, denominator, denominator_ne, quotient⟩ := member
    obtain ⟨first, first_eq⟩ := latticeCoordinates_surjective numerator
    obtain ⟨second, second_eq⟩ := latticeCoordinates_surjective denominator
    have first_coe : complexCoordinates first = (numerator : ℂ) := congrArg Subtype.val first_eq
    have second_coe : complexCoordinates second = (denominator : ℂ) := congrArg Subtype.val second_eq
    have second_nonzero : complexCoordinates second ≠ 0 := by simpa [second_coe] using denominator_ne
    have numerator_ne : (numerator : ℂ) ≠ 0 := by
      intro zero
      apply nonzero
      rw [quotient, zero, zero_div]
    refine ⟨first, second, ?_, ?_, ?_⟩
    · intro zero; apply numerator_ne; rw [← first_coe, zero, map_zero]
    · intro zero; apply second_nonzero; rw [zero, map_zero]
    · apply (determinant_quotient _ _ second_nonzero angle).mpr
      simpa only [first_coe, second_coe, ← quotient] using aligned

theorem determinant_rotation_one (point : ℂ) (angle : ℝ) :
    determinant point (rotation angle 1) = point.re * Real.sin angle - point.im * Real.cos angle := by
  simp [determinant, rotation, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The extended-slope formulation avoids Lean's convention `tan (pi/2) = 0`. -/
theorem directionallyResonant_iff_slope (angle : ℝ) : DirectionallyResonant angle ↔
    Real.cos angle = 0 ∨ ∃ slope : ℚ, Real.tan angle / Real.sqrt 3 = (slope : ℝ) := by
  rw [directionallyResonant_iff_field_direction]
  have sqrt_ne : Real.sqrt 3 ≠ 0 := by positivity
  constructor
  · rintro ⟨point, member, nonzero, aligned⟩
    by_cases cosine_zero : Real.cos angle = 0
    · exact Or.inl cosine_zero
    right
    obtain ⟨realPart, imaginaryPart, real_eq, imaginary_eq⟩ :=
      (mem_eisensteinField_iff_rational_parts point).mp member
    rw [determinant_rotation_one, real_eq, imaginary_eq] at aligned
    have real_ne : (realPart : ℝ) ≠ 0 := by
      intro zero
      have imaginary_zero : (imaginaryPart : ℝ) = 0 := by
        have product : (imaginaryPart : ℝ) * Real.sqrt 3 * Real.cos angle = 0 := by
          rw [zero] at aligned; linarith
        exact (mul_eq_zero.mp (mul_eq_zero.mp product |>.resolve_right cosine_zero)).resolve_right sqrt_ne
      apply nonzero
      apply Complex.ext <;> simp [real_eq, imaginary_eq, zero, imaginary_zero]
    refine ⟨imaginaryPart / realPart, ?_⟩
    push_cast
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [aligned]
  · intro slope
    rcases slope with cosine_zero | ⟨slope, slope_eq⟩
    · refine ⟨⟨0, Real.sqrt 3⟩,
        (mem_eisensteinField_iff_rational_parts _).mpr ⟨0, 1, by simp, by simp⟩, ?_, ?_⟩
      · intro zero; have := congrArg Complex.im zero; simpa using this
      · rw [determinant_rotation_one]; simp [cosine_zero]
    · by_cases cosine_zero : Real.cos angle = 0
      · refine ⟨⟨0, Real.sqrt 3⟩,
          (mem_eisensteinField_iff_rational_parts _).mpr ⟨0, 1, by simp, by simp⟩, ?_, ?_⟩
        · intro zero; have := congrArg Complex.im zero; simpa using this
        · rw [determinant_rotation_one]; simp [cosine_zero]
      · refine ⟨⟨1, (slope : ℝ) * Real.sqrt 3⟩,
          (mem_eisensteinField_iff_rational_parts _).mpr ⟨1, slope, by simp, rfl⟩,
          by intro zero; have := congrArg Complex.re zero; norm_num at this, ?_⟩
        rw [determinant_rotation_one]
        simp only [one_mul]
        rw [Real.tan_eq_sin_div_cos] at slope_eq
        apply sub_eq_zero.mpr
        field_simp at slope_eq
        nlinarith [slope_eq]

end MoireDirectionalArithmetic
