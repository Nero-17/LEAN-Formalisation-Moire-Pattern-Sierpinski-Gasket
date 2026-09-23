import MoirePrefixGeometry

namespace MoireSeparationGeometry

open MoireGeometry MoireEisenstein MoireSection2

def determinant (first second : ℂ) : ℝ :=
  first.re * second.im - first.im * second.re

def projection (direction point : ℂ) : ℝ := (star direction * point).re

theorem determinant_mul (factor first second : ℂ) :
    determinant (factor * first) (factor * second) =
      Complex.normSq factor * determinant first second := by
  simp only [determinant, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

/-- A determinant can be bounded using the two projections onto any one unit direction. -/
theorem determinant_le_projections (direction first second : ℂ) (unit : ‖direction‖ = 1) :
    |determinant first second| ≤
      |projection direction first| * ‖second‖ + ‖first‖ * |projection direction second| := by
  have conjugate_norm : ‖star direction‖ = 1 := by simpa using unit
  have norm_square : Complex.normSq (star direction) = 1 := by
    rw [Complex.normSq_eq_norm_sq, conjugate_norm]
    norm_num
  have determinant_eq := determinant_mul (star direction) first second
  rw [norm_square, one_mul] at determinant_eq
  rw [← determinant_eq]
  unfold determinant projection
  calc
    _ ≤ |(star direction * first).re * (star direction * second).im| +
        |(star direction * first).im * (star direction * second).re| := abs_sub _ _
    _ = |(star direction * first).re| * |(star direction * second).im| +
        |(star direction * first).im| * |(star direction * second).re| := by rw [abs_mul, abs_mul]
    _ ≤ |(star direction * first).re| * ‖star direction * second‖ +
        ‖star direction * first‖ * |(star direction * second).re| := by
      gcongr
      · exact Complex.abs_im_le_norm _
      · exact Complex.abs_im_le_norm _
    _ = _ := by rw [norm_mul, norm_mul, conjugate_norm, one_mul, one_mul]

theorem lattice_norm_sq (point : LatticePoint) :
    ‖complexCoordinates point‖ ^ 2 =
      ((point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2 : ℤ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [complexCoordinates, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, Complex.mul_re, Complex.mul_im, omega_re, omega_im]
  push_cast
  have sqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

/-- The minimum nonzero Eisenstein-lattice length is one. -/
theorem one_le_norm_lattice {point : LatticePoint} (nonzero : point ≠ 0) :
    1 ≤ ‖complexCoordinates point‖ := by
  have coordinate_nonzero : complexCoordinates point ≠ 0 := by
    intro equality
    exact nonzero (complexCoordinates_injective (equality.trans (map_zero _).symm))
  have positive := sq_pos_of_pos (norm_pos_iff.mpr coordinate_nonzero)
  rw [lattice_norm_sq] at positive
  have integer_positive : 0 < point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2 := by
    exact_mod_cast positive
  have integer_lower : 1 ≤ point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2 := integer_positive
  have real_lower : (1 : ℝ) ≤ ((point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast integer_lower
  rw [← lattice_norm_sq] at real_lower
  nlinarith [norm_nonneg (complexCoordinates point)]

end MoireSeparationGeometry
