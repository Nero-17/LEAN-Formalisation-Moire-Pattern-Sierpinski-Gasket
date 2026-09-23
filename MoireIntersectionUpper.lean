import MoireIntersectionCounting

namespace MoireIntersectionUpper

open MoireGeometry MoireSection2 MoireDifferenceMeasure MoireIntersectionCounting
open MoireBoxDimension MeasureTheory Filter
open scoped ENNReal NNReal

/-- A real-valued form of the exact geometric probability estimate. -/
theorem count_le_nine_pow_mass (angle : ℝ) (length : ℕ) :
    (intersectionCount angle length : ℝ) ≤ (9 : ℝ) ^ length *
      (differenceMeasure angle (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length))).toReal := by
  have bound := ENNReal.toReal_mono (measure_ne_top _ _)
    (count_le_small_ball angle length)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat] at bound
  rw [inv_pow, ← div_eq_mul_inv] at bound
  have result := (div_le_iff₀ (by positivity : (0 : ℝ) < 9 ^ length)).mp bound
  simpa only [mul_comm] using result

/-- The geometric part of Theorem 3's proof, with its remaining analytic input
stated directly for the actual difference measure rather than a scalar dimension. -/
theorem upperExponent_of_small_ball (angle : ℝ) (dimension : ℝ≥0)
    (constant : ℝ) (positive : 0 < constant)
    (mass_bound : ∀ᶠ length : ℕ in atTop,
      (differenceMeasure angle (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length))).toReal ≤
        constant * (((2 : ℝ) ^ (dimension : ℝ)) / 9) ^ length) :
    UpperExponent (shiftedIntersection gasket (rotation angle) 0) dimension := by
  refine ⟨constant, positive, ?_⟩
  filter_upwards [mass_bound] with length bound
  refine ⟨intersectionCenters angle length, intersectionCenters_cover angle length, ?_⟩
  rw [intersectionCenters_length]
  calc
    (intersectionCount angle length : ℝ) ≤ (9 : ℝ) ^ length *
        (differenceMeasure angle (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length))).toReal :=
      count_le_nine_pow_mass angle length
    _ ≤ (9 : ℝ) ^ length * (constant * (((2 : ℝ) ^ (dimension : ℝ)) / 9) ^ length) :=
      mul_le_mul_of_nonneg_left bound (by positivity)
    _ = constant * ((2 : ℝ) ^ (dimension : ℝ)) ^ length := by
      rw [div_pow]
      field_simp

theorem upperBox_le_of_small_ball (angle : ℝ) (dimension : ℝ) (nonneg : 0 ≤ dimension)
    (mass_bound : ∀ exponent : ℝ≥0, dimension < (exponent : ℝ) →
      ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ length : ℕ in atTop,
        (differenceMeasure angle (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length))).toReal ≤
          constant * (((2 : ℝ) ^ (exponent : ℝ)) / 9) ^ length) :
    upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) ≤ ENNReal.ofReal dimension := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro bound greater
  obtain ⟨exponent, exponent_gt, exponent_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp greater
  obtain ⟨constant, positive, estimate⟩ := mass_bound exponent
    ((ENNReal.ofReal_lt_coe_iff nonneg).mp exponent_gt)
  exact (iInf₂_le exponent (upperExponent_of_small_ball angle exponent constant positive estimate)).trans
    exponent_lt.le

end MoireIntersectionUpper
