import MoireDyadicConcentration
import Mathlib.Order.LiminfLimsup

namespace MoireLqDimension

open MoireDyadicConcentration MeasureTheory Filter
open scoped ENNReal

/-- The normalized logarithm of the actual dyadic moment. The value at level
zero is immaterial for the limit inferior. -/
noncomputable def scaleDimension (measure : Measure ℂ) (q : ℝ) (length : ℕ) : ℝ :=
  -Real.log (dyadicMoment measure length q).toReal / ((q - 1) * length * Real.log 2)

/-- The manuscript's Lq dimension, using its half-open dyadic square partition. -/
noncomputable def lqDimension (measure : Measure ℂ) (q : ℝ) : ℝ :=
  liminf (scaleDimension measure q) atTop

theorem scaleDimension_nonneg (measure : Measure ℂ) [IsProbabilityMeasure measure]
    (q : ℝ) (q_gt_one : 1 < q) (length : ℕ) : 0 ≤ scaleDimension measure q length := by
  have moment_le : (dyadicMoment measure length q).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by
      simpa using dyadicMoment_le_one measure length q q_gt_one.le)
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (ENNReal.toReal_nonneg) moment_le))
    (by positivity : 0 ≤ (q - 1) * (length : ℝ) * Real.log 2)

/-- The limit inferior supplies an eventual estimate at every sufficiently
fine scale, not merely along a subsequence. -/
theorem eventually_moment_le_exp (measure : Measure ℂ) [IsProbabilityMeasure measure]
    (q : ℝ) (q_gt_one : 1 < q) (dimension : ℝ)
    (below : dimension < lqDimension measure q) :
    ∀ᶠ length : ℕ in atTop, (dyadicMoment measure length q).toReal ≤
      Real.exp (-dimension * (q - 1) * length * Real.log 2) := by
  have bounded : atTop.IsBoundedUnder (· ≥ ·) (scaleDimension measure q) :=
    isBoundedUnder_of ⟨0, scaleDimension_nonneg measure q q_gt_one⟩
  have eventual := eventually_lt_of_lt_liminf below bounded
  filter_upwards [eventual, eventually_gt_atTop 0] with length bound length_pos
  have denominator_pos : 0 < (q - 1) * (length : ℝ) * Real.log 2 := by positivity
  have log_bound := (lt_div_iff₀ denominator_pos).mp bound
  have moment_pos : 0 < (dyadicMoment measure length q).toReal :=
    ENNReal.toReal_pos (ne_of_gt (dyadicMoment_pos measure length q))
      (ne_top_of_le_ne_top (by simp) (dyadicMoment_le_one measure length q q_gt_one.le))
  calc
    _ = Real.exp (Real.log (dyadicMoment measure length q).toReal) := (Real.exp_log moment_pos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem eventually_ball_mass_le_exp (measure : Measure ℂ) [IsProbabilityMeasure measure]
    (q : ℝ) (q_gt_one : 1 < q) (dimension : ℝ)
    (below : dimension < lqDimension measure q) :
    ∀ᶠ length : ℕ in atTop,
      (measure (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length))).toReal ≤
        81 * (Real.exp (-dimension * ((q - 1) / q) * Real.log 2)) ^ length := by
  have q_pos : 0 < q := by linarith
  filter_upwards [eventually_moment_le_exp measure q q_gt_one dimension below] with length moment_bound
  have moment_finite : dyadicMoment measure length q ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (dyadicMoment_le_one measure length q q_gt_one.le)
  have real_bound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr q_pos.le) moment_finite))
    (small_ball_mass_le_moment measure length q q_pos)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow] at real_bound
  calc
    _ ≤ 81 * (dyadicMoment measure length q).toReal ^ q⁻¹ := real_bound
    _ ≤ 81 * (Real.exp (-dimension * (q - 1) * length * Real.log 2)) ^ q⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ENNReal.toReal_nonneg moment_bound (inv_nonneg.mpr q_pos.le)) (by norm_num)
    _ = _ := by
      rw [← Real.exp_mul, ← Real.exp_nat_mul]
      congr 2
      simp only [div_eq_mul_inv]
      ring

end MoireLqDimension
