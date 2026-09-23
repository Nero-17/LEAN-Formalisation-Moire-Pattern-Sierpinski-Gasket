import MoireLqDimension

namespace MoireUpperFromLq

open MoireGeometry MoireSection2 MoireDifferenceMeasure MoireLqDimension
open MoireBoxDimension MoireIntersectionUpper MeasureTheory Filter
open scoped ENNReal NNReal

theorem upperExponent_of_lq (angle q : ℝ) (q_gt_one : 1 < q)
    (dimension : ℝ) (below : dimension < lqDimension (differenceMeasure angle) q)
    (exponent : ℝ≥0)
    (large : Real.log 9 / Real.log 2 - dimension * ((q - 1) / q) ≤ (exponent : ℝ)) :
    UpperExponent (shiftedIntersection gasket (rotation angle) 0) exponent := by
  have log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have rate_bound : Real.exp (-dimension * ((q - 1) / q) * Real.log 2) ≤
      (2 : ℝ) ^ (exponent : ℝ) / 9 := by
    have scaled := mul_le_mul_of_nonneg_right large log_two_pos.le
    rw [sub_mul, div_mul_cancel₀ _ log_two_pos.ne'] at scaled
    have rhs_positive : 0 < (2 : ℝ) ^ (exponent : ℝ) / 9 := by positivity
    calc
      _ ≤ Real.exp (Real.log ((2 : ℝ) ^ (exponent : ℝ) / 9)) := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow (by norm_num)]
        nlinarith
      _ = _ := Real.exp_log rhs_positive
  apply upperExponent_of_small_ball angle exponent 81 (by norm_num)
  filter_upwards [eventually_ball_mass_le_exp (differenceMeasure angle) q q_gt_one dimension below]
    with length bound
  exact bound.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.exp_pos _).le rate_bound _) (by norm_num))

theorem choose_exponents (symbolic exponent : ℝ) (greater : symbolic - 2 < exponent) :
    ∃ q : ℝ, 1 < q ∧ ∃ dimension : ℝ, dimension < 2 ∧
      symbolic - dimension * ((q - 1) / q) ≤ exponent := by
  let gap := exponent - (symbolic - 2)
  have gap_pos : 0 < gap := sub_pos.mpr greater
  let q := 1 + 4 / gap
  have q_gt_one : 1 < q := by
    have := div_pos (by norm_num : (0 : ℝ) < 4) gap_pos
    dsimp [q]
    linarith
  have q_pos : 0 < q := by linarith
  have error : 2 / q < gap / 2 := by
    rw [div_lt_iff₀ q_pos]
    have cancel : (4 / gap) * gap = 4 := by field_simp
    dsimp [q]
    nlinarith
  refine ⟨q, q_gt_one, 2 - gap / 2, by linarith, ?_⟩
  have fraction : (2 - gap / 2) / q ≤ 2 / q :=
    div_le_div_of_nonneg_right (by linarith) q_pos.le
  have identity : (2 - gap / 2) * ((q - 1) / q) =
      (2 - gap / 2) - (2 - gap / 2) / q := by field_simp
  rw [identity]
  dsimp [gap] at error fraction ⊢
  linarith

theorem transverse_exponent_nonneg : 0 ≤ Real.log 9 / Real.log 2 - 2 := by
  have positive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have log_four : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := congrArg Real.log (by norm_num)
      _ = _ := Real.log_pow (2 : ℝ) 2
  have bound := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 9)
  rw [log_four] at bound
  have := (le_div_iff₀ positive).mpr bound
  linarith

/-- The final geometric implication of Section 3, now for the actual intersection
and actual dyadic Lq dimension. The analytic full-dimension statement is an
explicit remaining hypothesis, not a theorem or a new axiom. -/
theorem upperBox_le_of_full_lq (angle : ℝ)
    (full : ∀ q : ℝ, 1 < q → lqDimension (differenceMeasure angle) q = 2) :
    upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) ≤
      ENNReal.ofReal (Real.log 9 / Real.log 2 - 2) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro bound greater
  obtain ⟨exponent, exponent_gt, exponent_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp greater
  obtain ⟨q, q_gt_one, dimension, dimension_lt, large⟩ :=
    choose_exponents (Real.log 9 / Real.log 2) exponent
      ((ENNReal.ofReal_lt_coe_iff transverse_exponent_nonneg).mp exponent_gt)
  have below : dimension < lqDimension (differenceMeasure angle) q := by rw [full q q_gt_one]; exact dimension_lt
  exact (iInf₂_le exponent (upperExponent_of_lq angle q q_gt_one dimension below exponent large)).trans
    exponent_lt.le

theorem ae_upperBox_le_of_ae_full_lq
    (full : ∀ᵐ angle : ℝ, ∀ q : ℝ, 1 < q → lqDimension (differenceMeasure angle) q = 2) :
    ∀ᵐ angle : ℝ, upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) ≤
      ENNReal.ofReal (Real.log 9 / Real.log 2 - 2) := by
  filter_upwards [full] with angle full_at_angle
  exact upperBox_le_of_full_lq angle full_at_angle

end MoireUpperFromLq
