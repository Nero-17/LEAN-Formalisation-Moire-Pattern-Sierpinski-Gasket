import MoireSmallBalls

namespace MoireMassDistribution

open MeasureTheory MeasureTheory.Measure Metric Filter Topology
open scoped ENNReal

private theorem power_swap (length : ℕ) (dimension : ℝ) :
    ((1 / 2 : ℝ) ^ length) ^ dimension = ((1 / 2 : ℝ) ^ dimension) ^ length := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_comm (length : ℝ), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Dyadic ball estimates control every sufficiently small set, including sets
of diameter zero. This is the mass-distribution step in Euclidean space. -/
theorem measure_le_diameter_power (measure : Measure ℂ) (dimension constant : ℝ)
    (dimension_pos : 0 < dimension) (constant_pos : 0 < constant)
    (balls : ∀ length center, measure (closedBall center ((1 / 2 : ℝ) ^ length)) ≤
      ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ length) ^ dimension))
    (set : Set ℂ) (small : ediam set ≤ 1) :
    measure set ≤ ENNReal.ofReal (constant * (2 : ℝ) ^ dimension) * (ediam set) ^ dimension := by
  have finite : ediam set ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top small
  have diam_le_one : diam set ≤ 1 := by
    simpa only [diam, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top small
  rcases set.eq_empty_or_nonempty with empty | ⟨center, center_mem⟩
  · simp [empty]
  have contained : ∀ length, diam set ≤ (1 / 2 : ℝ) ^ length →
      set ⊆ closedBall center ((1 / 2 : ℝ) ^ length) := by
    intro length bound point member
    exact (dist_le_diam_of_mem' finite member center_mem).trans bound
  by_cases diameter_zero : diam set = 0
  · have bound : ∀ length, measure set ≤
        ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ dimension) ^ length) := by
      intro length
      rw [← power_swap]
      exact (measure_mono (contained length (by rw [diameter_zero]; positivity))).trans (balls length center)
    have converges : Tendsto (fun length : ℕ =>
        ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ dimension) ^ length)) atTop (𝓝 0) := by
      have real_limit := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) dimension)
        (Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) dimension_pos)).const_mul constant
      simpa using ENNReal.tendsto_ofReal real_limit
    exact (ge_of_tendsto' converges bound).trans bot_le
  · have diameter_pos : 0 < diam set := lt_of_le_of_ne diam_nonneg (Ne.symm diameter_zero)
    obtain ⟨length, lower, upper⟩ := exists_nat_pow_near_of_lt_one diameter_pos diam_le_one
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have scale_bound : (1 / 2 : ℝ) ^ length ≤ 2 * diam set := by
      rw [pow_succ] at lower
      linarith
    calc
      measure set ≤ measure (closedBall center ((1 / 2 : ℝ) ^ length)) := measure_mono (contained length upper)
      _ ≤ ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ length) ^ dimension) := balls length center
      _ ≤ ENNReal.ofReal (constant * (2 * diam set) ^ dimension) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) scale_bound dimension_pos.le) constant_pos.le)
      _ = ENNReal.ofReal (constant * (2 : ℝ) ^ dimension) * (ediam set) ^ dimension := by
        rw [Real.mul_rpow (by norm_num) diam_nonneg, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg diam_nonneg dimension_pos.le]
        rw [diam, ENNReal.ofReal_toReal finite]

/-- A nonzero measure with dyadic s-power ball decay certifies an actual
Hausdorff-dimension lower bound. -/
theorem le_dimH_of_dyadic_mass (measure : Measure ℂ) (dimension constant : ℝ)
    (dimension_pos : 0 < dimension) (constant_pos : 0 < constant)
    (balls : ∀ length center, measure (closedBall center ((1 / 2 : ℝ) ^ length)) ≤
      ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ length) ^ dimension))
    (set : Set ℂ) (nonzero : measure set ≠ 0) : ENNReal.ofReal dimension ≤ dimH set := by
  have dominated : measure ≤ ENNReal.ofReal (constant * (2 : ℝ) ^ dimension) • hausdorffMeasure dimension := by
    apply (le_mkMetric (fun radius => ENNReal.ofReal (constant * (2 : ℝ) ^ dimension) * radius ^ dimension)
      measure 1 (by norm_num) (measure_le_diameter_power measure dimension constant dimension_pos constant_pos balls)).trans
    exact mkMetric_mono_smul ENNReal.ofReal_ne_top
      (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
      (Eventually.of_forall fun _ => le_rfl)
  have nonzero_hausdorff : hausdorffMeasure dimension set ≠ 0 := by
    intro zero
    have bound := dominated set
    rw [Measure.smul_apply, zero, smul_zero] at bound
    exact nonzero (le_antisymm bound bot_le)
  have result := le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨dimension, dimension_pos.le⟩) nonzero_hausdorff
  rw [← ENNReal.ofReal_coe_nnreal] at result
  exact result

end MoireMassDistribution
