import MoireIntersectionUpper
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.Floor

namespace MoireDyadicConcentration

open MeasureTheory
open scoped ENNReal

/-- The index of the half-open dyadic square containing a complex point. -/
noncomputable def dyadicIndex (length : ℕ) (point : ℂ) : ℤ × ℤ :=
  (⌊(2 : ℝ) ^ length * point.re⌋, ⌊(2 : ℝ) ^ length * point.im⌋)

def dyadicCell (length : ℕ) (index : ℤ × ℤ) : Set ℂ :=
  {point | dyadicIndex length point = index}

theorem dyadicCell_measurable (length : ℕ) (index : ℤ × ℤ) :
    MeasurableSet (dyadicCell length index) := by
  have measurable : Measurable (dyadicIndex length) := by unfold dyadicIndex; fun_prop
  exact measurable (measurableSet_singleton index)

theorem sum_cell_mass (measure : Measure ℂ) (length : ℕ) :
    (∑' index : ℤ × ℤ, measure (dyadicCell length index)) = measure Set.univ := by
  have partition : (⋃ index : ℤ × ℤ, dyadicCell length index) = Set.univ := by
    ext point
    simp [dyadicCell]
  rw [← measure_iUnion, partition]
  · intro first second different
    exact Set.disjoint_left.mpr (fun _ first_eq second_eq => different (first_eq.symm.trans second_eq))
  · exact dyadicCell_measurable length

/-- The actual dyadic q-moment, summed over all half-open squares. -/
noncomputable def dyadicMoment (measure : Measure ℂ) (length : ℕ) (q : ℝ) : ℝ≥0∞ :=
  ∑' index : ℤ × ℤ, (measure (dyadicCell length index)) ^ q

theorem dyadicMoment_le_one (measure : Measure ℂ) [IsProbabilityMeasure measure]
    (length : ℕ) (q : ℝ) (q_ge_one : 1 ≤ q) : dyadicMoment measure length q ≤ 1 := by
  calc
    _ ≤ ∑' index : ℤ × ℤ, measure (dyadicCell length index) := by
      apply ENNReal.tsum_le_tsum
      intro index
      simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge
        (show measure (dyadicCell length index) ≤ 1 from prob_le_one) q_ge_one
    _ = 1 := by rw [sum_cell_mass, measure_univ]

theorem dyadicMoment_pos (measure : Measure ℂ) [IsProbabilityMeasure measure]
    (length : ℕ) (q : ℝ) : 0 < dyadicMoment measure length q := by
  have exists_positive : ∃ index : ℤ × ℤ, measure (dyadicCell length index) ≠ 0 := by
    by_contra! all_zero
    have mass := sum_cell_mass measure length
    simp only [all_zero, tsum_zero, measure_univ] at mass
    exact zero_ne_one mass
  obtain ⟨index, nonzero⟩ := exists_positive
  have positive : 0 < (measure (dyadicCell length index)) ^ q :=
    ENNReal.rpow_pos (pos_iff_ne_zero.mpr nonzero) (measure_ne_top _ _)
  exact positive.trans_le (ENNReal.le_tsum index)

theorem cell_mass_le_moment (measure : Measure ℂ) (length : ℕ) (q : ℝ) (positive : 0 < q)
    (index : ℤ × ℤ) :
    measure (dyadicCell length index) ≤ (dyadicMoment measure length q) ^ q⁻¹ := by
  have bound : (measure (dyadicCell length index)) ^ q ≤ dyadicMoment measure length q :=
    ENNReal.le_tsum index
  have rooted := ENNReal.rpow_le_rpow bound (inv_nonneg.mpr positive.le)
  simpa only [← ENNReal.rpow_mul, mul_inv_cancel₀ positive.ne', ENNReal.rpow_one] using rooted

theorem scaled_coordinate_bound (length : ℕ) (point : ℂ) (coordinate : ℝ)
    (coordinate_bound : |coordinate| ≤ ‖point‖)
    (inside : dist point 0 ≤ 4 * (1 / 2 : ℝ) ^ length) :
    |(2 : ℝ) ^ length * coordinate| ≤ 4 := by
  rw [dist_zero_right] at inside
  calc
    |(2 : ℝ) ^ length * coordinate| = (2 : ℝ) ^ length * |coordinate| := by
      rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ (2 : ℝ) ^ length * (4 * (1 / 2 : ℝ) ^ length) :=
      mul_le_mul_of_nonneg_left (coordinate_bound.trans inside) (by positivity)
    _ = 4 := by
      calc
        _ = 4 * ((2 : ℝ) * (1 / 2)) ^ length := by rw [mul_pow]; ring
        _ = 4 := by norm_num

theorem floor_coordinate_bound {coordinate : ℝ} (bound : |coordinate| ≤ 4) :
    ⌊coordinate⌋ ∈ Finset.Icc (-4 : ℤ) 4 := by
  apply Finset.mem_Icc.mpr
  have lower := Int.floor_mono (abs_le.mp bound).1
  have upper := Int.floor_mono (abs_le.mp bound).2
  norm_num at lower upper
  exact ⟨lower, upper⟩

/-- Only 81 level-n squares are needed for the radius-4·2⁻ⁿ ball at zero. -/
theorem small_ball_covered (length : ℕ) :
    Metric.closedBall (0 : ℂ) (4 * (1 / 2 : ℝ) ^ length) ⊆
      ⋃ index ∈ (Finset.Icc (-4 : ℤ) 4).product (Finset.Icc (-4 : ℤ) 4), dyadicCell length index := by
  intro point inside
  refine Set.mem_iUnion.mpr ⟨dyadicIndex length point, Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
  apply Finset.mem_product.mpr
  exact ⟨floor_coordinate_bound (scaled_coordinate_bound length point point.re
      (Complex.abs_re_le_norm point) inside),
    floor_coordinate_bound (scaled_coordinate_bound length point point.im
      (Complex.abs_im_le_norm point) inside)⟩

/-- The concrete Lq-to-small-ball estimate used by the Section 3 covering proof. -/
theorem small_ball_mass_le_moment (measure : Measure ℂ) (length : ℕ) (q : ℝ) (positive : 0 < q) :
    measure (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length)) ≤
      81 * (dyadicMoment measure length q) ^ q⁻¹ := by
  calc
    _ ≤ measure (⋃ index ∈ (Finset.Icc (-4 : ℤ) 4).product (Finset.Icc (-4 : ℤ) 4),
        dyadicCell length index) := measure_mono (small_ball_covered length)
    _ ≤ ∑ index ∈ (Finset.Icc (-4 : ℤ) 4).product (Finset.Icc (-4 : ℤ) 4),
        measure (dyadicCell length index) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _index ∈ (Finset.Icc (-4 : ℤ) 4).product (Finset.Icc (-4 : ℤ) 4),
        (dyadicMoment measure length q) ^ q⁻¹ :=
      Finset.sum_le_sum (fun index _ => cell_mass_le_moment measure length q positive index)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Int.card_Icc]
      norm_num [Int.toNat]

end MoireDyadicConcentration
