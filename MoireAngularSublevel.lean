import MoireSeparationGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace MoireAngularSublevel

open MeasureTheory
open scoped ENNReal

/-- Distance to a multiple of pi is controlled by the sine, with an explicit
nearby integer when the argument lies in the angular range used below. -/
theorem near_multiple_of_pi (x : ℝ) (lower : -2 * Real.pi ≤ x) (upper : x ≤ 4 * Real.pi) :
    ∃ integer ∈ Finset.Icc (-3 : ℤ) 5,
      |x - integer * Real.pi| ≤ Real.pi / 2 * |Real.sin x| := by
  let integer : ℤ := ⌊x / Real.pi + 1 / 2⌋
  have pi_pos := Real.pi_pos
  have integer_lower := Int.floor_le (x / Real.pi + 1 / 2)
  have integer_upper := Int.lt_floor_add_one (x / Real.pi + 1 / 2)
  have cancel : x / Real.pi * Real.pi = x := div_mul_cancel₀ x pi_pos.ne'
  have close : |x - integer * Real.pi| ≤ Real.pi / 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right integer_lower pi_pos.le]
    · nlinarith [mul_lt_mul_of_pos_right integer_upper pi_pos]
  have integer_range : integer ∈ Finset.Icc (-3 : ℤ) 5 := by
    apply Finset.mem_Icc.mpr
    have lower_ratio : (-3 : ℝ) ≤ x / Real.pi + 1 / 2 := by
      have := (le_div_iff₀ pi_pos).mpr lower
      linarith
    have upper_ratio : x / Real.pi + 1 / 2 ≤ (5 : ℝ) := by
      have := (div_le_iff₀ pi_pos).mpr upper
      linarith
    have below := Int.floor_mono lower_ratio
    have above := Int.floor_mono upper_ratio
    norm_num at below above
    exact ⟨below, above⟩
  have sine_eq : |Real.sin (x - integer * Real.pi)| = |Real.sin x| := by
    rw [Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    norm_num
  have sine_bound := Real.mul_abs_le_abs_sin close
  rw [sine_eq] at sine_bound
  refine ⟨integer, integer_range, ?_⟩
  have multiplied := mul_le_mul_of_nonneg_left sine_bound pi_pos.le
  have cancel_two : Real.pi * (2 / Real.pi) = 2 := by field_simp
  nlinarith

/-- A uniform angular sublevel estimate, proved for Lebesgue measure.
The loose constant 9*pi is independent of the phase and threshold. -/
theorem sine_sublevel_volume (phase threshold : ℝ)
    (phase_lower : -2 * Real.pi ≤ phase) (phase_upper : phase ≤ 2 * Real.pi) :
    volume {angle : ℝ | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧
      |Real.sin (angle + phase)| < threshold} ≤ ENNReal.ofReal (9 * Real.pi * threshold) := by
  have covered : {angle : ℝ | 0 ≤ angle ∧ angle ≤ 2 * Real.pi ∧
      |Real.sin (angle + phase)| < threshold} ⊆
      ⋃ integer ∈ Finset.Icc (-3 : ℤ) 5,
        Set.Ioo (integer * Real.pi - phase - Real.pi / 2 * threshold)
          (integer * Real.pi - phase + Real.pi / 2 * threshold) := by
    rintro angle ⟨nonneg, upper, small⟩
    obtain ⟨integer, member, bound⟩ := near_multiple_of_pi (angle + phase) (by linarith) (by linarith)
    have close := bound.trans_lt (mul_lt_mul_of_pos_left small (by positivity : 0 < Real.pi / 2))
    rw [abs_lt] at close
    exact Set.mem_iUnion.mpr ⟨integer, Set.mem_iUnion.mpr ⟨member, by constructor <;> linarith⟩⟩
  calc
    _ ≤ volume (⋃ integer ∈ Finset.Icc (-3 : ℤ) 5,
        Set.Ioo (integer * Real.pi - phase - Real.pi / 2 * threshold)
          (integer * Real.pi - phase + Real.pi / 2 * threshold)) := measure_mono covered
    _ ≤ ∑ integer ∈ Finset.Icc (-3 : ℤ) 5,
        volume (Set.Ioo (integer * Real.pi - phase - Real.pi / 2 * threshold)
          (integer * Real.pi - phase + Real.pi / 2 * threshold)) := measure_biUnion_finset_le _ _
    _ = ∑ _integer ∈ Finset.Icc (-3 : ℤ) 5, ENNReal.ofReal (Real.pi * threshold) := by
      apply Finset.sum_congr rfl
      intro integer _
      rw [Real.volume_Ioo]
      congr 1
      ring
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      norm_num [Int.toNat]
      rw [← ENNReal.ofReal_ofNat 9, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

end MoireAngularSublevel
