import MoireAlmostEverySeparation
import Mathlib.MeasureTheory.Group.Measure

namespace MoireSeparationPeriodicity

open MoireGeometry MoireWordPacking MoireProjectionSeparation MoireAlmostEveryProjection
open MoireAlmostEverySeparation MeasureTheory Filter

theorem ae_of_periodic_on_interval (property : ℝ → Prop) (period : ℝ) (positive : 0 < period)
    (periodic : ∀ angle : ℝ, ∀ integer : ℤ, property (angle + integer * period) ↔ property angle)
    (on_interval : ∀ᵐ angle : ℝ, 0 ≤ angle → angle ≤ period → property angle) :
    ∀ᵐ angle : ℝ, property angle := by
  have shifted : ∀ integer : ℤ, ∀ᵐ angle : ℝ,
      0 ≤ angle + (-(integer : ℝ) * period) → angle + (-(integer : ℝ) * period) ≤ period →
        property (angle + (-(integer : ℝ) * period)) := by
    intro integer
    exact (measurePreserving_add_right volume (-(integer : ℝ) * period)).quasiMeasurePreserving.tendsto_ae
      on_interval
  filter_upwards [ae_all_iff.mpr shifted] with angle good
  let integer : ℤ := ⌊angle / period⌋
  have floor_lower := Int.floor_le (angle / period)
  have floor_upper := Int.lt_floor_add_one (angle / period)
  have cancel : angle / period * period = angle := div_mul_cancel₀ angle positive.ne'
  have lower : 0 ≤ angle + (-(integer : ℝ) * period) := by
    nlinarith [mul_le_mul_of_nonneg_right floor_lower positive.le]
  have upper : angle + (-(integer : ℝ) * period) ≤ period := by
    nlinarith [mul_lt_mul_of_pos_right floor_upper positive]
  have result := (periodic (angle + (-(integer : ℝ) * period)) integer).mpr (good integer lower upper)
  convert result using 1 <;> congr 1 <;> ring

theorem rotation_add_period (angle : ℝ) (integer : ℤ) (point : ℂ) :
    rotation (angle + integer * (2 * Real.pi)) point = rotation angle point := by
  have exponents : (((angle + integer * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      (angle : ℂ) * Complex.I + (integer : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  change Complex.exp _ * point = Complex.exp _ * point
  rw [exponents, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The manuscript's first separation lemma for Lebesgue-almost every real angle. -/
theorem ae_difference_exponential_separation : ∀ᵐ angle : ℝ, DifferenceExponentiallySeparated angle := by
  apply ae_of_periodic_on_interval _ (2 * Real.pi) (by positivity)
  · intro angle integer
    simp only [DifferenceExponentiallySeparated, differenceTranslation, rotation_add_period]
  · exact MoireAlmostEverySeparation.ae_difference_exponential_separation

/-- The manuscript's projected-factor dichotomy, simultaneously in all unit
directions and for Lebesgue-almost every real angle. -/
theorem ae_projection_dichotomy : ∀ᵐ angle : ℝ,
    ∀ direction : ℂ, ‖direction‖ = 1 →
      ExponentiallySeparated (fun _ word => wordCenter word) direction ∨
      ExponentiallySeparated (fun _ word => rotation angle (wordCenter word)) direction := by
  apply ae_of_periodic_on_interval _ (2 * Real.pi) (by positivity)
  · intro angle integer
    simp only [rotation_add_period]
  · exact MoireAlmostEveryProjection.ae_projection_dichotomy

end MoireSeparationPeriodicity
