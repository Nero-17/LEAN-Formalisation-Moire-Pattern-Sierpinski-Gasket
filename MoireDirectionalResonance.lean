import MoireDeterminantSublevel

namespace MoireDirectionalResonance
open MoireGeometry MoireSeparationGeometry MoireDeterminantSublevel
open MoireEisenstein MoireSection2 MeasureTheory

/-- Alignment of two nonzero lattice directions, not commensurability of the lattices. -/
def DirectionallyResonant (angle : ℝ) : Prop :=
  ∃ first second : LatticePoint, first ≠ 0 ∧ second ≠ 0 ∧
    determinant (complexCoordinates first) (rotation angle (complexCoordinates second)) = 0

theorem determinant_zero_iff (first second : ℂ) (first_nonzero : first ≠ 0)
    (second_nonzero : second ≠ 0) (angle : ℝ) :
    determinant first (rotation angle second) = 0 ↔
      ∃ k : ℤ, angle = k * Real.pi - Complex.arg (star first * second) := by
  rw [determinant_rotation_sine, mul_eq_zero]
  simp only [mul_eq_zero, norm_eq_zero, first_nonzero, second_nonzero, false_or]
  rw [Real.sin_eq_zero_iff]
  constructor <;> rintro ⟨k, equality⟩ <;> exact ⟨k, by linarith⟩

theorem directionallyResonant_iff (angle : ℝ) : DirectionallyResonant angle ↔
    ∃ first second : LatticePoint, first ≠ 0 ∧ second ≠ 0 ∧
      ∃ k : ℤ, angle = k * Real.pi -
        Complex.arg (star (complexCoordinates first) * complexCoordinates second) := by
  unfold DirectionallyResonant
  apply exists_congr
  intro first
  apply exists_congr
  intro second
  by_cases first_zero : first = 0
  · simp [first_zero]
  by_cases second_zero : second = 0
  · simp [second_zero]
  rw [determinant_zero_iff _ _
    (fun h => first_zero (complexCoordinates_injective (h.trans (map_zero _).symm)))
    (fun h => second_zero (complexCoordinates_injective (h.trans (map_zero _).symm)))]

theorem countable_directionallyResonant : Set.Countable {angle | DirectionallyResonant angle} := by
  apply (Set.countable_range (fun indices : LatticePoint × LatticePoint × ℤ =>
    (indices.2.2 : ℝ) * Real.pi -
      Complex.arg (star (complexCoordinates indices.1) * complexCoordinates indices.2.1))).mono
  intro angle member
  obtain ⟨first, second, _, _, k, equality⟩ := (directionallyResonant_iff angle).mp member
  exact ⟨(first, second, k), equality.symm⟩

theorem ae_not_directionallyResonant : ∀ᵐ angle : ℝ, ¬ DirectionallyResonant angle := by
  rw [ae_iff]
  simpa using countable_directionallyResonant.measure_zero (μ := volume)

end MoireDirectionalResonance
