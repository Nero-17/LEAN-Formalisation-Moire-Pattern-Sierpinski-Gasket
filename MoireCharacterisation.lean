import MoireDensity
import MoireNonempty

namespace MoireCharacterisation

open MoireGeometry MoireEisenstein MoireLatticeWords

/-- Corollary 2.9's equivalence, with initial nonemptiness now proved internally. -/
theorem finite_type_iff_resonant (angle : ℝ)
    (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3) :
    (liveReachable eisensteinLattice latticeCoordinates
      (Complex.exp (angle * Complex.I)) gasket).Finite ↔
      Complex.exp (angle * Complex.I) ∈ eisensteinField :=
  MoireFiniteType.finite_type_iff_resonant_of_nonempty angle
    (MoireNonempty.initial_intersection_nonempty angle nonneg upper)

theorem finite_type_angles_countable :
    {angle : ℝ | 0 ≤ angle ∧ angle ≤ Real.pi / 3 ∧
      (liveReachable eisensteinLattice latticeCoordinates
        (Complex.exp (angle * Complex.I)) gasket).Finite}.Countable := by
  apply MoireSection2Results.resonant_angles_countable.mono
  rintro angle ⟨nonneg, upper, finite_type⟩
  exact ⟨nonneg, upper, (finite_type_iff_resonant angle nonneg upper).mp finite_type⟩

theorem closure_finite_type_angles :
    closure {angle : ℝ | 0 ≤ angle ∧ angle ≤ Real.pi / 3 ∧
      (liveReachable eisensteinLattice latticeCoordinates
        (Complex.exp (angle * Complex.I)) gasket).Finite} = Set.Icc 0 (Real.pi / 3) := by
  convert MoireDensity.closure_resonant_angles using 2
  ext angle
  constructor
  · rintro ⟨nonneg, upper, finite_type⟩
    exact ⟨nonneg, upper, (finite_type_iff_resonant angle nonneg upper).mp finite_type⟩
  · rintro ⟨nonneg, upper, resonant⟩
    exact ⟨nonneg, upper, (finite_type_iff_resonant angle nonneg upper).mpr resonant⟩

end MoireCharacterisation
