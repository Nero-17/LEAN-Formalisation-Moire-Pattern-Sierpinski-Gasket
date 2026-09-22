import MoireAngles
import MoireFiniteType
import MoireDeterminization

namespace MoireSection2Results

open MoireEisenstein MoireGeometry

/-- The geometric lattice inclusion in condition (4) of Proposition 2.6. -/
theorem resonant_iff_rotated_lattice_inclusion (angle : ℝ) :
    Complex.exp (angle * Complex.I) ∈ eisensteinField ↔
      ∃ q : ℤ, 0 < q ∧
        rotation angle '' (eisensteinLattice : Set ℂ) ⊆
          (fun point : ℂ => (q : ℂ)⁻¹ * point) '' (eisensteinLattice : Set ℂ) := by
  rw [MoireFiniteType.field_iff_lattice_multiplier]
  constructor
  · rintro ⟨q, positive, inclusion⟩
    refine ⟨q, positive, ?_⟩
    rintro _ ⟨point, point_mem, rfl⟩
    refine ⟨(q : ℂ) * (Complex.exp (angle * Complex.I) * point),
      inclusion point point_mem, ?_⟩
    have q_ne : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
    change (q : ℂ)⁻¹ * ((q : ℂ) * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ q_ne, one_mul]
    rfl
  · rintro ⟨q, positive, inclusion⟩
    refine ⟨q, positive, ?_⟩
    intro point point_mem
    obtain ⟨imagePoint, image_mem, image_eq⟩ := inclusion ⟨point, point_mem, rfl⟩
    change (q : ℂ)⁻¹ * imagePoint = Complex.exp (angle * Complex.I) * point at image_eq
    have q_ne : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
    rw [← image_eq, ← mul_assoc, mul_inv_cancel₀ q_ne, one_mul]
    exact image_mem

/-- Definition 2.2 gives a finite deterministic graph at every resonant angle. -/
theorem resonant_reachable_states_finite (angle : ℝ)
    (resonant : Complex.exp (angle * Complex.I) ∈ eisensteinField) :
    {state | MoireDeterminization.ReachableState vertex gasket (rotation angle) state}.Finite :=
  MoireDeterminization.reachableStates_finite_of_finite_liveReachable angle
    (MoireFiniteType.resonant_implies_finite_type angle resonant)

/-- The countability part of Corollary 2.8 for the manuscript's angle interval. -/
theorem resonant_angles_countable :
    {angle : ℝ | 0 ≤ angle ∧ angle ≤ Real.pi / 3 ∧
      Complex.exp (angle * Complex.I) ∈ eisensteinField}.Countable := by
  apply (Set.countable_range (fun parameter : ℚ =>
    2 * Real.arctan (Real.sqrt 3 * (parameter : ℝ)))).mono
  rintro angle ⟨nonneg, upper, resonant⟩
  obtain ⟨parameter, parameter_eq⟩ :=
    (MoireAngles.exp_mem_eisensteinField_iff_rational_halfAngle angle nonneg upper).mp resonant
  refine ⟨parameter, ?_⟩
  dsimp only
  rw [← parameter_eq]
  exact (MoireAngles.angle_eq_arctan_halfAngle angle nonneg upper).symm

end MoireSection2Results
