import MoireTriangleBounds
import MoireCharacterisation

namespace MoirePiThirdGeometry

open MoireGeometry MoireSection2 MoireEisenstein MoireTriangleBounds

theorem rotation_coordinates (point : LatticePoint) :
    rotation (Real.pi / 3) (complexCoordinates point) =
      complexCoordinates (rotatePiThird point) := by
  have sqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  apply Complex.ext <;>
    simp [rotation, complexCoordinates, rotatePiThird, omega, Complex.mul_re, Complex.mul_im,
      piThird_exp_re, piThird_exp_im] <;>
    ring_nf <;> simp [sqrt_sq] <;> ring

theorem coordinate_bounds (point : LatticePoint)
    (bounds : ∀ digit, linearCoordinate digit (complexCoordinates point) ≤ 2) :
    2 * point.1 - point.2 ≤ 2 ∧ 2 * point.2 - point.1 ≤ 2 ∧
      -point.1 - point.2 ≤ 2 := by
  have sqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have first := bounds 0
  have second := bounds 1
  have third := bounds 2
  simp [linearCoordinate, complexCoordinates, omega] at first second third
  have second_eq : -(point.1 : ℝ) + point.2 * (1 / 2) +
      Real.sqrt 3 * ((point.2 : ℝ) * (Real.sqrt 3 / 2)) = 2 * point.2 - point.1 := by
    ring_nf
    rw [sqrt_sq]
    ring
  constructor
  · exact_mod_cast (show 2 * (point.1 : ℝ) - point.2 ≤ 2 by linarith)
  constructor
  · have square_product : (point.2 : ℝ) * Real.sqrt 3 * Real.sqrt 3 = point.2 * 3 := by
      nlinarith [congrArg (fun value : ℝ => (point.2 : ℝ) * value) sqrt_sq]
    exact_mod_cast (show 2 * (point.2 : ℝ) - point.1 ≤ 2 by nlinarith)
  · have square_product : (point.2 : ℝ) * Real.sqrt 3 * Real.sqrt 3 = point.2 * 3 := by
      nlinarith [congrArg (fun value : ℝ => (point.2 : ℝ) * value) sqrt_sq]
    exact_mod_cast (show -(point.1 : ℝ) - point.2 ≤ 2 by nlinarith)

/-- Exhaustive integer calculation, independently of any geometric liveness test. -/
theorem checked_successor_bound : ∀ carry : piThirdCarries, ∀ digits : Fin 3 × Fin 3,
    (2 * (nextCarryPiThird carry digits).1 - (nextCarryPiThird carry digits).2 ≤ 2 ∧
      2 * (nextCarryPiThird carry digits).2 - (nextCarryPiThird carry digits).1 ≤ 2 ∧
      -(nextCarryPiThird carry digits).1 - (nextCarryPiThird carry digits).2 ≤ 2) →
      nextCarryPiThird carry digits ∈ piThirdCarries := by decide

theorem successor_coordinates (carry : LatticePoint) (blueDigit redDigit : Fin 3) :
    (2 : ℚ) • complexCoordinates carry + vertex blueDigit -
      rotation (Real.pi / 3) (vertex redDigit) =
        complexCoordinates (nextCarryPiThird carry (blueDigit, redDigit)) := by
  rw [← MoireConcrete.complexCoordinates_vertex blueDigit,
    ← MoireConcrete.complexCoordinates_vertex redDigit, rotation_coordinates]
  simp [nextCarryPiThird, map_add, map_sub, two_smul]
  abel

theorem live_successor_mem (carry : LatticePoint) (carry_mem : carry ∈ piThirdCarries)
    (blueDigit redDigit : Fin 3)
    (live : (shiftedIntersection gasket (rotation (Real.pi / 3))
      ((2 : ℚ) • complexCoordinates carry + vertex blueDigit -
        rotation (Real.pi / 3) (vertex redDigit))).Nonempty) :
    nextCarryPiThird carry (blueDigit, redDigit) ∈ piThirdCarries := by
  rw [successor_coordinates] at live
  exact checked_successor_bound ⟨carry, carry_mem⟩ (blueDigit, redDigit)
    (coordinate_bounds _ (live_piThird_coordinate_bound _ live))

theorem parent_live_of_child_live (angle : ℝ) (displacement : ℂ)
    (blueDigit redDigit : Fin 3)
    (child_live : (shiftedIntersection gasket (rotation angle)
      ((2 : ℚ) • displacement + vertex blueDigit - rotation angle (vertex redDigit))).Nonempty) :
    (shiftedIntersection gasket (rotation angle) displacement).Nonempty := by
  obtain ⟨point, point_mem⟩ := child_live
  rw [gasket_intersection_recursion]
  exact ⟨cornerMap vertex blueDigit point,
    Set.mem_iUnion.mpr ⟨blueDigit, Set.mem_iUnion.mpr ⟨redDigit, point, point_mem, rfl⟩⟩⟩

theorem candidate_returns_or_zero : ∀ carry : piThirdCarries,
    carry.val = (0, 0) ∨ ∃ digits : Fin 3 × Fin 3, nextCarryPiThird carry digits = (0, 0) := by
  decide

theorem candidate_live (carry : LatticePoint) (carry_mem : carry ∈ piThirdCarries) :
    (shiftedIntersection gasket (rotation (Real.pi / 3)) (complexCoordinates carry)).Nonempty := by
  have zero_live := MoireNonempty.initial_intersection_nonempty (Real.pi / 3)
    (by positivity) le_rfl
  rcases candidate_returns_or_zero ⟨carry, carry_mem⟩ with zero | ⟨⟨blueDigit, redDigit⟩, returns⟩
  · change carry = (0, 0) at zero
    subst carry
    simpa [complexCoordinates] using zero_live
  · apply parent_live_of_child_live (Real.pi / 3) (complexCoordinates carry) blueDigit redDigit
    rw [successor_coordinates, returns]
    simpa [complexCoordinates] using zero_live

theorem live_successor_iff (carry : LatticePoint) (carry_mem : carry ∈ piThirdCarries)
    (blueDigit redDigit : Fin 3) :
    (shiftedIntersection gasket (rotation (Real.pi / 3))
      ((2 : ℚ) • complexCoordinates carry + vertex blueDigit -
        rotation (Real.pi / 3) (vertex redDigit))).Nonempty ↔
      nextCarryPiThird carry (blueDigit, redDigit) ∈ piThirdCarries := by
  constructor
  · exact live_successor_mem carry carry_mem blueDigit redDigit
  · intro successor_mem
    rw [successor_coordinates]
    exact candidate_live _ successor_mem

theorem carryStep_eq (displacement : ℂ) (digits : Fin 3 × Fin 3) :
    MoireLatticeWords.carryStep eisensteinLattice latticeCoordinates
      (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) displacement digits =
      (2 : ℚ) • displacement + vertex digits.1 - rotation (Real.pi / 3) (vertex digits.2) := by
  simp [MoireLatticeWords.carryStep, ← MoireConcrete.complexCoordinates_vertex,
    rotation, Algebra.smul_def]

theorem reachable_live_coordinates (displacement : ℂ)
    (reachable : MoireLatticeWords.ReachableCarry eisensteinLattice latticeCoordinates
      (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) displacement)
    (live : (shiftedIntersection gasket (rotation (Real.pi / 3)) displacement).Nonempty) :
    ∃ carry ∈ piThirdCarries, displacement = complexCoordinates carry := by
  revert live
  induction reachable with
  | initial =>
      intro _
      exact ⟨(0, 0), by decide, by simp [complexCoordinates]⟩
  | @step displacement previous digits inductionHypothesis =>
      intro live
      rw [carryStep_eq] at live ⊢
      have parent_live := parent_live_of_child_live (Real.pi / 3) displacement digits.1 digits.2 live
      obtain ⟨carry, carry_mem, rfl⟩ := inductionHypothesis parent_live
      exact ⟨nextCarryPiThird carry digits,
        live_successor_mem carry carry_mem digits.1 digits.2 live,
        successor_coordinates carry digits.1 digits.2⟩

theorem candidate_incoming_or_zero : ∀ carry : piThirdCarries,
    carry.val = (0, 0) ∨ ∃ digits : Fin 3 × Fin 3, nextCarryPiThird (0, 0) digits = carry.val := by
  decide

theorem candidate_reachable (carry : LatticePoint) (carry_mem : carry ∈ piThirdCarries) :
    MoireLatticeWords.ReachableCarry eisensteinLattice latticeCoordinates
      (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) (complexCoordinates carry) := by
  rcases candidate_incoming_or_zero ⟨carry, carry_mem⟩ with zero | ⟨digits, incoming⟩
  · change carry = (0, 0) at zero
    subst carry
    simpa [complexCoordinates] using
      (MoireLatticeWords.ReachableCarry.initial (lattice := eisensteinLattice)
        (coordinates := latticeCoordinates) (rotation := Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)))
  · have first := MoireLatticeWords.ReachableCarry.step
      (MoireLatticeWords.ReachableCarry.initial (lattice := eisensteinLattice)
        (coordinates := latticeCoordinates) (rotation := Complex.exp ((Real.pi / 3 : ℝ) * Complex.I))) digits
    rw [carryStep_eq] at first
    have zero_eq : (0 : ℂ) = complexCoordinates (0, 0) := by simp [complexCoordinates]
    rw [zero_eq, successor_coordinates, incoming] at first
    exact first

theorem liveReachable_piThird_eq :
    MoireLatticeWords.liveReachable eisensteinLattice latticeCoordinates
      (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) gasket =
      complexCoordinates '' (piThirdCarries : Set LatticePoint) := by
  ext displacement
  constructor
  · rintro ⟨reachable, live⟩
    rw [← MoireConcrete.rotation_eq_mulLeft] at live
    obtain ⟨carry, carry_mem, equality⟩ := reachable_live_coordinates displacement reachable live
    exact ⟨carry, carry_mem, equality.symm⟩
  · rintro ⟨carry, carry_mem, rfl⟩
    refine ⟨candidate_reachable carry carry_mem, ?_⟩
    rw [← MoireConcrete.rotation_eq_mulLeft]
    exact candidate_live carry carry_mem

end MoirePiThirdGeometry
