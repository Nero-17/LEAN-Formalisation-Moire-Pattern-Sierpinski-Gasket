import MoireGeometry
import MoireEisenstein
import MoireCounting
import MoireFibre
import MoireEndpoint
import Mathlib.Tactic.FinCases

/-! # Concrete manuscript results and a concrete counting obstruction -/

namespace MoireConcrete

open MoireSection2 MoireGeometry MoireEisenstein MoireLatticeWords

noncomputable section

theorem complexCoordinates_vertex (digit : Fin 3) :
    complexCoordinates (vertexPiThird digit) = vertex digit := by
  fin_cases digit
  · exact complexCoordinates_vertex_zero
  · exact complexCoordinates_vertex_one
  · exact complexCoordinates_vertex_two

theorem fieldVertex_eq_vertex :
    fieldVertex eisensteinLattice latticeCoordinates = vertex := by
  funext digit
  exact complexCoordinates_vertex digit

theorem rotation_eq_mulLeft (angle : ℝ) :
    MoireGeometry.rotation angle = LinearMap.mulLeft ℚ (Complex.exp (angle * Complex.I)) := rfl

/-- The finite-type converse for the actual gasket, with precisely the
nonempty-intersection and finite-live-reachable assumptions in the paper. -/
theorem finite_type_implies_commensurable (angle : ℝ)
    (intersection_nonempty :
      (shiftedIntersection gasket (MoireGeometry.rotation angle) 0).Nonempty)
    (finite_live_displacements :
      (liveReachable eisensteinLattice latticeCoordinates
        (Complex.exp (angle * Complex.I)) gasket).Finite) :
    Complex.exp (angle * Complex.I) ∈ eisensteinField := by
  apply rotation_mem_eisensteinField_of_finite_liveReachable
    (Complex.exp (angle * Complex.I)) gasket
  · rw [fieldVertex_eq_vertex]
    exact gasket_selfSimilar
  · exact intersection_nonempty
  · exact finite_live_displacements

/-- Proposition `prop:fibre` for the actual complex-plane gasket. -/
theorem gasket_zeroFibre_hausdorffDim (angle : ℝ) :
    dimH (MoireFibre.zeroFibre gasket (MoireGeometry.rotation angle)) =
      dimH (gasket ∩ MoireGeometry.rotation angle '' gasket) :=
  MoireFibre.zeroFibre_hausdorffDim gasket (MoireGeometry.rotation angle)
    (rotation_isometry angle)

/-- All nine actual first-level gasket pairs meet at zero relative rotation. -/
theorem zero_angle_all_firstLevel_pairs_meet (digits : Fin 3 × Fin 3) :
    ((cornerMap vertex digits.1 '' gasket) ∩
      (cornerMap vertex digits.2 '' gasket)).Nonempty :=
  MoireCounting.firstLevel_pair_intersects vertex gasket vertex_mem_gasket digits.1 digits.2

/-- This counts actual set intersections, not an abstract graph recurrence. -/
def zeroAngleFirstLevelPairs : Finset (Fin 3 × Fin 3) := by
  classical
  exact Finset.univ.filter (fun digits =>
    ((cornerMap vertex digits.1 '' gasket) ∩
      (cornerMap vertex digits.2 '' gasket)).Nonempty)

theorem zeroAngleFirstLevelPairs_eq_univ : zeroAngleFirstLevelPairs = Finset.univ := by
  classical
  apply Finset.filter_true_of_mem
  intro digits _
  exact zero_angle_all_firstLevel_pairs_meet digits

theorem zeroAngleFirstLevelPairs_card : zeroAngleFirstLevelPairs.card = 9 := by
  rw [zeroAngleFirstLevelPairs_eq_univ]
  decide

/-- The manuscript's unlabelled complex displacement alphabet at zero angle. -/
def zeroAngleDisplacements : Finset ℂ := by
  classical
  exact Finset.univ.image (fun digits : Fin 3 × Fin 3 => vertex digits.1 - vertex digits.2)

theorem zeroAngleDisplacements_eq_image :
    zeroAngleDisplacements = MoireCounting.zeroRotationDigits.image complexCoordinates := by
  classical
  simp only [zeroAngleDisplacements, MoireCounting.zeroRotationDigits, Finset.image_image]
  congr 1
  funext digits
  simp [complexCoordinates_vertex]

theorem zeroAngleDisplacements_card : zeroAngleDisplacements.card = 7 := by
  classical
  rw [zeroAngleDisplacements_eq_image,
    Finset.card_image_of_injective _ complexCoordinates_injective]
  exact MoireCounting.zeroRotationDigits_card

/-- Every digit is in the actual difference set, witnessed by gasket vertices. -/
theorem zeroAngleDisplacements_mem_difference (displacement : ℂ)
    (displacement_mem : displacement ∈ zeroAngleDisplacements) :
    ∃ redPoint ∈ gasket, ∃ bluePoint ∈ gasket, displacement = redPoint - bluePoint := by
  classical
  obtain ⟨digits, _, rfl⟩ := Finset.mem_image.mp displacement_mem
  exact ⟨vertex digits.1, vertex_mem_gasket digits.1,
    vertex digits.2, vertex_mem_gasket digits.2, rfl⟩

/-- The unlabelled alphabet with the paper's actual difference-set endpoint test. -/
def zeroAngleLegalDisplacements : Finset ℂ := by
  classical
  exact zeroAngleDisplacements.filter (fun displacement =>
        ∃ redPoint ∈ gasket, ∃ bluePoint ∈ gasket,
          displacement = redPoint - bluePoint)

/-- Kernel-checked refutation of the unlabelled count in `cor:legal-endpoint`,
already at θ=0 and n=1. All seven alphabet elements satisfy the endpoint test. -/
theorem manuscript_unlabelled_count_is_false :
    zeroAngleFirstLevelPairs.card ≠ zeroAngleLegalDisplacements.card := by
  classical
  unfold zeroAngleLegalDisplacements
  rw [Finset.filter_true_of_mem (fun displacement displacement_mem =>
    zeroAngleDisplacements_mem_difference displacement displacement_mem),
    zeroAngleFirstLevelPairs_card, zeroAngleDisplacements_card]
  decide

end
end MoireConcrete
