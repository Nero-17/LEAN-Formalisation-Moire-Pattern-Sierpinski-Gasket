import MoireBoxEquality
import MoirePiThirdTable
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace MoireSection2Complete

open MoireGeometry MoireSection2 MoireDeterminization MoireActualUpper MoireBoxDimension
open scoped ENNReal Matrix.Norms.Operator

/-- Theorem 2.4: resonance yields the actual Hausdorff and both box dimensions.
Finiteness is constructed from resonance, and no dimension formula is assumed. -/
theorem resonant_dimensions (angle : ℝ) (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3)
    (resonant : Complex.exp (angle * Complex.I) ∈ MoireEisenstein.eisensteinField) :
    letI : Fintype (States angle) :=
      (MoireSection2Results.resonant_reachable_states_finite angle resonant).fintype
    letI : DecidableEq (States angle) := Classical.decEq _
    dimH (shiftedIntersection gasket (rotation angle) 0) = ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) ∧
    lowerBoxDimension (shiftedIntersection gasket (rotation angle) 0) = ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) ∧
    upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) = ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) := by
  letI : Fintype (States angle) :=
    (MoireSection2Results.resonant_reachable_states_finite angle resonant).fintype
  letI : DecidableEq (States angle) := Classical.decEq _
  exact ⟨MoireHausdorffEquality.hausdorff_dimension_eq angle nonneg upper,
    MoireBoxEquality.box_dimensions_eq angle nonneg upper⟩

theorem piThird_actual_spectral_radius [Fintype (States (Real.pi / 3))]
    [DecidableEq (States (Real.pi / 3))] :
    spectralRadius ℂ (A := Matrix (States (Real.pi / 3)) (States (Real.pi / 3)) ℂ)
      ((adjacencyMatrix vertex gasket (rotation (Real.pi / 3))).map (Nat.cast : ℕ → ℂ)) =
        ENNReal.ofReal (Real.sqrt 6) := by
  have radius_eq :
      spectralRadius ℂ (A := Matrix (Fin 4) (Fin 4) ℂ)
        ((Matrix.reindexAlgEquiv ℂ ℂ MoirePiThirdTable.stateEquiv.symm)
          ((adjacencyMatrix vertex gasket (rotation (Real.pi / 3))).map (Nat.cast : ℕ → ℂ))) =
      spectralRadius ℂ (A := Matrix (States (Real.pi / 3)) (States (Real.pi / 3)) ℂ)
        ((adjacencyMatrix vertex gasket (rotation (Real.pi / 3))).map (Nat.cast : ℕ → ℂ)) := by
    unfold spectralRadius
    rw [AlgEquiv.spectrum_eq]
  rw [← radius_eq]
  exact MoirePiThirdTable.geometric_matrix_spectral_radius

/-- Example 2.5 is a consequence of the actual dimension theorem and the
verified four-state matrix, not merely a simplification of a proposed formula. -/
theorem piThird_dimensions :
    dimH (shiftedIntersection gasket (rotation (Real.pi / 3)) 0) =
      ENNReal.ofReal (Real.log 6 / Real.log 4) ∧
    lowerBoxDimension (shiftedIntersection gasket (rotation (Real.pi / 3)) 0) =
      ENNReal.ofReal (Real.log 6 / Real.log 4) ∧
    upperBoxDimension (shiftedIntersection gasket (rotation (Real.pi / 3)) 0) =
      ENNReal.ofReal (Real.log 6 / Real.log 4) := by
  letI : Fintype (States (Real.pi / 3)) := Fintype.ofEquiv (Fin 4) MoirePiThirdTable.stateEquiv
  letI : DecidableEq (States (Real.pi / 3)) := Classical.decEq _
  have hausdorff := MoireHausdorffEquality.hausdorff_dimension_eq (Real.pi / 3)
    (by positivity) le_rfl
  have boxes := MoireBoxEquality.box_dimensions_eq (Real.pi / 3) (by positivity) le_rfl
  rw [piThird_actual_spectral_radius, ENNReal.toReal_ofReal (Real.sqrt_nonneg 6)] at hausdorff boxes
  have exponent : Real.log (Real.sqrt 6) / Real.log 2 = Real.log 6 / Real.log 4 := by
    rw [Real.log_sqrt (by norm_num)]
    have four : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log ((2 : ℝ) ^ 2) := congrArg Real.log (by norm_num)
        _ = 2 * Real.log 2 := Real.log_pow (2 : ℝ) 2
    rw [four]
    ring
  rw [exponent] at hausdorff boxes
  exact ⟨hausdorff, boxes⟩

end MoireSection2Complete
