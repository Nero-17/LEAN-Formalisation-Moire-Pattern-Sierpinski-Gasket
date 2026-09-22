import MoireSection2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Labelled digits and a counterexample to the manuscript's set alphabet

At zero rotation there are nine ordered pairs but only seven distinct
displacement vectors. They cannot be interchanged in counting formulae.
All finite certificates in this file use kernel reduction, not `native_decide`.
-/

namespace MoireCounting

open MoireSection2

def zeroRotationDigits : Finset LatticePoint :=
  Finset.univ.image (fun digits : Fin 3 × Fin 3 =>
    vertexPiThird digits.1 - vertexPiThird digits.2)

theorem zeroRotationDigits_card : zeroRotationDigits.card = 7 := by decide

theorem labelledDigits_card : Fintype.card (Fin 3 × Fin 3) = 9 := by decide

/-- This is a counterexample to counting labelled words by distinct vectors. -/
theorem distinct_digits_do_not_count_pairs :
    zeroRotationDigits.card ≠ Fintype.card (Fin 3 × Fin 3) := by decide

/-- Coincident displacement vectors can come from different child pairs. -/
theorem three_zero_digits :
    (Finset.univ.filter (fun digits : Fin 3 × Fin 3 =>
      vertexPiThird digits.1 - vertexPiThird digits.2 = 0)).card = 3 := by decide

section PairIntersections

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Every pair of first-level cells meets when the two gaskets coincide.
The shared point is the midpoint of the two corresponding vertices. -/
theorem firstLevel_pair_intersects (vertices : Fin 3 → V) (set : Set V)
    (vertices_mem : ∀ digit, vertices digit ∈ set) (blueDigit redDigit : Fin 3) :
    ((cornerMap vertices blueDigit '' set) ∩
      (cornerMap vertices redDigit '' set)).Nonempty := by
  refine ⟨cornerMap vertices blueDigit (vertices redDigit),
    ⟨vertices redDigit, vertices_mem redDigit, rfl⟩,
    vertices blueDigit, vertices_mem blueDigit, ?_⟩
  simp [cornerMap, add_comm]

end PairIntersections

/-- The two-step growth recurrence of the four-carry graph at `π/3`.
This sequence is not claimed here to be an independently constructed
geometric intersection count: the finite graph-to-geometry bridge is separate. -/
def piThirdGraphCount : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | n + 2 => 6 * piThirdGraphCount n

theorem piThirdGraphCount_even (level : ℕ) :
    piThirdGraphCount (2 * level) = 6 ^ level := by
  induction level with
  | zero => rfl
  | succ level inductionHypothesis =>
      rw [Nat.mul_succ, piThirdGraphCount, inductionHypothesis, pow_succ]
      omega

theorem piThirdGraphCount_odd (level : ℕ) :
    piThirdGraphCount (2 * level + 1) = 6 ^ (level + 1) := by
  induction level with
  | zero => rfl
  | succ level inductionHypothesis =>
      have index_eq : 2 * (level + 1) + 1 = (2 * level + 1) + 2 := by omega
      rw [index_eq, piThirdGraphCount, inductionHypothesis, pow_succ]
      omega

theorem piThirdGraphCount_even_ratio (level : ℕ) :
    (piThirdGraphCount (2 * level + 1) : ℚ) /
      piThirdGraphCount (2 * level) = 6 := by
  rw [piThirdGraphCount_even, piThirdGraphCount_odd]
  push_cast
  rw [pow_succ]
  field_simp

theorem piThirdGraphCount_odd_ratio (level : ℕ) :
    (piThirdGraphCount (2 * level + 2) : ℚ) /
      piThirdGraphCount (2 * level + 1) = 1 := by
  rw [show 2 * level + 2 = 2 * (level + 1) by omega,
    piThirdGraphCount_even, piThirdGraphCount_odd]
  exact div_self (by positivity)

end MoireCounting
