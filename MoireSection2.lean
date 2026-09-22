import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Lean.Elab.Tactic.Decide

/-!
# Formalisation of the algebraic core of the carry and finite-type sections

This file verifies the carry identities, the lattice-membership argument, the
finite-state repetition step in the converse theorem, and the complete carry
table for the angle `π / 3`.

The Mauldin--Williams dimension theorem is not currently reproduced here: using
it would require a separate formalisation of graph-directed self-similar sets and
their Hausdorff dimension.  No axiom is introduced for that missing analytic part.
-/

namespace MoireSection2

section CarryAlgebra

variable {ι V : Type*} [AddCommGroup V]

/-- The closed weighted sum `∑ 2^(n-r) d_r` from the paper. -/
def weightedSum : List V → V
  | [] => 0
  | displacement :: remainingDisplacements =>
      (2 ^ remainingDisplacements.length) • displacement +
        weightedSum remainingDisplacements

/-- Appending one digit gives exactly the carry update `c ↦ 2c + d`. -/
theorem weightedSum_append_singleton (displacements : List V) (displacement : V) :
    weightedSum (displacements ++ [displacement]) =
      2 • weightedSum displacements + displacement := by
  induction displacements with
  | nil => simp [weightedSum]
  | cons firstDisplacement remainingDisplacements inductionHypothesis =>
      simp only [List.cons_append, weightedSum, List.length_append,
        List.length_singleton]
      rw [inductionHypothesis]
      rw [pow_succ]
      simp only [mul_nsmul]
      abel

/-- The displacement contributed by one blue/red digit pair. -/
def digitDisplacement (vertex : ι → V) (rotate : V →+ V) (digits : ι × ι) : V :=
  vertex digits.1 - rotate (vertex digits.2)

/-- The level carry in the closed form used in Section 2. -/
def carryClosed (vertex : ι → V) (rotate : V →+ V) (digits : List (ι × ι)) : V :=
  weightedSum (digits.map (digitDisplacement vertex rotate))

/-- The closed carry formula satisfies the recursive update in the paper. -/
theorem carryClosed_append (vertex : ι → V) (rotate : V →+ V)
    (digits : List (ι × ι)) (nextDigits : ι × ι) :
    carryClosed vertex rotate (digits ++ [nextDigits]) =
      2 • carryClosed vertex rotate digits +
        digitDisplacement vertex rotate nextDigits := by
  simp [carryClosed, weightedSum_append_singleton]

/-- Every carry stays in an additive subgroup containing all digit displacements. -/
theorem carryClosed_mem_addSubgroup (vertex : ι → V) (rotate : V →+ V)
    (lattice : AddSubgroup V) (digits : List (ι × ι))
    (digit_mem : ∀ digit ∈ digits, digitDisplacement vertex rotate digit ∈ lattice) :
    carryClosed vertex rotate digits ∈ lattice := by
  induction digits with
  | nil => simp [carryClosed, weightedSum]
  | cons firstDigits remainingDigits inductionHypothesis =>
      simp only [carryClosed, List.map_cons, weightedSum]
      exact lattice.add_mem
        (lattice.nsmul_mem (digit_mem firstDigits (by simp))
          (2 ^ (List.map (digitDisplacement vertex rotate) remainingDigits).length))
        (inductionHypothesis (fun digit digit_in_remainingDigits =>
          digit_mem digit (by simp [digit_in_remainingDigits])))

end CarryAlgebra

section GeometricRecursion

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The affine contraction `Fᵢ(x) = (x + pᵢ) / 2`. -/
def cornerMap (vertex : ι → V) (digit : ι) (point : V) : V :=
  (1 / 2 : ℚ) • (point + vertex digit)

/-- The shifted intersection `E_c = S ∩ (R(S) - c)`. -/
def shiftedIntersection (gasket : Set V) (rotate : Module.End ℚ V) (drift : V) : Set V :=
  {point | point ∈ gasket ∧
    ∃ redPoint ∈ gasket, point = rotate redPoint - drift}

/-- The carry recursion lemma from Section 2, stated for any rational vector
space and any linear rotation. -/
theorem shiftedIntersection_eq_iUnion
    (vertex : ι → V) (gasket : Set V) (rotate : Module.End ℚ V) (drift : V)
    (selfSimilar : gasket = ⋃ digit, cornerMap vertex digit '' gasket) :
    shiftedIntersection gasket rotate drift =
      ⋃ blueDigit, ⋃ redDigit,
        cornerMap vertex blueDigit ''
          shiftedIntersection gasket rotate
            ((2 : ℚ) • drift + vertex blueDigit - rotate (vertex redDigit)) := by
  ext point
  constructor
  · rintro ⟨point_in_gasket, redPoint, redPoint_in_gasket, point_eq⟩
    rw [selfSimilar] at point_in_gasket redPoint_in_gasket
    rcases Set.mem_iUnion.mp point_in_gasket with
      ⟨blueDigit, bluePreimage, bluePreimage_in_gasket, bluePreimage_eq⟩
    rcases Set.mem_iUnion.mp redPoint_in_gasket with
      ⟨redDigit, redPreimage, redPreimage_in_gasket, redPreimage_eq⟩
    refine Set.mem_iUnion.mpr ⟨blueDigit, Set.mem_iUnion.mpr ⟨redDigit, ?_⟩⟩
    refine ⟨bluePreimage, ⟨bluePreimage_in_gasket,
      redPreimage, redPreimage_in_gasket, ?_⟩, bluePreimage_eq⟩
    calc
      bluePreimage =
          (2 : ℚ) • cornerMap vertex blueDigit bluePreimage -
            vertex blueDigit := by
        simp only [cornerMap]
        module
      _ = (2 : ℚ) • point - vertex blueDigit := by rw [bluePreimage_eq]
      _ = (2 : ℚ) • (rotate redPoint - drift) - vertex blueDigit := by rw [point_eq]
      _ = (2 : ℚ) •
            (rotate (cornerMap vertex redDigit redPreimage) - drift) -
              vertex blueDigit := by rw [← redPreimage_eq]
      _ = rotate redPreimage -
            ((2 : ℚ) • drift + vertex blueDigit - rotate (vertex redDigit)) := by
        simp only [cornerMap, map_smul, map_add]
        module
  · intro point_in_union
    rcases Set.mem_iUnion.mp point_in_union with ⟨blueDigit, point_in_blue_union⟩
    rcases Set.mem_iUnion.mp point_in_blue_union with
      ⟨redDigit, bluePreimage, bluePreimage_in_intersection, bluePreimage_eq⟩
    rcases bluePreimage_in_intersection with
      ⟨bluePreimage_in_gasket, redPreimage, redPreimage_in_gasket,
        bluePreimage_relation⟩
    refine ⟨?_, cornerMap vertex redDigit redPreimage, ?_, ?_⟩
    · rw [selfSimilar]
      exact Set.mem_iUnion.mpr ⟨blueDigit,
        ⟨bluePreimage, bluePreimage_in_gasket, bluePreimage_eq⟩⟩
    · rw [selfSimilar]
      exact Set.mem_iUnion.mpr ⟨redDigit,
        ⟨redPreimage, redPreimage_in_gasket, rfl⟩⟩
    · calc
        point = cornerMap vertex blueDigit bluePreimage := bluePreimage_eq.symm
        _ = cornerMap vertex blueDigit
              (rotate redPreimage -
                ((2 : ℚ) • drift + vertex blueDigit -
                  rotate (vertex redDigit))) := by rw [bluePreimage_relation]
        _ = rotate (cornerMap vertex redDigit redPreimage) - drift := by
          simp only [cornerMap, map_smul, map_add]
          module

end GeometricRecursion

section FiniteState

/-- An infinite sequence taking values in a fixed finite set repeats a state. -/
theorem exists_repeated_state {V : Type*} [DecidableEq V]
    (states : ℕ → V) (candidates : Finset V)
    (state_mem : ∀ level, states level ∈ candidates) :
    ∃ firstLevel secondLevel, firstLevel < secondLevel ∧
      states firstLevel = states secondLevel := by
  let statesInCandidates : ℕ → {state // state ∈ candidates} :=
    fun level => ⟨states level, state_mem level⟩
  obtain ⟨firstLevel, secondLevel, levels_ne, states_eq⟩ :=
    Finite.exists_ne_map_eq_of_infinite statesInCandidates
  rcases lt_or_gt_of_ne levels_ne with levels_lt | levels_gt
  · exact ⟨firstLevel, secondLevel, levels_lt, congrArg Subtype.val states_eq⟩
  · exact ⟨secondLevel, firstLevel, levels_gt, congrArg Subtype.val states_eq.symm⟩

end FiniteState

section RepeatedCarry

variable {K : Type*} [Field K]

/-- Ratios of nonzero elements of a lattice subring.  For the Eisenstein lattice
this is precisely the arithmetic set denoted `ℚ(ω)` in the paper. -/
def ratioClosure (lattice : Subring K) : Set K :=
  {value | ∃ numerator denominator : lattice,
    (denominator : K) ≠ 0 ∧
      value = (numerator : K) / (denominator : K)}

/-- The exact algebraic heart of “finite type implies commensurable”.  Equality
of two carries gives one nonzero lattice vector that the rotation sends to
another lattice vector, hence the rotation is a quotient of lattice elements. -/
theorem rotation_mem_ratioClosure_of_repeated_carry
    (lattice : Subring K) (rotation : K) (blueValue redValue : ℕ → lattice)
    {firstLevel secondLevel : ℕ}
    (repeatedCarry :
      (blueValue secondLevel : K) - rotation * (redValue secondLevel : K) =
        (blueValue firstLevel : K) - rotation * (redValue firstLevel : K))
    (redValues_ne : redValue secondLevel ≠ redValue firstLevel) :
    rotation ∈ ratioClosure lattice := by
  refine ⟨blueValue secondLevel - blueValue firstLevel,
    redValue secondLevel - redValue firstLevel, ?_, ?_⟩
  · change (redValue secondLevel : K) - (redValue firstLevel : K) ≠ 0
    exact sub_ne_zero.mpr (fun values_eq => redValues_ne (Subtype.ext values_eq))
  · apply (eq_div_iff (by
      change (redValue secondLevel : K) - (redValue firstLevel : K) ≠ 0
      exact sub_ne_zero.mpr
        (fun values_eq => redValues_ne (Subtype.ext values_eq)))).2
    change rotation *
      ((redValue secondLevel : K) - (redValue firstLevel : K)) =
        (blueValue secondLevel : K) - (blueValue firstLevel : K)
    linear_combination -repeatedCarry

end RepeatedCarry

section PiThird

/-- Eisenstein-lattice coordinates relative to `(p₀, p₁)`. -/
abbrev LatticePoint := ℤ × ℤ

/-- The three gasket vertices in Eisenstein-lattice coordinates. -/
def vertexPiThird : Fin 3 → LatticePoint
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, -1)

/-- Rotation through `π / 3` in the basis `(p₀, p₁)`. -/
def rotatePiThird (point : LatticePoint) : LatticePoint :=
  (point.1 - point.2, point.1)

/-- One carry update at the angle `π / 3`. -/
def nextCarryPiThird (carry : LatticePoint) (digits : Fin 3 × Fin 3) : LatticePoint :=
  2 • carry + (vertexPiThird digits.1 - rotatePiThird (vertexPiThird digits.2))

/-- The four candidate/live carries listed in Section 2. -/
def piThirdCarries : Finset LatticePoint :=
  {(0, 0), (-1, 0), (0, -1), (1, 1)}

/-- Digit pairs whose next carry remains among the four Section 2 states. -/
def allowedPiThird (carry : LatticePoint) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun digits => nextCarryPiThird carry digits ∈ piThirdCarries)

theorem rotatePiThird_vertex_zero :
    rotatePiThird (vertexPiThird 0) = -vertexPiThird 2 := by
  decide

theorem rotatePiThird_vertex_one :
    rotatePiThird (vertexPiThird 1) = -vertexPiThird 0 := by
  decide

theorem rotatePiThird_vertex_two :
    rotatePiThird (vertexPiThird 2) = -vertexPiThird 1 := by
  decide

/-- The central carry has the six outgoing digit pairs displayed in the paper. -/
theorem allowedPiThird_zero :
    allowedPiThird (0, 0) =
      {(1, 0), (2, 2), (0, 0), (2, 1), (0, 2), (1, 1)} := by
  decide

/-- Each outer carry has exactly the single return edge displayed in the paper. -/
theorem allowedPiThird_outer_zero :
    allowedPiThird (-vertexPiThird 0) = {(0, 1)} := by
  decide

theorem allowedPiThird_outer_one :
    allowedPiThird (-vertexPiThird 1) = {(1, 2)} := by
  decide

theorem allowedPiThird_outer_two :
    allowedPiThird (-vertexPiThird 2) = {(2, 0)} := by
  decide

/-- The six central edges split as two edges to each outer carry. -/
theorem two_edges_to_each_outer_carry :
    ((allowedPiThird (0, 0)).filter
      (fun digits => nextCarryPiThird (0, 0) digits = -vertexPiThird 0)).card = 2 ∧
    ((allowedPiThird (0, 0)).filter
      (fun digits => nextCarryPiThird (0, 0) digits = -vertexPiThird 1)).card = 2 ∧
    ((allowedPiThird (0, 0)).filter
      (fun digits => nextCarryPiThird (0, 0) digits = -vertexPiThird 2)).card = 2 := by
  decide

/-- All three outer edges return to the central carry. -/
theorem outer_carries_return_to_zero :
    nextCarryPiThird (-vertexPiThird 0) (0, 1) = (0, 0) ∧
    nextCarryPiThird (-vertexPiThird 1) (1, 2) = (0, 0) ∧
    nextCarryPiThird (-vertexPiThird 2) (2, 0) = (0, 0) := by
  decide

/-- There are six legal two-step returns, matching the six quarter-scale maps. -/
theorem six_two_step_returns :
    (Finset.univ.filter (fun digitPairs : (Fin 3 × Fin 3) × (Fin 3 × Fin 3) =>
      nextCarryPiThird
        (nextCarryPiThird (0, 0) digitPairs.1) digitPairs.2 = (0, 0) ∧
      nextCarryPiThird (0, 0) digitPairs.1 ∈ piThirdCarries)).card = 6 := by
  decide

end PiThird

end MoireSection2
