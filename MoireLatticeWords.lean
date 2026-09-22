import MoireSection2
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Injectivity of finite Eisenstein-lattice words

The vertices are `(1, 0)`, `(0, 1)`, and `(-1, -1)` in the basis `(1, ω)`.
Their three residue classes modulo two are distinct and nonzero.  This file
proves that the weighted address map in Section 2 is injective on *all* finite
words, including words of different lengths.  It then uses that fact to supply
the nonzero denominator in the finite-carry converse.

The field-valued results explicitly require an injective additive embedding of
these integer coordinates into the lattice subring.  Identifying that embedding
with the complex Eisenstein lattice is a separate geometric interface.
-/

namespace MoireLatticeWords

open MoireSection2

/-- The elementary parity calculation recovers both a digit and its predecessor. -/
theorem doubling_vertex_unique
    (firstDigit secondDigit : Fin 3) (firstPoint secondPoint : LatticePoint)
    (value_eq : 2 • firstPoint + vertexPiThird firstDigit =
      2 • secondPoint + vertexPiThird secondDigit) :
    firstDigit = secondDigit ∧ firstPoint = secondPoint := by
  have firstCoordinate_eq := congrArg Prod.fst value_eq
  have secondCoordinate_eq := congrArg Prod.snd value_eq
  fin_cases firstDigit <;> fin_cases secondDigit <;>
    simp [vertexPiThird] at firstCoordinate_eq secondCoordinate_eq
  all_goals
    first
    | omega
    | exact ⟨rfl, Prod.ext (by omega) (by omega)⟩

/-- A last digit in a nonzero residue class prevents a value of zero. -/
theorem doubling_add_vertex_ne_zero (digit : Fin 3) (point : LatticePoint) :
    2 • point + vertexPiThird digit ≠ 0 := by
  intro value_eq
  have firstCoordinate_eq := congrArg Prod.fst value_eq
  have secondCoordinate_eq := congrArg Prod.snd value_eq
  fin_cases digit <;>
    simp [vertexPiThird] at firstCoordinate_eq secondCoordinate_eq <;>
    omega

/-- A least-significant-digit-first recursion used only for the injectivity proof. -/
def reverseValue : List (Fin 3) → LatticePoint
  | [] => 0
  | digit :: remainingDigits => 2 • reverseValue remainingDigits + vertexPiThird digit

theorem reverseValue_cons_ne_zero (digit : Fin 3) (remainingDigits : List (Fin 3)) :
    reverseValue (digit :: remainingDigits) ≠ 0 :=
  doubling_add_vertex_ne_zero digit (reverseValue remainingDigits)

/-- Injectivity includes the empty word and does not assume equal lengths. -/
theorem reverseValue_injective : Function.Injective reverseValue := by
  intro firstWord
  induction firstWord with
  | nil =>
      intro secondWord values_eq
      cases secondWord with
      | nil => rfl
      | cons digit remainingDigits =>
          exact False.elim (reverseValue_cons_ne_zero digit remainingDigits values_eq.symm)
  | cons firstDigit firstRemainingDigits inductionHypothesis =>
      intro secondWord values_eq
      cases secondWord with
      | nil =>
          exact False.elim
            (reverseValue_cons_ne_zero firstDigit firstRemainingDigits values_eq)
      | cons secondDigit secondRemainingDigits =>
          obtain ⟨digits_eq, predecessorValues_eq⟩ :=
            doubling_vertex_unique firstDigit secondDigit
              (reverseValue firstRemainingDigits) (reverseValue secondRemainingDigits)
              values_eq
          exact congrArg₂ List.cons digits_eq (inductionHypothesis predecessorValues_eq)

/-- The usual most-significant-digit-first value used in the manuscript. -/
def wordValue (word : List (Fin 3)) : LatticePoint :=
  weightedSum (word.map vertexPiThird)

/-- The auxiliary recursion agrees exactly with the manuscript after reversal. -/
theorem reverseValue_eq_wordValue_reverse (word : List (Fin 3)) :
    reverseValue word = wordValue word.reverse := by
  induction word with
  | nil => rfl
  | cons digit remainingDigits inductionHypothesis =>
      simp [reverseValue, wordValue, List.map_append,
        weightedSum_append_singleton, inductionHypothesis, wordValue]

/-- The raw lattice address map is injective on all finite words. -/
theorem wordValue_injective : Function.Injective wordValue := by
  intro firstWord secondWord values_eq
  apply List.reverse_inj.mp
  apply reverseValue_injective
  simpa [reverseValue_eq_wordValue_reverse] using values_eq

@[simp] theorem wordValue_nil : wordValue [] = 0 := rfl

/-- Appending a final symbol gives the exact carry recurrence. -/
theorem wordValue_append_singleton (word : List (Fin 3)) (digit : Fin 3) :
    wordValue (word ++ [digit]) = 2 • wordValue word + vertexPiThird digit := by
  simp [wordValue, List.map_append, weightedSum_append_singleton]

theorem wordValue_eq_zero_iff (word : List (Fin 3)) :
    wordValue word = 0 ↔ word = [] := by
  constructor
  · exact fun value_eq => wordValue_injective (value_eq.trans wordValue_nil.symm)
  · intro word_eq
    simp [word_eq]

/-- A finite prefix of an infinite address, in the manuscript's order. -/
def addressPrefix (address : ℕ → Fin 3) (level : ℕ) : List (Fin 3) :=
  (List.range level).map address

@[simp] theorem addressPrefix_length (address : ℕ → Fin 3) (level : ℕ) :
    (addressPrefix address level).length = level := by
  simp [addressPrefix]

@[simp] theorem addressPrefix_zero (address : ℕ → Fin 3) :
    addressPrefix address 0 = [] := rfl

theorem addressPrefix_succ (address : ℕ → Fin 3) (level : ℕ) :
    addressPrefix address (level + 1) = addressPrefix address level ++ [address level] := by
  simp [addressPrefix, List.range_succ, List.map_append]

/-- Along any address, different prefix levels have different lattice values. -/
theorem prefixValue_injective (address : ℕ → Fin 3) :
    Function.Injective (fun level => wordValue (addressPrefix address level)) := by
  intro firstLevel secondLevel values_eq
  have words_eq := wordValue_injective values_eq
  have lengths_eq := congrArg List.length words_eq
  simpa using lengths_eq

section FiniteCarries

variable {K : Type*} [Field K]

/-- A field carry obtained from two actual infinite addresses. -/
def prefixCarry (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation : K) (blueAddress redAddress : ℕ → Fin 3) (level : ℕ) : K :=
  (coordinates (wordValue (addressPrefix blueAddress level)) : K) -
    rotation * (coordinates (wordValue (addressPrefix redAddress level)) : K)

/-- The field version of the relative-displacement update. -/
def carryStep (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation carry : K) (digits : Fin 3 × Fin 3) : K :=
  2 * carry + (coordinates (vertexPiThird digits.1) : K) -
    rotation * (coordinates (vertexPiThird digits.2) : K)

@[simp] theorem prefixCarry_zero
    (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation : K) (blueAddress redAddress : ℕ → Fin 3) :
    prefixCarry lattice coordinates rotation blueAddress redAddress 0 = 0 := by
  simp [prefixCarry]

/-- Carries of the actual finite prefixes obey precisely the local update. -/
theorem prefixCarry_succ
    (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation : K) (blueAddress redAddress : ℕ → Fin 3) (level : ℕ) :
    prefixCarry lattice coordinates rotation blueAddress redAddress (level + 1) =
      carryStep lattice coordinates rotation
        (prefixCarry lattice coordinates rotation blueAddress redAddress level)
        (blueAddress level, redAddress level) := by
  simp only [prefixCarry, addressPrefix_succ, wordValue_append_singleton,
    two_nsmul, map_add, Subring.coe_add, carryStep]
  ring

/-- Finite carries along any pair of infinite addresses force a lattice ratio.
The distinctness of red values is proved from their lengths, rather than assumed. -/
theorem rotation_mem_ratioClosure_of_finite_prefixCarries
    (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (coordinates_injective : Function.Injective coordinates)
    (rotation : K) (blueAddress redAddress : ℕ → Fin 3)
    (candidates : Finset K)
    (carry_mem : ∀ level,
      prefixCarry lattice coordinates rotation blueAddress redAddress level ∈ candidates) :
    rotation ∈ ratioClosure lattice := by
  classical
  obtain ⟨firstLevel, secondLevel, levels_lt, carries_eq⟩ :=
    exists_repeated_state
      (prefixCarry lattice coordinates rotation blueAddress redAddress) candidates carry_mem
  apply rotation_mem_ratioClosure_of_repeated_carry lattice rotation
    (fun level => coordinates (wordValue (addressPrefix blueAddress level)))
    (fun level => coordinates (wordValue (addressPrefix redAddress level)))
    carries_eq.symm
  intro redValues_eq
  have levels_eq := prefixValue_injective redAddress (coordinates_injective redValues_eq)
  omega

/-- A finite set containing the initial carry and admitting a successor from
every one of its states forces commensurability.  The infinite addresses,
repeated state, and nonzero lattice denominator are all constructed in the proof.

When `live` is the set of live reachable displacements, its successor property
is the remaining geometric interface, supplied by the gasket recursion. -/
theorem rotation_mem_ratioClosure_of_finite_live_carries
    (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (coordinates_injective : Function.Injective coordinates)
    (rotation : K) (live : Set K) (live_finite : live.Finite)
    (zero_live : (0 : K) ∈ live)
    (successor_live : ∀ carry ∈ live, ∃ digits : Fin 3 × Fin 3,
      carryStep lattice coordinates rotation carry digits ∈ live) :
    rotation ∈ ratioClosure lattice := by
  classical
  let digitsOf (state : {carry // carry ∈ live}) : Fin 3 × Fin 3 :=
    Classical.choose (successor_live state.val state.property)
  have digitsOf_live (state : {carry // carry ∈ live}) :
      carryStep lattice coordinates rotation state.val (digitsOf state) ∈ live :=
    Classical.choose_spec (successor_live state.val state.property)
  let nextState (state : {carry // carry ∈ live}) : {carry // carry ∈ live} :=
    ⟨carryStep lattice coordinates rotation state.val (digitsOf state), digitsOf_live state⟩
  let statePath : ℕ → {carry // carry ∈ live} :=
    Nat.rec ⟨0, zero_live⟩ (fun _ state => nextState state)
  let blueAddress (level : ℕ) : Fin 3 := (digitsOf (statePath level)).1
  let redAddress (level : ℕ) : Fin 3 := (digitsOf (statePath level)).2
  have statePath_eq (level : ℕ) :
      (statePath level).val =
        prefixCarry lattice coordinates rotation blueAddress redAddress level := by
    induction level with
    | zero => exact (prefixCarry_zero lattice coordinates rotation blueAddress redAddress).symm
    | succ level inductionHypothesis =>
        change carryStep lattice coordinates rotation (statePath level).val
          (digitsOf (statePath level)) = _
        rw [prefixCarry_succ]
        dsimp only [blueAddress, redAddress]
        rw [inductionHypothesis]
  apply rotation_mem_ratioClosure_of_finite_prefixCarries
    lattice coordinates coordinates_injective rotation blueAddress redAddress live_finite.toFinset
  intro level
  apply live_finite.mem_toFinset.mpr
  rw [← statePath_eq level]
  exact (statePath level).property

end FiniteCarries

section LiveReachability

variable {K : Type*} [Field K] [CharZero K]

/-- The three lattice vertices viewed as points of the ambient field. -/
def fieldVertex (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (digit : Fin 3) : K := coordinates (vertexPiThird digit)

/-- Reachability by finitely many exact carry updates, beginning at zero. -/
inductive ReachableCarry (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation : K) : K → Prop
  | initial : ReachableCarry lattice coordinates rotation 0
  | step {carry : K} (previous : ReachableCarry lattice coordinates rotation carry)
      (digits : Fin 3 × Fin 3) :
      ReachableCarry lattice coordinates rotation
        (carryStep lattice coordinates rotation carry digits)

/-- A reachable carry is live precisely when the corresponding gasket
intersection is nonempty. -/
def liveReachable (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation : K) (gasket : Set K) : Set K :=
  {carry | ReachableCarry lattice coordinates rotation carry ∧
    (shiftedIntersection gasket (LinearMap.mulLeft ℚ rotation) carry).Nonempty}

/-- Self-similarity supplies the live-successor property directly. -/
theorem live_has_live_successor
    (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (rotation : K) (gasket : Set K)
    (selfSimilar : gasket = ⋃ digit,
      cornerMap (fieldVertex lattice coordinates) digit '' gasket)
    {carry : K}
    (carry_live :
      (shiftedIntersection gasket (LinearMap.mulLeft ℚ rotation) carry).Nonempty) :
    ∃ digits : Fin 3 × Fin 3,
      (shiftedIntersection gasket (LinearMap.mulLeft ℚ rotation)
        (carryStep lattice coordinates rotation carry digits)).Nonempty := by
  obtain ⟨point, point_mem⟩ := carry_live
  rw [shiftedIntersection_eq_iUnion (fieldVertex lattice coordinates) gasket
    (LinearMap.mulLeft ℚ rotation) carry selfSimilar] at point_mem
  rcases Set.mem_iUnion.mp point_mem with ⟨blueDigit, point_mem⟩
  rcases Set.mem_iUnion.mp point_mem with ⟨redDigit, preimage, preimage_mem, _⟩
  refine ⟨(blueDigit, redDigit), preimage, ?_⟩
  simpa [carryStep, fieldVertex, Algebra.smul_def] using preimage_mem

/-- The Section 2 converse with its original structural assumptions: a
self-similar gasket, a live initial carry, and finitely many live reachable
carries.  All infinite-path and address-injectivity steps are proved internally. -/
theorem rotation_mem_ratioClosure_of_finite_liveReachable
    (lattice : Subring K) (coordinates : LatticePoint →+ lattice)
    (coordinates_injective : Function.Injective coordinates)
    (rotation : K) (gasket : Set K)
    (selfSimilar : gasket = ⋃ digit,
      cornerMap (fieldVertex lattice coordinates) digit '' gasket)
    (zero_live :
      (shiftedIntersection gasket (LinearMap.mulLeft ℚ rotation) 0).Nonempty)
    (live_finite : (liveReachable lattice coordinates rotation gasket).Finite) :
    rotation ∈ ratioClosure lattice := by
  apply rotation_mem_ratioClosure_of_finite_live_carries
    lattice coordinates coordinates_injective rotation
    (liveReachable lattice coordinates rotation gasket) live_finite
  · exact ⟨ReachableCarry.initial, zero_live⟩
  · intro carry carry_mem
    obtain ⟨digits, successor_live⟩ :=
      live_has_live_successor lattice coordinates rotation gasket selfSimilar carry_mem.2
    exact ⟨digits, ReachableCarry.step carry_mem.1 digits, successor_live⟩

end LiveReachability

end MoireLatticeWords
