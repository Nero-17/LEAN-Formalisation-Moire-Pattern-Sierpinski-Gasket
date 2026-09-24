import MoireConcrete
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Matrix.Basic

/-!
# The live subset construction of Definition 2.3

States are finite sets of relative displacements.  Each blue label has one
target, obtained by collecting all red successors and keeping exactly the live
ones.  The represented sets satisfy the resulting deterministic recursion.
This file does not assume or assert a graph-directed dimension theorem.
-/

namespace MoireDeterminization

open MoireSection2

noncomputable section

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

/-- The union of the actual shifted intersections represented by a state. -/
def stateIntersection (gasket : Set V) (rotate : Module.End ℚ V)
    (state : Finset V) : Set V :=
  {point | ∃ displacement ∈ state,
    point ∈ shiftedIntersection gasket rotate displacement}

/-- Exactly the live-filtered target set in Definition 2.3. -/
def successorState (vertex : ι → V) (gasket : Set V) (rotate : Module.End ℚ V)
    (state : Finset V) (blueDigit : ι) : Finset V := by
  classical
  exact (state.biUnion (fun displacement => Finset.univ.image (fun redDigit =>
    (2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit)))).filter
      (fun displacement => (shiftedIntersection gasket rotate displacement).Nonempty)

theorem mem_successorState (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V) (state : Finset V) (blueDigit : ι) (target : V) :
    target ∈ successorState vertex gasket rotate state blueDigit ↔
      (∃ displacement ∈ state, ∃ redDigit,
        (2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit) = target) ∧
      (shiftedIntersection gasket rotate target).Nonempty := by
  classical
  simp [successorState]

@[simp] theorem stateIntersection_empty (gasket : Set V) (rotate : Module.End ℚ V) :
    stateIntersection gasket rotate ∅ = ∅ := by
  ext point
  simp [stateIntersection]

@[simp] theorem stateIntersection_singleton (gasket : Set V)
    (rotate : Module.End ℚ V) (displacement : V) :
    stateIntersection gasket rotate {displacement} =
      shiftedIntersection gasket rotate displacement := by
  classical
  ext point
  simp [stateIntersection]

/-- The actual union recursion after determinization. Empty targets contribute
the empty set, so this is also the recursion with only nonempty-target edges. -/
theorem stateIntersection_eq_iUnion (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V)
    (selfSimilar : gasket = ⋃ digit, cornerMap vertex digit '' gasket)
    (state : Finset V) :
    stateIntersection gasket rotate state =
      ⋃ blueDigit, cornerMap vertex blueDigit ''
        stateIntersection gasket rotate
          (successorState vertex gasket rotate state blueDigit) := by
  classical
  ext point
  constructor
  · rintro ⟨displacement, displacement_mem, point_mem⟩
    rw [shiftedIntersection_eq_iUnion vertex gasket rotate displacement selfSimilar]
      at point_mem
    obtain ⟨blueDigit, point_mem⟩ := Set.mem_iUnion.mp point_mem
    obtain ⟨redDigit, predecessor, predecessor_mem, point_eq⟩ :=
      Set.mem_iUnion.mp point_mem
    refine Set.mem_iUnion.mpr ⟨blueDigit, predecessor, ?_, point_eq⟩
    refine ⟨(2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit),
      ?_, predecessor_mem⟩
    exact (mem_successorState vertex gasket rotate state blueDigit _).mpr
      ⟨⟨displacement, displacement_mem, redDigit, rfl⟩, ⟨predecessor, predecessor_mem⟩⟩
  · intro point_mem
    obtain ⟨blueDigit, predecessor, predecessor_mem, point_eq⟩ :=
      Set.mem_iUnion.mp point_mem
    obtain ⟨target, target_mem, predecessor_mem⟩ := predecessor_mem
    obtain ⟨⟨displacement, displacement_mem, redDigit, target_eq⟩, _⟩ :=
      (mem_successorState vertex gasket rotate state blueDigit target).mp target_mem
    refine ⟨displacement, displacement_mem, ?_⟩
    rw [shiftedIntersection_eq_iUnion vertex gasket rotate displacement selfSimilar]
    refine Set.mem_iUnion.mpr ⟨blueDigit, Set.mem_iUnion.mpr
      ⟨redDigit, predecessor, ?_, point_eq⟩⟩
    simpa [target_eq] using predecessor_mem

/-- An edge exists precisely for the nonempty target of its blue label. -/
def Edge (vertex : ι → V) (gasket : Set V) (rotate : Module.End ℚ V)
    (source : Finset V) (blueDigit : ι) (target : Finset V) : Prop :=
  target = successorState vertex gasket rotate source blueDigit ∧ target.Nonempty

/-- There is at most one outgoing edge with a fixed blue label. -/
theorem edge_deterministic (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V) {source firstTarget secondTarget : Finset V}
    {blueDigit : ι}
    (firstEdge : Edge vertex gasket rotate source blueDigit firstTarget)
    (secondEdge : Edge vertex gasket rotate source blueDigit secondTarget) :
    firstTarget = secondTarget :=
  firstEdge.1.trans secondEdge.1.symm

/-- Reachability retains only the states obtained from the singleton zero state
by nonempty-target edges, identifying states as equal finite sets. -/
inductive ReachableState (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V) : Finset V → Prop
  | initial : ReachableState vertex gasket rotate {0}
  | step {source target : Finset V}
      (previous : ReachableState vertex gasket rotate source) (blueDigit : ι)
      (edge : Edge vertex gasket rotate source blueDigit target) :
      ReachableState vertex gasket rotate target

/-- Matrix entries count blue labels, as in the manuscript, rather than pairs
of blue and red digits. The reachable index set is proved finite separately. -/
def adjacencyMatrix (vertex : ι → V) (gasket : Set V) (rotate : Module.End ℚ V) :
    Matrix {state // ReachableState vertex gasket rotate state}
      {state // ReachableState vertex gasket rotate state} ℕ := by
  classical
  exact fun source target => (Finset.univ.filter
    (fun blueDigit => Edge vertex gasket rotate source.val blueDigit target.val)).card

/-- Every represented point remains in the original gasket. -/
theorem stateIntersection_subset (gasket : Set V) (rotate : Module.End ℚ V)
    (state : Finset V) : stateIntersection gasket rotate state ⊆ gasket := by
  rintro point ⟨displacement, _, point_mem⟩
  exact point_mem.1

/-- Any nonempty target state represents a nonempty set because the transition
has explicitly discarded all non-live displacements. -/
theorem edge_target_nonempty (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V) {source target : Finset V} {blueDigit : ι}
    (edge : Edge vertex gasket rotate source blueDigit target) :
    (stateIntersection gasket rotate target).Nonempty := by
  obtain ⟨displacement, displacement_mem⟩ := edge.2
  have successor_mem :
      displacement ∈ successorState vertex gasket rotate source blueDigit := by
    simpa [edge.1] using displacement_mem
  obtain ⟨point, point_mem⟩ :=
    ((mem_successorState vertex gasket rotate source blueDigit displacement).mp successor_mem).2
  exact ⟨point, displacement, displacement_mem, point_mem⟩

theorem reachableState_represents_nonempty (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V)
    (initial_live : (shiftedIntersection gasket rotate 0).Nonempty)
    {state : Finset V} (reachable : ReachableState vertex gasket rotate state) :
    (stateIntersection gasket rotate state).Nonempty := by
  cases reachable with
  | initial => simpa using initial_live
  | step previous blueDigit edge => exact edge_target_nonempty vertex gasket rotate edge

/-- A finite pool containing zero and all live successors contains every
reachable state. This is the exact interface to the arithmetic finiteness proof. -/
theorem reachableState_subset_pool (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V) (pool : Finset V) (zero_mem : (0 : V) ∈ pool)
    (closed_live : ∀ displacement ∈ pool, ∀ blueDigit redDigit,
      (shiftedIntersection gasket rotate
        ((2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit))).Nonempty →
      (2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit) ∈ pool)
    {state : Finset V} (reachable : ReachableState vertex gasket rotate state) :
    state ⊆ pool := by
  classical
  induction reachable with
  | initial => simpa using zero_mem
  | @step source target previous blueDigit edge inductionHypothesis =>
      intro displacement displacement_mem
      rw [edge.1] at displacement_mem
      obtain ⟨⟨previousDisplacement, previous_mem, redDigit, rfl⟩, live⟩ :=
        (mem_successorState vertex gasket rotate source blueDigit displacement).mp displacement_mem
      exact closed_live previousDisplacement (inductionHypothesis previous_mem)
        blueDigit redDigit live

/-- Finitely many available live displacements give finitely many reachable
subset states. No graph dimension conclusion is built into this theorem. -/
theorem reachableStates_finite (vertex : ι → V) (gasket : Set V)
    (rotate : Module.End ℚ V) (pool : Finset V) (zero_mem : (0 : V) ∈ pool)
    (closed_live : ∀ displacement ∈ pool, ∀ blueDigit redDigit,
      (shiftedIntersection gasket rotate
        ((2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit))).Nonempty →
      (2 : ℚ) • displacement + vertex blueDigit - rotate (vertex redDigit) ∈ pool) :
    {state | ReachableState vertex gasket rotate state}.Finite := by
  classical
  apply pool.powerset.finite_toSet.subset
  intro state reachable
  exact Finset.mem_powerset.mpr
    (reachableState_subset_pool vertex gasket rotate pool zero_mem closed_live reachable)

/-- Definition 2.3's initial state represents exactly the actual rotated gasket
intersection at coincident centres. -/
theorem initialState_intersection (angle : ℝ) :
    stateIntersection MoireGeometry.gasket (MoireGeometry.rotation angle) {0} =
      MoireGeometry.gasket ∩ MoireGeometry.rotation angle '' MoireGeometry.gasket := by
  rw [stateIntersection_singleton]
  ext point
  simp only [shiftedIntersection, sub_zero, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_image]
  constructor
  · rintro ⟨point_mem, redPoint, redPoint_mem, point_eq⟩
    exact ⟨point_mem, redPoint, redPoint_mem, point_eq.symm⟩
  · rintro ⟨point_mem, redPoint, redPoint_mem, point_eq⟩
    exact ⟨point_mem, redPoint, redPoint_mem, point_eq.symm⟩

/-- Determinized recursion specialized to the actual vertices, rotation and
address-series gasket, with no self-similarity hypothesis left over. -/
theorem gasket_state_recursion (angle : ℝ) (state : Finset ℂ) :
    stateIntersection MoireGeometry.gasket (MoireGeometry.rotation angle) state =
      ⋃ blueDigit, cornerMap MoireGeometry.vertex blueDigit ''
        stateIntersection MoireGeometry.gasket (MoireGeometry.rotation angle)
          (successorState MoireGeometry.vertex MoireGeometry.gasket
            (MoireGeometry.rotation angle) state blueDigit) :=
  stateIntersection_eq_iUnion MoireGeometry.vertex MoireGeometry.gasket
    (MoireGeometry.rotation angle) MoireGeometry.gasket_selfSimilar state

section ExistingReachability

open MoireLatticeWords MoireEisenstein MoireConcrete

/-- The finite-set graph is finite under the existing development's precise
finite-type predicate. Adding zero to the pool avoids any hidden initial-liveness
assumption in this purely combinatorial finiteness statement. -/
theorem reachableStates_finite_of_finite_liveReachable (angle : ℝ)
    (finite_live :
      (liveReachable eisensteinLattice latticeCoordinates
        (Complex.exp (angle * Complex.I)) MoireGeometry.gasket).Finite) :
    {state | ReachableState MoireGeometry.vertex MoireGeometry.gasket
      (MoireGeometry.rotation angle) state}.Finite := by
  classical
  apply reachableStates_finite MoireGeometry.vertex MoireGeometry.gasket
    (MoireGeometry.rotation angle) (finite_live.toFinset ∪ {0})
  · simp
  · intro displacement displacement_mem blueDigit redDigit successor_live
    have displacement_reachable : ReachableCarry eisensteinLattice latticeCoordinates
        (Complex.exp (angle * Complex.I)) displacement := by
      rcases Finset.mem_union.mp displacement_mem with live_mem | zero_mem
      · exact (finite_live.mem_toFinset.mp live_mem).1
      · have displacement_zero : displacement = 0 := Finset.mem_singleton.mp zero_mem
        rw [displacement_zero]
        exact ReachableCarry.initial
    apply Finset.mem_union.mpr
    left
    apply finite_live.mem_toFinset.mpr
    constructor
    · have successor_reachable :=
        ReachableCarry.step displacement_reachable (blueDigit, redDigit)
      simpa [carryStep, ← complexCoordinates_vertex, MoireGeometry.rotation,
        Algebra.smul_def] using successor_reachable
    · simpa [rotation_eq_mulLeft] using successor_live

end ExistingReachability

end

end MoireDeterminization
