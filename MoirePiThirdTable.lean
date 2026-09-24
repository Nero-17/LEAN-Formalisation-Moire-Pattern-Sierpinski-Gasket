import MoirePiThirdGeometry
import MoirePiThirdSpectrum

namespace MoirePiThirdTable

open MoireSection2 MoireGeometry MoireEisenstein MoirePiThirdGeometry MoireDeterminization

def coordinateState : Fin 4 → Finset LatticePoint
  | 0 => {(0, 0)}
  | 1 => {(0, -1), (1, 1)}
  | 2 => {(-1, 0), (1, 1)}
  | 3 => {(-1, 0), (0, -1)}

def coordinateSuccessor (state : Finset LatticePoint) (blueDigit : Fin 3) : Finset LatticePoint :=
  (state.biUnion (fun carry => Finset.univ.image (fun redDigit =>
    nextCarryPiThird carry (blueDigit, redDigit)))).filter (· ∈ piThirdCarries)

def transition : Fin 4 → Fin 3 → Option (Fin 4)
  | 0, 0 => some 1
  | 0, 1 => some 2
  | 0, 2 => some 3
  | 1, 0 => none
  | 1, _ => some 0
  | 2, 1 => none
  | 2, _ => some 0
  | 3, 2 => none
  | 3, _ => some 0

theorem coordinateState_subset : ∀ state, coordinateState state ⊆ piThirdCarries := by decide

theorem coordinate_table : ∀ state blueDigit,
    coordinateSuccessor (coordinateState state) blueDigit =
      match transition state blueDigit with
      | none => ∅
      | some target => coordinateState target := by decide

noncomputable def geometricState (state : Fin 4) : Finset ℂ :=
  (coordinateState state).image complexCoordinates

theorem successor_image (state : Finset LatticePoint) (state_subset : state ⊆ piThirdCarries)
    (blueDigit : Fin 3) :
    successorState vertex gasket (rotation (Real.pi / 3)) (state.image complexCoordinates) blueDigit =
      (coordinateSuccessor state blueDigit).image complexCoordinates := by
  classical
  ext target
  rw [mem_successorState]
  simp only [coordinateSuccessor, Finset.mem_image, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨_, ⟨carry, carry_mem, rfl⟩, redDigit, equality⟩, live⟩
    refine ⟨nextCarryPiThird carry (blueDigit, redDigit), ?_, ?_⟩
    · refine ⟨⟨carry, carry_mem, redDigit, rfl⟩, ?_⟩
      apply (live_successor_iff carry (state_subset carry_mem) blueDigit redDigit).mp
      rwa [equality]
    · rwa [successor_coordinates] at equality
  · rintro ⟨_, ⟨⟨carry, carry_mem, redDigit, rfl⟩, successor_mem⟩, rfl⟩
    refine ⟨⟨complexCoordinates carry, ⟨carry, carry_mem, rfl⟩, redDigit,
      successor_coordinates carry blueDigit redDigit⟩, candidate_live _ successor_mem⟩

/-- Each of the twelve cells uses the actual geometric nonempty-intersection filter. -/
theorem geometric_table (state : Fin 4) (blueDigit : Fin 3) :
    successorState vertex gasket (rotation (Real.pi / 3)) (geometricState state) blueDigit =
      match transition state blueDigit with
      | none => ∅
      | some target => geometricState target := by
  rw [geometricState, successor_image _ (coordinateState_subset state), coordinate_table]
  cases transition state blueDigit <;> simp [geometricState]

theorem geometricState_nonempty (state : Fin 4) : (geometricState state).Nonempty := by
  apply Finset.Nonempty.image
  have : ∀ state, (coordinateState state).Nonempty := by decide
  exact this state

theorem geometricState_injective : Function.Injective geometricState := by
  intro first second equality
  have coordinate_eq := Finset.image_injective complexCoordinates_injective equality
  have checked : Function.Injective coordinateState := by decide
  exact checked coordinate_eq

theorem geometricState_zero : geometricState 0 = {0} := by
  simp [geometricState, coordinateState, complexCoordinates]

theorem edge_iff_transition (source target : Fin 4) (blueDigit : Fin 3) :
    Edge vertex gasket (rotation (Real.pi / 3)) (geometricState source) blueDigit
      (geometricState target) ↔ transition source blueDigit = some target := by
  unfold Edge
  rw [geometric_table]
  cases equality : transition source blueDigit with
  | none => simp [Finset.Nonempty.ne_empty (geometricState_nonempty target)]
  | some next =>
      simp [geometricState_injective.eq_iff, geometricState_nonempty, eq_comm]

theorem geometricState_reachable (state : Fin 4) :
    ReachableState vertex gasket (rotation (Real.pi / 3)) (geometricState state) := by
  have initial : ReachableState vertex gasket (rotation (Real.pi / 3)) (geometricState 0) := by
    rw [geometricState_zero]
    exact ReachableState.initial
  fin_cases state
  · exact initial
  · exact ReachableState.step initial 0 ((edge_iff_transition 0 1 0).mpr rfl)
  · exact ReachableState.step initial 1 ((edge_iff_transition 0 2 1).mpr rfl)
  · exact ReachableState.step initial 2 ((edge_iff_transition 0 3 2).mpr rfl)

theorem reachableState_iff (state : Finset ℂ) :
    ReachableState vertex gasket (rotation (Real.pi / 3)) state ↔
      ∃ index, state = geometricState index := by
  constructor
  · intro reachable
    induction reachable with
    | initial => exact ⟨0, geometricState_zero.symm⟩
    | @step source target previous blueDigit edge inductionHypothesis =>
      obtain ⟨index, rfl⟩ := inductionHypothesis
      have target_eq := edge.1
      rw [geometric_table] at target_eq
      cases transition_eq : transition index blueDigit with
      | none =>
          have target_empty : target = ∅ := by simpa [transition_eq] using target_eq
          exact False.elim (edge.2.ne_empty target_empty)
      | some next => exact ⟨next, by simpa [transition_eq] using target_eq⟩
  · rintro ⟨index, rfl⟩
    exact geometricState_reachable index

noncomputable def stateEquiv : Fin 4 ≃
    {state // ReachableState vertex gasket (rotation (Real.pi / 3)) state} :=
  Equiv.ofBijective (fun index => ⟨geometricState index, geometricState_reachable index⟩)
    ⟨fun _ _ equality => geometricState_injective (congrArg Subtype.val equality),
      fun state => by
        obtain ⟨index, equality⟩ := (reachableState_iff state.val).mp state.property
        exact ⟨index, Subtype.ext equality.symm⟩⟩

/-- Definition 2.3's actual matrix, in precisely the displayed order of its four states. -/
theorem adjacency_eq :
    (fun source target : Fin 4 =>
      (adjacencyMatrix vertex gasket (rotation (Real.pi / 3))
        (stateEquiv source) (stateEquiv target) : ℂ)) = MoirePiThirdSpectrum.adjacency := by
  classical
  ext source target
  change ((Finset.univ.filter (fun blueDigit =>
    Edge vertex gasket (rotation (Real.pi / 3)) (geometricState source) blueDigit
      (geometricState target))).card : ℂ) = _
  simp_rw [edge_iff_transition]
  have checked : ∀ source target : Fin 4,
      (Finset.univ.filter (fun digit => transition source digit = some target)).card =
        (!![0, 1, 1, 1; 2, 0, 0, 0; 2, 0, 0, 0; 2, 0, 0, 0] :
          Matrix (Fin 4) (Fin 4) ℕ) source target := by decide
  rw [checked]
  fin_cases source <;> fin_cases target <;>
    norm_num [transition, MoirePiThirdSpectrum.adjacency]

theorem geometric_matrix_spectral_radius :
    spectralRadius ℂ (A := Matrix (Fin 4) (Fin 4) ℂ) ((fun source target : Fin 4 =>
      (adjacencyMatrix vertex gasket (rotation (Real.pi / 3))
        (stateEquiv source) (stateEquiv target) : ℂ)) : Matrix (Fin 4) (Fin 4) ℂ) =
      ENNReal.ofReal (Real.sqrt 6) := by
  rw [adjacency_eq]
  exact MoirePiThirdSpectrum.spectral_radius

end MoirePiThirdTable
