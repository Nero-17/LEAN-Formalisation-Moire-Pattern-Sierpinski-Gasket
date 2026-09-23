import MoireHausdorffUpper

namespace MoireActualUpper

open MoireGeometry MoireSection2 MoireDeterminization
open scoped Matrix.Norms.Operator

noncomputable section

variable (angle : ℝ)

abbrev States (angle : ℝ) := {state // ReachableState vertex gasket (rotation angle) state}

variable [Fintype (States angle)] [DecidableEq (States angle)]

theorem outgoing_nonzero (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3)
    (source : States angle) : 1 ≤ ∑ target : States angle,
      adjacencyMatrix vertex gasket (rotation angle) source target := by
  classical
  obtain ⟨point, member⟩ := MoireGraphGeometry.reachable_state_nonempty angle nonneg upper
    source.val source.property
  obtain ⟨target, member⟩ := Set.mem_iUnion.mp (MoireGraphCovers.actual_graph_recursion angle source member)
  obtain ⟨digit, member⟩ := Set.mem_iUnion.mp member
  obtain ⟨legal, _⟩ := Set.mem_iUnion.mp member
  have positive : 1 ≤ adjacencyMatrix vertex gasket (rotation angle) source target := by
    apply Nat.succ_le_iff.mpr
    exact Finset.card_pos.mpr ⟨digit, Finset.mem_filter.mpr ⟨Finset.mem_univ _, legal⟩⟩
  exact positive.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ target))

/-- The Hausdorff upper inequality of Theorem 2.4, for precisely the actual
reachable-state matrix of Definition 2.2. -/
theorem dimH_initial_le (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3) :
    dimH (shiftedIntersection gasket (rotation angle) 0) ≤ ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) /
          Real.log 2) := by
  classical
  letI : Nonempty (States angle) := ⟨⟨{0}, ReachableState.initial⟩⟩
  have radius_ge_one := MoireSpectralGrowth.one_le_spectralRadius
    (adjacencyMatrix vertex gasket (rotation angle)) (outgoing_nonzero angle nonneg upper)
  have result := MoireHausdorffUpper.graph_dimH_le
    (fun (source : States angle) digit (target : States angle) =>
      Edge vertex gasket (rotation angle) source.val digit target.val)
    (fun source : States angle => stateIntersection gasket (rotation angle) source.val)
    (fun source point member => MoireDimension.norm_le_one_of_mem_gasket
      (stateIntersection_subset gasket (rotation angle) source.val member))
    (MoireGraphCovers.actual_graph_recursion angle) radius_ge_one
    (⟨{0}, ReachableState.initial⟩ : States angle)
  have matrix_eq : MoireGraphCovers.adjacency
      (fun (source : States angle) digit (target : States angle) =>
        Edge vertex gasket (rotation angle) source.val digit target.val) =
      adjacencyMatrix vertex gasket (rotation angle) := rfl
  rw [matrix_eq] at result
  simpa only [stateIntersection_singleton] using result

end

/-- Resonance supplies finiteness; the upper bound therefore has no extra
finite-graph hypothesis beyond the assumptions of Theorem 2.4. -/
theorem resonant_dimH_initial_le (angle : ℝ) (nonneg : 0 ≤ angle)
    (upper : angle ≤ Real.pi / 3)
    (resonant : Complex.exp (angle * Complex.I) ∈ MoireEisenstein.eisensteinField) :
    letI : Fintype (States angle) :=
      (MoireSection2Results.resonant_reachable_states_finite angle resonant).fintype
    letI : DecidableEq (States angle) := Classical.decEq _
    dimH (shiftedIntersection gasket (rotation angle) 0) ≤ ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) /
          Real.log 2) := by
  classical
  letI : Fintype (States angle) :=
    (MoireSection2Results.resonant_reachable_states_finite angle resonant).fintype
  letI : DecidableEq (States angle) := Classical.decEq _
  exact dimH_initial_le angle nonneg upper

end MoireActualUpper
