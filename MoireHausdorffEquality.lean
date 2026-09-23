import MoireHausdorffLower

namespace MoireHausdorffEquality

open MoireGeometry MoireSection2 MoireDeterminization MoireActualUpper
open scoped Matrix.Norms.Operator

theorem reachable_dimH_le_initial (angle : ℝ) (state : Finset ℂ)
    (reachable : ReachableState vertex gasket (rotation angle) state) :
    dimH (stateIntersection gasket (rotation angle) state) ≤
      dimH (shiftedIntersection gasket (rotation angle) 0) := by
  induction reachable with
  | initial => simp
  | @step source target previous digit edge ih =>
      have contained : cornerMap vertex digit '' stateIntersection gasket (rotation angle) target ⊆
          stateIntersection gasket (rotation angle) source := by
        intro point member
        rw [gasket_state_recursion angle source]
        exact Set.mem_iUnion.mpr ⟨digit, by simpa only [← edge.1] using member⟩
      rw [← MoireDimension.dimH_cornerMap_image vertex digit]
      exact (dimH_mono contained).trans ih

variable (angle : ℝ) [Fintype (States angle)] [DecidableEq (States angle)]

/-- The actual Hausdorff-dimension equality in Theorem 2.4. -/
theorem hausdorff_dimension_eq (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3) :
    dimH (shiftedIntersection gasket (rotation angle) 0) = ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) /
          Real.log 2) := by
  classical
  letI : Nonempty (States angle) := ⟨⟨{0}, ReachableState.initial⟩⟩
  apply le_antisymm (dimH_initial_le angle nonneg upper)
  have radius_ge_one := MoireSpectralGrowth.one_le_spectralRadius
    (adjacencyMatrix vertex gasket (rotation angle)) (outgoing_nonzero angle nonneg upper)
  by_cases growth_gt_one : 1 < (spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
      ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal
  · letI : MeasurableSpace (States angle) := ⊤
    letI : MeasurableSingletonClass (States angle) := ⟨fun _ => trivial⟩
    obtain ⟨weights, weights_nonneg, weights_nonzero, subeigen⟩ :=
      MoireSpectralWeights.exists_nonnegative_spectral_weights (adjacencyMatrix vertex gasket (rotation angle))
    have positive_somewhere : ∃ state, 0 < weights state := by
      by_contra! absent
      apply weights_nonzero
      funext state
      exact le_antisymm (absent state) (weights_nonneg state)
    obtain ⟨state, positive⟩ := positive_somewhere
    have lower := MoireHausdorffLower.represented_dimH_lower angle
      (fun state : States angle => state.val) Subtype.val_injective
      (fun state => MoireGraphGeometry.reachable_state_nonempty angle nonneg upper state.val state.property)
      weights weights_nonneg _ growth_gt_one subeigen (state, 0) positive
    exact lower.trans (reachable_dimH_le_initial angle state.val state.property)
  · have radius_eq := le_antisymm (le_of_not_gt growth_gt_one) radius_ge_one
    simp only [radius_eq, Real.log_one, zero_div, ENNReal.ofReal_zero]
    exact bot_le

end MoireHausdorffEquality
