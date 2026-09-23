import MoireBoxBounds
import MoireBoxSimilarity

namespace MoireBoxEquality

open MoireBoxDimension MoireGeometry MoireSection2 MoireDeterminization MoireActualUpper MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.Operator

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

theorem represented_lowerExponent (angle : ℝ) (represented : State → Finset ℂ)
    (injective : Function.Injective represented)
    (nonempty : ∀ state, (stateIntersection gasket (rotation angle) (represented state)).Nonempty)
    (weights : State → ℝ) (weights_nonneg : ∀ state, 0 ≤ weights state)
    (growth : ℝ) (growth_gt_one : 1 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (MoireGraphCovers.adjacency
        (fun source digit target => Edge vertex gasket (rotation angle)
          (represented source) digit (represented target)) source target : ℝ) * weights target)
    (initial : State × Fin 3) (positive : 0 < weights initial.1) :
    LowerExponent (stateIntersection gasket (rotation angle) (represented initial.1))
      ⟨Real.log growth / Real.log 2,
        div_nonneg (Real.log_nonneg growth_gt_one.le) (Real.log_pos (by norm_num)).le⟩ := by
  letI : Nonempty State := ⟨initial.1⟩
  let edge : State → Fin 3 → State → Prop := fun source digit target =>
    Edge vertex gasket (rotation angle) (represented source) digit (represented target)
  let measure := MoireGeometricMeasure.geometricMeasure edge weights weights_nonneg initial
  have deterministic : ∀ source digit first second, edge source digit first → edge source digit second → first = second := by
    intro source digit first second first_edge second_edge
    exact injective (edge_deterministic vertex gasket (rotation angle) first_edge second_edge)
  have growth_pos : 0 < growth := lt_trans zero_lt_one growth_gt_one
  have sum_pos : 0 < ∑ state, weights state := positive.trans_le
    (Finset.single_le_sum (fun state _ => weights_nonneg state) (Finset.mem_univ initial.1))
  have mass_one : measure (stateIntersection gasket (rotation angle) (represented initial.1)) = 1 := by
    have supported := MoireGeometricMeasure.ae_code_mem angle represented nonempty weights weights_nonneg
      growth growth_pos subeigen initial positive
    have measurable := (MoireGraphGeometry.stateIntersection_isCompact angle (represented initial.1)).measurableSet
    change (MoireGeometricMeasure.geometricMeasure edge weights weights_nonneg initial) _ = 1
    rw [MoireGeometricMeasure.geometricMeasure,
      Measure.map_apply MoireGeometricMeasure.code_measurable measurable]
    exact (mem_ae_iff_prob_eq_one (measurable.preimage MoireGeometricMeasure.code_measurable)).mp supported
  apply MoireBoxBounds.lowerExponent_of_dyadic_mass measure _ mass_one _
    (289 * (∑ state, weights state) / weights initial.1) (by positivity)
  intro length center
  have bound := MoireSpectralMass.geometric_dyadic_ball_mass edge deterministic weights weights_nonneg
    growth growth_pos subeigen initial positive length center
  apply bound.trans_eq
  change _ = ENNReal.ofReal ((289 * (∑ state, weights state) / weights initial.1) *
    ((1 / 2 : ℝ) ^ length) ^ (Real.log growth / Real.log 2))
  rw [MoireHausdorffLower.dyadic_spectral_power growth growth_pos length,
    ← ENNReal.ofReal_ofNat 289, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  field_simp

section Actual

variable (angle : ℝ) [Fintype (States angle)] [DecidableEq (States angle)]

theorem box_dimensions_eq (nonneg : 0 ≤ angle) (upper : angle ≤ Real.pi / 3) :
    lowerBoxDimension (shiftedIntersection gasket (rotation angle) 0) = ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) ∧
    upperBoxDimension (shiftedIntersection gasket (rotation angle) 0) = ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) := by
  classical
  letI : Nonempty (States angle) := ⟨⟨{0}, ReachableState.initial⟩⟩
  have radius_ge_one := MoireSpectralGrowth.one_le_spectralRadius
    (adjacencyMatrix vertex gasket (rotation angle)) (outgoing_nonzero angle nonneg upper)
  have upper_bound := MoireBoxBounds.graph_upperBox_le
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
  rw [matrix_eq, stateIntersection_singleton] at upper_bound
  have lower_bound : ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix (States angle) (States angle) ℂ)
        ((adjacencyMatrix vertex gasket (rotation angle)).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) ≤
      lowerBoxDimension (shiftedIntersection gasket (rotation angle) 0) := by
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
      have lower := represented_lowerExponent angle (fun state : States angle => state.val) Subtype.val_injective
        (fun state => MoireGraphGeometry.reachable_state_nonempty angle nonneg upper state.val state.property)
        weights weights_nonneg _ growth_gt_one subeigen (state, 0) positive
      have initial_lower := MoireBoxSimilarity.reachable_lowerExponent_initial angle state.val state.property _ lower
      have result := le_iSup₂ (f := fun dimension : ℝ≥0 =>
        fun _ : LowerExponent (shiftedIntersection gasket (rotation angle) 0) dimension =>
          (dimension : ℝ≥0∞)) _ initial_lower
      rw [← ENNReal.ofReal_coe_nnreal] at result
      exact result
    · have radius_eq := le_antisymm (le_of_not_gt growth_gt_one) radius_ge_one
      simp only [radius_eq, Real.log_one, zero_div, ENNReal.ofReal_zero]
      exact bot_le
  have comparison := lowerBoxDimension_le_upperBoxDimension (shiftedIntersection gasket (rotation angle) 0)
  exact ⟨le_antisymm (comparison.trans upper_bound) lower_bound,
    le_antisymm upper_bound (lower_bound.trans comparison)⟩

end Actual

end MoireBoxEquality
