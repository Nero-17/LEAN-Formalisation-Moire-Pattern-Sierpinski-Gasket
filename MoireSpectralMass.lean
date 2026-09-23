import MoireSmallBalls
import MoireGeometricMeasure

namespace MoireSpectralMass

open MeasureTheory ProbabilityTheory MoireDeterministicPaths MoireLabelledMeasure
open scoped ENNReal

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

theorem blueWord_mass_bound (edge : State → Fin 3 → State → Prop)
    (deterministic : ∀ source digit first second, edge source digit first →
      edge source digit second → first = second)
    (weights : State → ℝ) (weights_nonneg : ∀ state, 0 ≤ weights state)
    (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (MoireGraphCovers.adjacency edge source target : ℝ) * weights target)
    (initial : State × Fin 3) (positive : 0 < weights initial.1)
    (length : ℕ) (word : Fin length → Fin 3) :
    MoirePathMeasure.pathMeasure (labelledAdjacency edge)
      (fun state => weights state.1) (fun state => weights_nonneg state.1) initial
      {path | blueWord path length = word} ≤
        ENNReal.ofReal ((∑ state, weights state) / (growth ^ length * weights initial.1)) := by
  let good : Set (ℕ → State × Fin 3) := {path | path 0 = initial ∧
    ∀ time, 0 < weights (path time).1 ∧ edge (path time).1 (path (time + 1)).2 (path (time + 1)).1}
  have full : ∀ᵐ path ∂MoirePathMeasure.pathMeasure (labelledAdjacency edge)
      (fun state => weights state.1) (fun state => weights_nonneg state.1) initial, path ∈ good :=
    ae_labelled_paths edge weights weights_nonneg growth growth_pos subeigen initial positive
  have rows : ∀ source : State × Fin 3, growth * weights source.1 ≤
      ∑ target, (labelledAdjacency edge source target : ℝ) * weights target.1 := by
    intro source
    rw [labelled_row_sum]
    exact subeigen source.1
  apply blueWord_mass_le _ edge deterministic good full initial (fun _ member => member.1)
    (fun _ member time => (member.2 time).2) length _ ?_ word
  intro path member
  have estimate := cylinder_mass_bound (labelledAdjacency edge)
    (fun state => weights state.1) (fun state => weights_nonneg state.1) growth growth_pos rows path
    (fun time => (member.2 time).1)
    (fun time => by simp only [labelledAdjacency, if_pos (member.2 time).2]) length
  rw [member.1] at estimate
  apply estimate.trans
  apply ENNReal.ofReal_le_ofReal
  exact div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun state _ => weights_nonneg state) (Finset.mem_univ _))
    (mul_nonneg (pow_nonneg growth_pos.le _) positive.le)

/-- The actual planar probability measure has the required spectral small-ball
decay at every dyadic scale. -/
theorem geometric_dyadic_ball_mass (edge : State → Fin 3 → State → Prop)
    (deterministic : ∀ source digit first second, edge source digit first →
      edge source digit second → first = second)
    (weights : State → ℝ) (weights_nonneg : ∀ state, 0 ≤ weights state)
    (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (MoireGraphCovers.adjacency edge source target : ℝ) * weights target)
    (initial : State × Fin 3) (positive : 0 < weights initial.1)
    (length : ℕ) (center : ℂ) :
    MoireGeometricMeasure.geometricMeasure edge weights weights_nonneg initial
      (Metric.closedBall center ((1 / 2 : ℝ) ^ length)) ≤
        289 * ENNReal.ofReal ((∑ state, weights state) / (growth ^ length * weights initial.1)) := by
  unfold MoireGeometricMeasure.geometricMeasure
  rw [Measure.map_apply MoireGeometricMeasure.code_measurable measurableSet_closedBall]
  exact MoireSmallBalls.dyadic_ball_mass_le _ length _
    (blueWord_mass_bound edge deterministic weights weights_nonneg growth growth_pos subeigen
      initial positive length) center

end MoireSpectralMass
