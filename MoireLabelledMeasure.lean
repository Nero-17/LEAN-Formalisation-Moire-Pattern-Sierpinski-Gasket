import MoirePathCylinders
import MoirePathSupport
import MoireGraphCovers

namespace MoireLabelledMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Remembering the most recent blue label separates parallel edges. -/
def labelledAdjacency (edge : State → Fin 3 → State → Prop) :
    Matrix (State × Fin 3) (State × Fin 3) ℕ := by
  classical
  exact fun source target => if edge source.1 target.2 target.1 then 1 else 0

theorem labelled_row_sum (edge : State → Fin 3 → State → Prop) (weights : State → ℝ)
    (source : State × Fin 3) :
    (∑ target, (labelledAdjacency edge source target : ℝ) * weights target.1) =
      ∑ target, (MoireGraphCovers.adjacency edge source.1 target : ℝ) * weights target := by
  classical
  simp only [Fintype.sum_prod_type, labelledAdjacency, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, ite_mul, one_mul, zero_mul, MoireGraphCovers.adjacency]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.sum_filter]
  simp

variable [MeasurableSpace State] [MeasurableSingletonClass State] [Nonempty State]

theorem ae_labelled_paths (edge : State → Fin 3 → State → Prop) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (MoireGraphCovers.adjacency edge source target : ℝ) * weights target)
    (initial : State × Fin 3) (positive : 0 < weights initial.1) :
    ∀ᵐ path ∂MoirePathMeasure.pathMeasure (labelledAdjacency edge)
      (fun state => weights state.1) (fun state => weights_nonneg state.1) initial,
      path 0 = initial ∧ ∀ time, 0 < weights (path time).1 ∧
        edge (path time).1 (path (time + 1)).2 (path (time + 1)).1 := by
  have rows : ∀ source : State × Fin 3, growth * weights source.1 ≤
      ∑ target, (labelledAdjacency edge source target : ℝ) * weights target.1 := by
    intro source
    rw [labelled_row_sum]
    exact subeigen source.1
  have supported : ∀ᵐ path ∂MoirePathMeasure.pathMeasure (labelledAdjacency edge)
      (fun state => weights state.1) (fun state => weights_nonneg state.1) initial,
      path 0 = initial ∧ ∀ time, 0 < weights (path time).1 ∧
        labelledAdjacency edge (path time) (path (time + 1)) ≠ 0 := by
    apply MoirePathSupport.ae_good_paths (labelledAdjacency edge)
      (fun state => weights state.1) (fun state => weights_nonneg state.1) initial
      (fun state => 0 < weights state.1)
      (fun source target => labelledAdjacency edge source target ≠ 0) positive
    intro source source_positive
    exact MoirePathSupport.transition_positive_support (labelledAdjacency edge)
      (fun state => weights state.1) (fun state => weights_nonneg state.1)
      growth growth_pos rows source source_positive
  filter_upwards [supported] with path legal
  refine ⟨legal.1, fun time => ⟨(legal.2 time).1, ?_⟩⟩
  have step := (legal.2 time).2
  by_contra absent
  simp only [labelledAdjacency, if_neg absent, ne_eq, not_true_eq_false] at step

/-- For a matrix with single labelled edges, the finite-product estimate is a
bound on the mass of a cylinder in the genuine countably additive path measure. -/
theorem cylinder_mass_bound (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ state, growth * weights state ≤
      ∑ target, (adjacency state target : ℝ) * weights target)
    (path : ℕ → State) (path_positive : ∀ level, 0 < weights (path level))
    (single_edges : ∀ level, adjacency (path level) (path (level + 1)) = 1) (length : ℕ) :
    MoirePathMeasure.pathMeasure adjacency weights weights_nonneg (path 0)
      (MoirePathCylinders.cylinder path length) ≤
        ENNReal.ofReal (weights (path length) / (growth ^ length * weights (path 0))) := by
  rw [MoirePathCylinders.cylinder_measure_product adjacency weights weights_nonneg
    (path 0) path rfl length]
  have transition : ∀ level,
      MoirePathMeasure.transitionPMF adjacency weights weights_nonneg (path level) (path (level + 1)) =
        ENNReal.ofReal (weights (path (level + 1)) /
          (∑ target, (adjacency (path level) target : ℝ) * weights target)) := by
    intro level
    rw [MoirePathMeasure.transitionPMF_apply adjacency weights weights_nonneg _ _
      (MoireSpectralWeights.normalized_row_sum adjacency weights weights_nonneg growth growth_pos
        subeigen (path level) (path_positive level)).1, single_edges]
    simp
  simp_rw [transition]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · exact ENNReal.ofReal_le_ofReal (MoireSpectralWeights.path_probability_bound
      adjacency weights weights_nonneg growth growth_pos subeigen path path_positive length)
  · intro level _
    exact (MoireSpectralWeights.normalized_row_sum adjacency weights weights_nonneg growth growth_pos
      subeigen (path level) (path_positive level)).2.2 (path (level + 1)) |>.1

end

end MoireLabelledMeasure
