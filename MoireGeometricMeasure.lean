import MoirePathSupport
import MoireLabelledMeasure
import MoireActualUpper

namespace MoireGeometricMeasure

open MeasureTheory ProbabilityTheory MoireGeometry MoireSection2 MoireDeterminization

noncomputable section

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

def code (path : ℕ → State × Fin 3) : ℂ :=
  addressPoint vertex (fun length => (path (length + 1)).2)

theorem code_measurable : Measurable (code (State := State)) :=
  (MoireDimension.continuous_addressPoint vertex).measurable.comp (by fun_prop)

/-- The planar measure is the pushforward of the actual labelled-path law. -/
def geometricMeasure (edge : State → Fin 3 → State → Prop) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State × Fin 3) : Measure ℂ :=
  (MoirePathMeasure.pathMeasure (MoireLabelledMeasure.labelledAdjacency edge)
    (fun state => weights state.1) (fun state => weights_nonneg state.1) initial).map code

instance geometricMeasure_probability (edge : State → Fin 3 → State → Prop) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State × Fin 3) :
    IsProbabilityMeasure (geometricMeasure edge weights weights_nonneg initial) := by
  unfold geometricMeasure
  exact Measure.isProbabilityMeasure_map code_measurable.aemeasurable

/-- Almost every labelled path codes a point of its represented intersection. -/
theorem ae_code_mem (angle : ℝ) (represented : State → Finset ℂ)
    (nonempty : ∀ state, (stateIntersection gasket (rotation angle) (represented state)).Nonempty)
    (weights : State → ℝ) (weights_nonneg : ∀ state, 0 ≤ weights state)
    (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (MoireGraphCovers.adjacency
        (fun source digit target => Edge vertex gasket (rotation angle)
          (represented source) digit (represented target)) source target : ℝ) * weights target)
    (initial : State × Fin 3) (positive : 0 < weights initial.1) :
    ∀ᵐ path ∂MoirePathMeasure.pathMeasure
      (MoireLabelledMeasure.labelledAdjacency (fun source digit target =>
        Edge vertex gasket (rotation angle) (represented source) digit (represented target)))
      (fun state => weights state.1) (fun state => weights_nonneg state.1) initial,
      code path ∈ stateIntersection gasket (rotation angle) (represented initial.1) := by
  letI : Nonempty State := ⟨initial.1⟩
  have supported := MoireLabelledMeasure.ae_labelled_paths
    (fun source digit target => Edge vertex gasket (rotation angle)
      (represented source) digit (represented target)) weights weights_nonneg
    growth growth_pos subeigen initial positive
  filter_upwards [supported] with path legal
  have edges := fun length => (legal.2 length).2
  have member := MoireGraphCoding.addressPoint_mem_of_path angle
    (fun length => (path (length + 1)).2) (fun length => represented (path length).1) edges
    (fun length => nonempty (path length).1)
  simpa only [legal.1, code] using member

end

end MoireGeometricMeasure
