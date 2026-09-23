import MoireSpectralWeights
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

namespace MoirePathMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

noncomputable def transitionPMF (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (source : State) : PMF State := by
  classical
  by_cases outgoing_pos : 0 < ∑ target, (adjacency source target : ℝ) * weights target
  · refine PMF.ofFintype (fun target => ENNReal.ofReal
      ((adjacency source target : ℝ) * weights target /
        (∑ next, (adjacency source next : ℝ) * weights next))) ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun target _ =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (weights_nonneg target)) outgoing_pos.le)]
    rw [← Finset.sum_div, div_self (ne_of_gt outgoing_pos), ENNReal.ofReal_one]
  · exact PMF.pure source

theorem transitionPMF_apply (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (source target : State)
    (outgoing_pos : 0 < ∑ next, (adjacency source next : ℝ) * weights next) :
    transitionPMF adjacency weights weights_nonneg source target = ENNReal.ofReal
      ((adjacency source target : ℝ) * weights target /
        (∑ next, (adjacency source next : ℝ) * weights next)) := by
  simp [transitionPMF, outgoing_pos, PMF.ofFintype_apply]

noncomputable def transitionKernel (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) : Kernel State State where
  toFun source := (transitionPMF adjacency weights weights_nonneg source).toMeasure
  measurable' := measurable_of_countable _

instance transitionKernel_markov (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) :
    IsMarkovKernel (transitionKernel adjacency weights weights_nonneg) :=
  ⟨fun source => PMF.toMeasure.isProbabilityMeasure _⟩

noncomputable def historyKernel (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (level : ℕ) :
    Kernel (Finset.Iic level → State) State :=
  (transitionKernel adjacency weights weights_nonneg).comap
    (fun history => history ⟨level, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance historyKernel_markov (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (level : ℕ) :
    IsMarkovKernel (historyKernel adjacency weights weights_nonneg level) := by
  unfold historyKernel
  infer_instance

/-- An actual countably additive probability measure on infinite state paths. -/
noncomputable def pathMeasure (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initialState : State) :
    Measure (ℕ → State) :=
  Kernel.trajMeasure (X := fun _ => State) (Measure.dirac initialState)
    (historyKernel adjacency weights weights_nonneg)

instance pathMeasure_probability (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initialState : State) :
    IsProbabilityMeasure (pathMeasure adjacency weights weights_nonneg initialState) := by
  unfold pathMeasure
  infer_instance

end MoirePathMeasure
