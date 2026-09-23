import MoirePathCylinders

namespace MoirePathSupport

open MeasureTheory ProbabilityTheory Filter

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

theorem ae_initial (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State) :
    ∀ᵐ path ∂MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial,
      path 0 = initial := by
  have history : ∀ᵐ history ∂(MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial).map
      (Preorder.frestrictLe 0), history ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = initial := by
    rw [MoirePathCylinders.initial_marginal]
    simp
  exact ae_of_ae_map (by fun_prop) history

theorem ae_step (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State)
    (good : State → Prop) (relation : State → State → Prop)
    (kernel_step : ∀ source, good source →
      ∀ᵐ target ∂MoirePathMeasure.transitionKernel adjacency weights weights_nonneg source,
        good target ∧ relation source target)
    (length : ℕ)
    (previous : ∀ᵐ path ∂MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial,
      good (path length)) :
    ∀ᵐ path ∂MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial,
      good (path (length + 1)) ∧ relation (path length) (path (length + 1)) := by
  have history : ∀ᵐ history ∂(MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial).map
      (Preorder.frestrictLe length), good (history ⟨length, Finset.mem_Iic.mpr le_rfl⟩) :=
    (ae_map_iff (by fun_prop) (Set.to_countable _).measurableSet).mpr previous
  have pair := Measure.ae_compProd_of_ae_ae
    (p := fun pair : (Finset.Iic length → State) × State =>
      good pair.2 ∧ relation (pair.1 ⟨length, Finset.mem_Iic.mpr le_rfl⟩) pair.2)
    (κ := MoirePathMeasure.historyKernel adjacency weights weights_nonneg length)
    (Set.to_countable _).measurableSet
    (history.mono fun past member => kernel_step _ member)
  change ∀ᵐ pair ∂(Kernel.trajMeasure (X := fun _ => State) (Measure.dirac initial)
    (MoirePathMeasure.historyKernel adjacency weights weights_nonneg)).map
      (Preorder.frestrictLe length) ⊗ₘ
        MoirePathMeasure.historyKernel adjacency weights weights_nonneg length, _ at pair
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure] at pair
  exact ae_of_ae_map (by fun_prop) pair

theorem ae_good_paths (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State)
    (good : State → Prop) (relation : State → State → Prop) (initial_good : good initial)
    (kernel_step : ∀ source, good source →
      ∀ᵐ target ∂MoirePathMeasure.transitionKernel adjacency weights weights_nonneg source,
        good target ∧ relation source target) :
    ∀ᵐ path ∂MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial,
      path 0 = initial ∧ ∀ length, good (path length) ∧ relation (path length) (path (length + 1)) := by
  have positive : ∀ length, ∀ᵐ path ∂MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial,
      good (path length) := by
    intro length
    induction length with
    | zero => exact (ae_initial adjacency weights weights_nonneg initial).mono fun path starts => starts ▸ initial_good
    | succ length ih =>
        exact (ae_step adjacency weights weights_nonneg initial good relation kernel_step length ih).mono
          (fun _ member => member.1)
  have edges : ∀ length, ∀ᵐ path ∂MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial,
      good (path length) ∧ relation (path length) (path (length + 1)) := by
    intro length
    filter_upwards [positive length,
      ae_step adjacency weights weights_nonneg initial good relation kernel_step length (positive length)]
      with path member step using ⟨member, step.2⟩
  filter_upwards [ae_initial adjacency weights weights_nonneg initial, ae_all_iff.mpr edges]
    with path starts legal using ⟨starts, legal⟩

variable [Nonempty State]

theorem transition_positive_support (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ source, growth * weights source ≤
      ∑ target, (adjacency source target : ℝ) * weights target)
    (source : State) (positive : 0 < weights source) :
    ∀ᵐ target ∂MoirePathMeasure.transitionKernel adjacency weights weights_nonneg source,
      0 < weights target ∧ adjacency source target ≠ 0 := by
  change ∀ᵐ target ∂(MoirePathMeasure.transitionPMF adjacency weights weights_nonneg source).toMeasure, _
  apply (mem_ae_iff_prob_eq_one (Set.to_countable _).measurableSet).mpr
  apply (PMF.toMeasure_apply_eq_one_iff _ (Set.to_countable _).measurableSet).mpr
  intro target member
  have mass_nonzero := (PMF.mem_support_iff _ _).mp member
  have outgoing := (MoireSpectralWeights.normalized_row_sum adjacency weights weights_nonneg
    growth growth_pos subeigen source positive).1
  rw [MoirePathMeasure.transitionPMF_apply _ _ _ _ _ outgoing] at mass_nonzero
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le] at mass_nonzero
  have product_positive : 0 < (adjacency source target : ℝ) * weights target :=
    (div_pos_iff_of_pos_right outgoing).mp mass_nonzero
  have target_positive : 0 < weights target := by
    by_contra! small
    have zero := le_antisymm small (weights_nonneg target)
    simp [zero] at product_positive
  refine ⟨target_positive, ?_⟩
  intro zero
  simp [zero] at product_positive

end MoirePathSupport
