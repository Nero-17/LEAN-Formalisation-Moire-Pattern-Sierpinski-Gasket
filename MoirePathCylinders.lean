import MoirePathMeasure

namespace MoirePathCylinders

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {State : Type*} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The cylinder fixes the state at each time from zero through `length`. -/
def cylinder (path : ℕ → State) (length : ℕ) : Set (ℕ → State) :=
  {sample | ∀ time ≤ length, sample time = path time}

theorem cylinder_eq_preimage (path : ℕ → State) (length : ℕ) :
    cylinder path length = (fun sample : ℕ → State => fun time : Finset.Iic length => sample time) ⁻¹'
      {fun time : Finset.Iic length => path time} := by
  ext sample
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
  constructor
  · intro agree time
    exact agree time (Finset.mem_Iic.mp time.property)
  · intro agree time bound
    exact agree ⟨time, Finset.mem_Iic.mpr bound⟩

theorem cylinder_measurable (path : ℕ → State) (length : ℕ) :
    MeasurableSet (cylinder path length) := by
  rw [cylinder_eq_preimage]
  exact (measurableSet_singleton _).preimage (by fun_prop)

theorem cylinder_succ_eq_preimage (path : ℕ → State) (length : ℕ) :
    cylinder path (length + 1) =
      (fun sample : ℕ → State => ((fun time : Finset.Iic length => sample time), sample (length + 1))) ⁻¹'
        ({fun time : Finset.Iic length => path time} ×ˢ {path (length + 1)}) := by
  ext sample
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod,
    Set.mem_singleton_iff, funext_iff]
  constructor
  · intro agree
    exact ⟨fun time => agree time (Nat.le_trans (Finset.mem_Iic.mp time.property) (Nat.le_succ _)),
      agree _ le_rfl⟩
  · rintro ⟨agree, last⟩ time bound
    rcases Nat.eq_or_lt_of_le bound with equal | less
    · simpa [equal] using last
    · exact agree ⟨time, Finset.mem_Iic.mpr (Nat.le_of_lt_succ less)⟩

/-- The trajectory measure assigns cylinder probabilities by the actual
one-step kernel, rather than merely satisfying a formal product inequality. -/
theorem cylinder_measure_succ (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State)
    (path : ℕ → State) (length : ℕ) :
    MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial (cylinder path (length + 1)) =
      MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial (cylinder path length) *
        MoirePathMeasure.transitionPMF adjacency weights weights_nonneg (path length) (path (length + 1)) := by
  have marginal := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => State) (μ₀ := Measure.dirac initial)
    (κ := MoirePathMeasure.historyKernel adjacency weights weights_nonneg)
    (a := length)
  have evaluation := congrArg (fun measure => measure
    ({fun time : Finset.Iic length => path time} ×ˢ {path (length + 1)})) marginal
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply (by fun_prop)
      ((measurableSet_singleton _).prod (measurableSet_singleton _))] at evaluation
  rw [cylinder_succ_eq_preimage]
  simp only [Preorder.frestrictLe, Finset.restrict_def, MoirePathMeasure.pathMeasure] at evaluation ⊢
  rw [← evaluation]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  change _ * MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial
    ((fun sample : ℕ → State => fun time : Finset.Iic length => sample time) ⁻¹'
      {fun time : Finset.Iic length => path time}) = _
  rw [← cylinder_eq_preimage]
  change (MoirePathMeasure.transitionPMF adjacency weights weights_nonneg (path length)).toMeasure
      {path (length + 1)} * _ = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact mul_comm _ _

theorem initial_marginal (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State) :
    (MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial).map
      (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 => initial) := by
  unfold MoirePathMeasure.pathMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (by fun_prop)]
  rfl

theorem cylinder_measure_zero (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State)
    (path : ℕ → State) (starts : path 0 = initial) :
    MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial (cylinder path 0) = 1 := by
  have law := congrArg (fun measure => measure {fun time : Finset.Iic 0 => path time})
    (initial_marginal adjacency weights weights_nonneg initial)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at law
  rw [cylinder_eq_preimage]
  have history_eq : (fun time : Finset.Iic 0 => path time) = fun _ => initial := by
    funext time
    have time_zero : (time : ℕ) = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp time.property)
    simpa only [time_zero] using starts
  simpa only [Preorder.frestrictLe, Finset.restrict_def, history_eq,
    Measure.dirac_apply_of_mem (Set.mem_singleton _)] using law

theorem cylinder_measure_product (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (initial : State)
    (path : ℕ → State) (starts : path 0 = initial) (length : ℕ) :
    MoirePathMeasure.pathMeasure adjacency weights weights_nonneg initial (cylinder path length) =
      ∏ time ∈ Finset.range length,
        MoirePathMeasure.transitionPMF adjacency weights weights_nonneg (path time) (path (time + 1)) := by
  induction length with
  | zero => simpa using cylinder_measure_zero adjacency weights weights_nonneg initial path starts
  | succ length ih => rw [cylinder_measure_succ, ih, Finset.prod_range_succ]

end MoirePathCylinders
