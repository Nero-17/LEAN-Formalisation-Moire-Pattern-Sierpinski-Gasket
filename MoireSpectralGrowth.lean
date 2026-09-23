import MoireSpectralWeights

namespace MoireSpectralGrowth

open Filter Topology
open scoped Matrix.Norms.Operator NNReal ENNReal

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

/-- Gelfand's formula gives exponential bounds with every rate strictly above
the spectral radius, including for reducible matrices and Jordan blocks. -/
theorem eventually_norm_pow_lt (matrix : Matrix State State ℂ) (rate : ℝ)
    (larger : (spectralRadius ℂ matrix).toReal < rate) :
    ∀ᶠ length : ℕ in atTop, ‖matrix ^ length‖ < rate ^ length := by
  have finite_radius : spectralRadius ℂ matrix ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) matrix)
  have converges : Tendsto (fun length : ℕ => ‖matrix ^ length‖ ^ (1 / (length : ℝ)))
      atTop (𝓝 (spectralRadius ℂ matrix).toReal) := by
    have limit := (ENNReal.tendsto_toReal finite_radius).comp
      (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius matrix)
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
      using limit
  have rate_pos : 0 < rate := lt_of_le_of_lt ENNReal.toReal_nonneg larger
  filter_upwards [converges.eventually (gt_mem_nhds larger), eventually_gt_atTop 0]
    with length bound positive
  have positive_real : (0 : ℝ) < length := by exact_mod_cast positive
  have := (Real.rpow_inv_lt_iff_of_pos (norm_nonneg (matrix ^ length)) rate_pos.le
    positive_real).mp (by simpa only [one_div] using bound)
  simpa only [Real.rpow_natCast] using this

theorem row_sum_le_norm (matrix : Matrix State State ℕ) (source : State) :
    (∑ target, (matrix source target : ℝ)) ≤ ‖matrix.map (Nat.cast : ℕ → ℂ)‖ := by
  have bound := Finset.le_sup (f := fun row : State =>
    ∑ column : State, ‖(matrix row column : ℂ)‖₊) (Finset.mem_univ source)
  have cast_bound := (NNReal.coe_le_coe).mpr bound
  simpa only [Matrix.linfty_opNorm_def, Matrix.map_apply, NNReal.coe_sum,
    coe_nnnorm, Complex.norm_natCast] using cast_bound

/-- Counts of labelled walks from each state satisfy the spectral growth bound. -/
theorem eventually_row_sum_pow_lt (matrix : Matrix State State ℕ) (rate : ℝ)
    (larger : (spectralRadius ℂ (A := Matrix State State ℂ)
      (matrix.map (Nat.cast : ℕ → ℂ))).toReal < rate) :
    ∀ᶠ length : ℕ in atTop, ∀ source,
      (∑ target, ((matrix ^ length) source target : ℝ)) < rate ^ length := by
  filter_upwards [eventually_norm_pow_lt (matrix.map (Nat.cast : ℕ → ℂ)) rate larger]
    with length bound
  intro source
  apply lt_of_le_of_lt (row_sum_le_norm (matrix ^ length) source)
  change ‖(matrix ^ length).map (Nat.castRingHom ℂ)‖ < rate ^ length
  rw [Matrix.map_pow]
  exact bound

theorem one_le_row_sum_pow (matrix : Matrix State State ℕ)
    (outgoing : ∀ source, 1 ≤ ∑ target, matrix source target)
    (length : ℕ) (source : State) : 1 ≤ ∑ target, (matrix ^ length) source target := by
  induction length generalizing source with
  | zero => simp [Matrix.one_apply]
  | succ length ih =>
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      exact (outgoing source).trans (Finset.sum_le_sum fun target _ =>
        by simpa using Nat.mul_le_mul_left (matrix source target) (ih target))

/-- A finite graph with an outgoing edge at every vertex has spectral radius
at least one. This includes graphs with transient vertices. -/
theorem one_le_spectralRadius (matrix : Matrix State State ℕ)
    (outgoing : ∀ source, 1 ≤ ∑ target, matrix source target) :
    1 ≤ (spectralRadius ℂ (A := Matrix State State ℂ)
      (matrix.map (Nat.cast : ℕ → ℂ))).toReal := by
  by_contra! small
  obtain ⟨length, bound⟩ := (eventually_row_sum_pow_lt matrix 1 small).exists
  let source : State := Classical.arbitrary State
  have lower : (1 : ℝ) ≤ ∑ target, ((matrix ^ length) source target : ℝ) := by
    exact_mod_cast one_le_row_sum_pow matrix outgoing length source
  simpa using lt_of_le_of_lt lower (bound source)

end MoireSpectralGrowth
