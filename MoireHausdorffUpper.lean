import MoireGraphCovers
import MoireSpectralGrowth

namespace MoireHausdorffUpper

open Filter Topology MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal NNReal

noncomputable section

private theorem cost_identity (rate dimension : ℝ) (length : ℕ) :
    rate ^ length * (2 * (1 / 2 : ℝ) ^ length) ^ dimension =
      (2 : ℝ) ^ dimension * (rate * (1 / 2 : ℝ) ^ dimension) ^ length := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_comm (length : ℝ) dimension, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_pow]
  ring

/-- Finite covers whose diameter costs vanish force the actual Hausdorff measure
to vanish. The number of covering balls may vary at each level. -/
theorem measure_zero_of_list_covers (set : Set ℂ) (centers : ℕ → List ℂ)
    (radius : ℕ → ℝ≥0∞) (radius_zero : Tendsto radius atTop (𝓝 0))
    (cover : ∀ level, ∀ point ∈ set, ∃ center ∈ centers level,
      edist point center ≤ radius level)
    (dimension : ℝ) (dimension_nonneg : 0 ≤ dimension)
    (cost_zero : Tendsto (fun level => ((centers level).length : ℝ≥0∞) *
      (2 * radius level) ^ dimension) atTop (𝓝 0)) :
    hausdorffMeasure dimension set = 0 := by
  let balls := fun level (index : Fin (centers level).length) =>
    closedEBall ((centers level).get index) (radius level)
  have covered : ∀ level, set ⊆ ⋃ index, balls level index := by
    intro level point member
    obtain ⟨center, member, bound⟩ := cover level point member
    obtain ⟨index, equality⟩ := List.mem_iff_get.mp member
    apply Set.mem_iUnion.mpr
    refine ⟨index, ?_⟩
    change edist point ((centers level).get index) ≤ radius level
    rw [equality]
    exact bound
  have diameter : ∀ level index, ediam (balls level index) ≤ 2 * radius level :=
    fun _ _ => ediam_closedEBall_le
  have costs_bound : ∀ level, (∑ index, ediam (balls level index) ^ dimension) ≤
      ((centers level).length : ℝ≥0∞) * (2 * radius level) ^ dimension := by
    intro level
    calc
      _ ≤ ∑ _index : Fin (centers level).length, (2 * radius level) ^ dimension :=
        Finset.sum_le_sum fun index _ => ENNReal.rpow_le_rpow (diameter level index) dimension_nonneg
      _ = _ := by simp
  have costs_zero : Tendsto (fun level => ∑ index, ediam (balls level index) ^ dimension)
      atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds cost_zero (fun _ => bot_le) costs_bound
  have bound := hausdorffMeasure_le_liminf_sum dimension set
    (fun level => 2 * radius level)
    (by simpa using ENNReal.Tendsto.const_mul radius_zero (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ⊤))) balls
    (Eventually.of_forall diameter) (Eventually.of_forall covered)
  rw [costs_zero.liminf_eq] at bound
  exact le_antisymm bound bot_le

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

open scoped Matrix.Norms.Operator

/-- The spectral upper bound for the actual Hausdorff measure of a finite
graph of gasket similarities. No separation assumption is needed for this direction. -/
theorem graph_hausdorffMeasure_zero
    (edge : State → Fin 3 → State → Prop) (sets : State → Set ℂ)
    (bounded : ∀ source, ∀ point ∈ sets source, ‖point‖ ≤ 1)
    (recursion : ∀ source, sets source ⊆ ⋃ target, ⋃ digit,
      ⋃ (_ : edge source digit target),
        MoireSection2.cornerMap MoireGeometry.vertex digit '' sets target)
    (dimension : ℝ) (dimension_nonneg : 0 ≤ dimension)
    (spectral_lt : (spectralRadius ℂ (A := Matrix State State ℂ)
      ((MoireGraphCovers.adjacency edge).map (Nat.cast : ℕ → ℂ))).toReal <
        (2 : ℝ) ^ dimension) (source : State) :
    hausdorffMeasure dimension (sets source) = 0 := by
  classical
  obtain ⟨rate, spectral_rate, rate_lt⟩ := exists_between spectral_lt
  have rate_pos : 0 < rate := lt_of_le_of_lt ENNReal.toReal_nonneg spectral_rate
  have discounted_lt : rate * (1 / 2 : ℝ) ^ dimension < 1 := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, ← div_eq_mul_one_div]
    exact (div_lt_one (Real.rpow_pos_of_pos (by norm_num) _)).mpr rate_lt
  have real_cost_zero : Tendsto (fun level : ℕ =>
      (2 : ℝ) ^ dimension * (rate * (1 / 2 : ℝ) ^ dimension) ^ level) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (mul_nonneg rate_pos.le (Real.rpow_nonneg (by norm_num) _)) discounted_lt).const_mul
        ((2 : ℝ) ^ dimension)
  have enn_cost_zero := ENNReal.tendsto_ofReal real_cost_zero
  have count_bound := MoireSpectralGrowth.eventually_row_sum_pow_lt
    (MoireGraphCovers.adjacency edge) rate spectral_rate
  apply measure_zero_of_list_covers (sets source)
    (fun level => MoireGraphCovers.centers edge level source)
    (fun level => ENNReal.ofReal ((1 / 2 : ℝ) ^ level))
  · simpa using ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  · intro level point member
    obtain ⟨center, center_mem, bound⟩ :=
      MoireGraphCovers.centers_cover edge sets bounded recursion level source point member
    exact ⟨center, center_mem, by simpa only [edist_dist] using ENNReal.ofReal_le_ofReal bound⟩
  · exact dimension_nonneg
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero, bot_eq_zero] using enn_cost_zero)
      (Eventually.of_forall fun _ => bot_le)
    filter_upwards [count_bound] with level bound
    have card_bound : ((MoireGraphCovers.centers edge level source).length : ℝ) ≤ rate ^ level := by
      rw [MoireGraphCovers.centers_length, Nat.cast_sum]
      exact (bound source).le
    calc
      _ ≤ ENNReal.ofReal (rate ^ level) *
          (2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ level)) ^ dimension :=
        mul_le_mul_right' (by simpa using ENNReal.ofReal_le_ofReal card_bound) _
      _ = ENNReal.ofReal ((2 : ℝ) ^ dimension *
          (rate * (1 / 2 : ℝ) ^ dimension) ^ level) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) dimension_nonneg,
          ← ENNReal.ofReal_mul (pow_nonneg rate_pos.le _), cost_identity]

/-- The Hausdorff dimension is bounded by the spectral exponent. -/
theorem graph_dimH_le
    (edge : State → Fin 3 → State → Prop) (sets : State → Set ℂ)
    (bounded : ∀ source, ∀ point ∈ sets source, ‖point‖ ≤ 1)
    (recursion : ∀ source, sets source ⊆ ⋃ target, ⋃ digit,
      ⋃ (_ : edge source digit target),
        MoireSection2.cornerMap MoireGeometry.vertex digit '' sets target)
    (radius_ge_one : 1 ≤ (spectralRadius ℂ (A := Matrix State State ℂ)
      ((MoireGraphCovers.adjacency edge).map (Nat.cast : ℕ → ℂ))).toReal)
    (source : State) :
    dimH (sets source) ≤ ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix State State ℂ)
        ((MoireGraphCovers.adjacency edge).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) := by
  have log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have exponent_nonneg := div_nonneg (Real.log_nonneg radius_ge_one) log_two_pos.le
  apply dimH_le
  intro dimension infinite
  by_contra! greater
  have exponent_lt := (ENNReal.ofReal_lt_coe_iff exponent_nonneg).mp greater
  have radius_pos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) radius_ge_one
  have spectral_lt := (Real.lt_rpow_iff_log_lt radius_pos (by norm_num : (0 : ℝ) < 2)).mpr
    ((div_lt_iff₀ log_two_pos).mp exponent_lt)
  have zero := graph_hausdorffMeasure_zero edge sets bounded recursion dimension
    dimension.coe_nonneg spectral_lt source
  exact ENNReal.zero_ne_top (zero.symm.trans infinite)

end

end MoireHausdorffUpper
