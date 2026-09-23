import MoireBoxDimension

namespace MoireBoxBounds

open MoireBoxDimension MoireGeometry MoireSection2 MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix.Norms.Operator

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

theorem graph_upperExponent (edge : State → Fin 3 → State → Prop) (sets : State → Set ℂ)
    (bounded : ∀ source, ∀ point ∈ sets source, ‖point‖ ≤ 1)
    (recursion : ∀ source, sets source ⊆ ⋃ target, ⋃ digit,
      ⋃ (_ : edge source digit target), cornerMap vertex digit '' sets target)
    (dimension : ℝ≥0)
    (spectral_lt : (spectralRadius ℂ (A := Matrix State State ℂ)
      ((MoireGraphCovers.adjacency edge).map (Nat.cast : ℕ → ℂ))).toReal < (2 : ℝ) ^ (dimension : ℝ))
    (source : State) : UpperExponent (sets source) dimension := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards [MoireSpectralGrowth.eventually_row_sum_pow_lt
    (MoireGraphCovers.adjacency edge) ((2 : ℝ) ^ (dimension : ℝ)) spectral_lt] with length bound
  refine ⟨MoireGraphCovers.centers edge length source,
    MoireGraphCovers.centers_cover edge sets bounded recursion length source, ?_⟩
  simpa only [MoireGraphCovers.centers_length, Nat.cast_sum, one_mul] using (bound source).le

theorem graph_upperBox_le (edge : State → Fin 3 → State → Prop) (sets : State → Set ℂ)
    (bounded : ∀ source, ∀ point ∈ sets source, ‖point‖ ≤ 1)
    (recursion : ∀ source, sets source ⊆ ⋃ target, ⋃ digit,
      ⋃ (_ : edge source digit target), cornerMap vertex digit '' sets target)
    (radius_ge_one : 1 ≤ (spectralRadius ℂ (A := Matrix State State ℂ)
      ((MoireGraphCovers.adjacency edge).map (Nat.cast : ℕ → ℂ))).toReal)
    (source : State) : upperBoxDimension (sets source) ≤ ENNReal.ofReal
      (Real.log ((spectralRadius ℂ (A := Matrix State State ℂ)
        ((MoireGraphCovers.adjacency edge).map (Nat.cast : ℕ → ℂ))).toReal) / Real.log 2) := by
  have log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have exponent_nonneg := div_nonneg (Real.log_nonneg radius_ge_one) log_two_pos.le
  apply le_of_forall_gt_imp_ge_of_dense
  intro bound greater
  obtain ⟨dimension, exponent_lt, dimension_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp greater
  have spectral_lt := (Real.lt_rpow_iff_log_lt
    (lt_of_lt_of_le zero_lt_one radius_ge_one) (by norm_num : (0 : ℝ) < 2)).mpr
      ((div_lt_iff₀ log_two_pos).mp ((ENNReal.ofReal_lt_coe_iff exponent_nonneg).mp exponent_lt))
  exact (iInf₂_le dimension (graph_upperExponent edge sets bounded recursion dimension spectral_lt source)).trans
    dimension_lt.le

/-- A probability mass bound gives a lower bound for every finite ball cover. -/
theorem lowerExponent_of_dyadic_mass (measure : Measure ℂ) (set : Set ℂ)
    (mass_one : measure set = 1) (dimension : ℝ≥0) (constant : ℝ) (positive : 0 < constant)
    (balls : ∀ length center, measure (Metric.closedBall center ((1 / 2 : ℝ) ^ length)) ≤
      ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ length) ^ (dimension : ℝ))) :
    LowerExponent set dimension := by
  refine ⟨constant⁻¹, inv_pos.mpr positive, Eventually.of_forall ?_⟩
  intro length centers cover
  have covered : set ⊆ ⋃ index : Fin centers.length,
      Metric.closedBall (centers.get index) ((1 / 2 : ℝ) ^ length) := by
    intro point member
    obtain ⟨center, center_mem, bound⟩ := cover point member
    obtain ⟨index, equality⟩ := List.mem_iff_get.mp center_mem
    exact Set.mem_iUnion.mpr ⟨index, by change dist point (centers.get index) ≤ _; rw [equality]; exact bound⟩
  have cost : (1 : ℝ≥0∞) ≤ (centers.length : ℝ≥0∞) *
      ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ length) ^ (dimension : ℝ)) := by
    calc
      1 = measure set := mass_one.symm
      _ ≤ measure (⋃ index : Fin centers.length, Metric.closedBall (centers.get index) ((1 / 2 : ℝ) ^ length)) :=
        measure_mono covered
      _ ≤ ∑ index : Fin centers.length, measure (Metric.closedBall (centers.get index) ((1 / 2 : ℝ) ^ length)) :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _index : Fin centers.length, ENNReal.ofReal (constant * ((1 / 2 : ℝ) ^ length) ^ (dimension : ℝ)) :=
        Finset.sum_le_sum fun index _ => balls length (centers.get index)
      _ = _ := by simp
  have real_cost : (1 : ℝ) ≤ (centers.length : ℝ) *
      (constant * ((1 / 2 : ℝ) ^ length) ^ (dimension : ℝ)) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤
      (centers.length : ℝ) * (constant * ((1 / 2 : ℝ) ^ length) ^ (dimension : ℝ)))).mp
    simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using cost
  have decay : ((1 / 2 : ℝ) ^ length) ^ (dimension : ℝ) =
      (((2 : ℝ) ^ (dimension : ℝ)) ^ length)⁻¹ := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm (length : ℝ),
      Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div, Real.inv_rpow (by norm_num), inv_pow]
  rw [decay, ← mul_assoc, ← div_eq_mul_inv] at real_cost
  have power_pos : 0 < ((2 : ℝ) ^ (dimension : ℝ)) ^ length := by positivity
  have count_bound := (le_div_iff₀ power_pos).mp real_cost
  have := (div_le_iff₀ positive).mpr (by simpa only [one_mul] using count_bound)
  simpa only [div_eq_mul_inv, mul_comm] using this

end MoireBoxBounds
