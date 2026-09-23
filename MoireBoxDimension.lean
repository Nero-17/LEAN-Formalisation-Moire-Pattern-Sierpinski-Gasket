import MoireHausdorffEquality

namespace MoireBoxDimension

open Filter Topology
open scoped ENNReal NNReal

/-- A finite cover by closed Euclidean balls at dyadic scale. -/
def Covers (set : Set ℂ) (length : ℕ) (centers : List ℂ) : Prop :=
  ∀ point ∈ set, ∃ center ∈ centers, dist point center ≤ (1 / 2 : ℝ) ^ length

/-- An upper covering exponent: eventually, covers have O(2^(n s)) balls. -/
def UpperExponent (set : Set ℂ) (dimension : ℝ≥0) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ length : ℕ in atTop,
    ∃ centers : List ℂ, Covers set length centers ∧
      (centers.length : ℝ) ≤ constant * ((2 : ℝ) ^ (dimension : ℝ)) ^ length

/-- A lower covering exponent: every sufficiently fine cover needs at least
a positive constant times 2^(n s) balls. -/
def LowerExponent (set : Set ℂ) (dimension : ℝ≥0) : Prop :=
  ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ length : ℕ in atTop,
    ∀ centers : List ℂ, Covers set length centers →
      constant * ((2 : ℝ) ^ (dimension : ℝ)) ^ length ≤ (centers.length : ℝ)

/-- Upper box dimension in its dyadic covering-growth definition. -/
noncomputable def upperBoxDimension (set : Set ℂ) : ℝ≥0∞ :=
  ⨅ dimension : ℝ≥0, ⨅ (_ : UpperExponent set dimension), (dimension : ℝ≥0∞)

/-- Lower box dimension in its dyadic covering-growth definition. -/
noncomputable def lowerBoxDimension (set : Set ℂ) : ℝ≥0∞ :=
  ⨆ dimension : ℝ≥0, ⨆ (_ : LowerExponent set dimension), (dimension : ℝ≥0∞)

theorem eventually_scaled_pow_lt (small large first second : ℝ)
    (small_nonneg : 0 ≤ small) (larger : small < large)
    (first_pos : 0 < first) (second_pos : 0 < second) :
    ∀ᶠ length : ℕ in atTop, first * small ^ length < second * large ^ length := by
  have large_pos : 0 < large := lt_of_le_of_lt small_nonneg larger
  have ratio_lt : small / large < 1 := (div_lt_one large_pos).mpr larger
  have converges : Tendsto (fun length : ℕ => first * (small / large) ^ length) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg small_nonneg large_pos.le) ratio_lt).const_mul first
  filter_upwards [converges.eventually (gt_mem_nhds second_pos)] with length bound
  rw [div_pow, ← mul_div_assoc] at bound
  exact (div_lt_iff₀ (pow_pos large_pos length)).mp bound

theorem lower_exponent_le_upper_exponent {set : Set ℂ} {lower upper : ℝ≥0}
    (low : LowerExponent set lower) (high : UpperExponent set upper) : lower ≤ upper := by
  obtain ⟨lower_constant, lower_pos, lower_bound⟩ := low
  obtain ⟨upper_constant, upper_pos, upper_bound⟩ := high
  by_contra! reversed
  have exponent_lt : (2 : ℝ) ^ (upper : ℝ) < (2 : ℝ) ^ (lower : ℝ) :=
    (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr reversed
  obtain ⟨length, low, ⟨centers, cover, high⟩, impossible⟩ :=
    (lower_bound.and (upper_bound.and (eventually_scaled_pow_lt _ _ _ _
      (Real.rpow_nonneg (by norm_num) _) exponent_lt upper_pos lower_pos))).exists
  exact (not_lt_of_ge ((low centers cover).trans high)) impossible

theorem lowerBoxDimension_le_upperBoxDimension (set : Set ℂ) :
    lowerBoxDimension set ≤ upperBoxDimension set := by
  unfold lowerBoxDimension upperBoxDimension
  refine iSup_le fun lower => iSup_le fun low => le_iInf fun upper => le_iInf fun high => ?_
  exact_mod_cast lower_exponent_le_upper_exponent low high

theorem lowerExponent_mono {small large : Set ℂ} (subset : small ⊆ large) (dimension : ℝ≥0)
    (lower : LowerExponent small dimension) : LowerExponent large dimension := by
  obtain ⟨constant, positive, bounds⟩ := lower
  refine ⟨constant, positive, bounds.mono fun length bound centers cover => ?_⟩
  exact bound centers (fun point member => cover point (subset member))

end MoireBoxDimension
