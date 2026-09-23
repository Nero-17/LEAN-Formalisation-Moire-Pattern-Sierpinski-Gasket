import MoireSection2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Auxiliary lemmas and conditional scalar deductions for the upper-bound section

The theorem of Corso and Shmerkin is represented by the proposition
`CorsoShmerkinInput`; every use of it is therefore visible in a theorem's
arguments. It is not installed as a global Lean axiom. This file checks generic
rescaling and counting identities, a Borel--Cantelli mechanism, and scalar
implications corresponding to the dimension argument. The actual gasket
measures, dyadic Lq dimensions and geometric covering deduction are now
supplied separately in `MoireDifferenceMeasure`, `MoireDifferenceLaw`,
`MoireLqDimension` and `MoireUpperFromLq`. The analytic full-dimension input
and separation estimates remain unfinished. In this older file, the theorem named
`ae_upper_box_dimension_le` is a conditional scalar statement, not a completed
formal proof of the manuscript's upper bound for gasket intersections.
-/

namespace MoireSection3

open Filter MeasureTheory
open scoped BigOperators ENNReal

section CylinderTranslations

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A level-`n` cylinder translation is `2⁻ⁿ` times its raw carry. -/
def cylinderTranslation (vertex : ι → V) (rotate : V →+ V)
    (digits : List (ι × ι)) : V :=
  (((2 : ℚ) ^ digits.length)⁻¹) •
    MoireSection2.carryClosed vertex rotate digits

/-- Multiplication by `2ⁿ` recovers the raw carry exactly. -/
theorem pow_two_smul_cylinderTranslation (vertex : ι → V) (rotate : V →+ V)
    (digits : List (ι × ι)) :
    ((2 : ℚ) ^ digits.length) • cylinderTranslation vertex rotate digits =
      MoireSection2.carryClosed vertex rotate digits := by
  simp [cylinderTranslation, smul_smul]

/-- For equal-length words, rescaling their translation difference gives the
difference of their raw carries. -/
theorem pow_two_smul_cylinderTranslation_sub (vertex : ι → V) (rotate : V →+ V)
    (firstDigits secondDigits : List (ι × ι))
    (length_eq : firstDigits.length = secondDigits.length) :
    ((2 : ℚ) ^ firstDigits.length) •
        (cylinderTranslation vertex rotate firstDigits -
          cylinderTranslation vertex rotate secondDigits) =
      MoireSection2.carryClosed vertex rotate firstDigits -
        MoireSection2.carryClosed vertex rotate secondDigits := by
  rw [smul_sub, pow_two_smul_cylinderTranslation]
  rw [length_eq, pow_two_smul_cylinderTranslation]

end CylinderTranslations

section FiniteScaleUnionBound

variable {Ω κ : Type*} [MeasurableSpace Ω]

/-- The finite union estimate used when all level-`n` bad pairs are collected. -/
theorem measure_badUnion_le_sum (measure : Measure Ω) (candidates : Finset κ)
    (bad : κ → Set Ω) :
    measure (⋃ candidate ∈ candidates, bad candidate) ≤
      ∑ candidate ∈ candidates, measure (bad candidate) := by
  exact measure_biUnion_finset_le candidates bad

/-- If each bad pair excludes a set of measure at most `bound`, the union costs
at most the number of candidate pairs times `bound`. -/
theorem measure_badUnion_le_card_nsmul (measure : Measure Ω)
    (candidates : Finset κ) (bad : κ → Set Ω) (bound : ℝ≥0∞)
    (each_bad_le : ∀ candidate ∈ candidates, measure (bad candidate) ≤ bound) :
    measure (⋃ candidate ∈ candidates, bad candidate) ≤
      candidates.card • bound := by
  calc
    measure (⋃ candidate ∈ candidates, bad candidate) ≤
        ∑ candidate ∈ candidates, measure (bad candidate) :=
      measure_badUnion_le_sum measure candidates bad
    _ ≤ ∑ _candidate ∈ candidates, bound := by
      exact Finset.sum_le_sum fun candidate candidate_mem =>
        each_bad_le candidate candidate_mem
    _ = candidates.card • bound := by simp

end FiniteScaleUnionBound

section BorelCantelli

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A summable upper bound for the bad-scale measures implies that almost every
angle belongs to only finitely many bad sets. -/
theorem ae_eventually_not_mem_of_summable_measure_bound
    (measure : Measure Ω) (bad : ℕ → Set Ω) (bound : ℕ → ℝ≥0∞)
    (bound_tsum_ne_top : (∑' level, bound level) ≠ ∞)
    (measure_bad_le : ∀ level, measure (bad level) ≤ bound level) :
    ∀ᵐ angle ∂measure, ∀ᶠ level in atTop, angle ∉ bad level := by
  apply MeasureTheory.ae_eventually_notMem
  exact ne_top_of_le_ne_top bound_tsum_ne_top
    (ENNReal.tsum_le_tsum measure_bad_le)

end BorelCantelli

section FinitePairBorelCantelli

variable {Ω κ : Type*} [MeasurableSpace Ω]

/-- The complete finite-pair/Borel--Cantelli mechanism used in both separation
lemmas.  Once the sum of “number of pairs times the bound for one pair” is
finite, almost every angle avoids every bad pair at all sufficiently large
scales. -/
theorem ae_eventually_avoids_finite_bad_pairs (measure : Measure Ω)
    (candidates : ℕ → Finset κ) (bad : ℕ → κ → Set Ω)
    (boundForOnePair : ℕ → ℝ≥0∞)
    (total_bound_tsum_ne_top :
      (∑' level, (candidates level).card • boundForOnePair level) ≠ ∞)
    (each_bad_le : ∀ level candidate, candidate ∈ candidates level →
      measure (bad level candidate) ≤ boundForOnePair level) :
    ∀ᵐ angle ∂measure, ∀ᶠ level in atTop,
      angle ∉ ⋃ candidate ∈ candidates level, bad level candidate := by
  apply ae_eventually_not_mem_of_summable_measure_bound measure
    (fun level => ⋃ candidate ∈ candidates level, bad level candidate)
    (fun level => (candidates level).card • boundForOnePair level)
    total_bound_tsum_ne_top
  intro level
  exact measure_badUnion_le_card_nsmul measure (candidates level)
    (bad level) (boundForOnePair level) (each_bad_le level)

end FinitePairBorelCantelli

section UniformCounting

variable {Ω : Type*} [Fintype Ω]

/-- Probability under the uniform distribution on a finite sample space. -/
def uniformProbability (event : Ω → Prop) [DecidablePred event] : ℚ :=
  ((Finset.univ.filter event).card : ℚ) / (Fintype.card Ω : ℚ)

/-- Exact conversion between an event count and its uniform probability. -/
theorem card_filter_eq_card_mul_uniformProbability [Nonempty Ω]
    (event : Ω → Prop) [DecidablePred event] :
    ((Finset.univ.filter event).card : ℚ) =
      (Fintype.card Ω : ℚ) * uniformProbability event := by
  rw [uniformProbability]
  field_simp

/-- There are exactly `9ⁿ` blue/red digit-pair words of length `n`. -/
theorem card_level_words (level : ℕ) :
    Fintype.card (Fin level → Fin 3 × Fin 3) = 9 ^ level := by
  simp

/-- The exact identity denoted `Q_n(θ) = 9^n P(C_n ∈ -K)` in the paper,
with the geometric event left as a predicate on level words. -/
theorem level_event_count_eq_nine_pow_mul_uniformProbability (level : ℕ)
    (event : (Fin level → Fin 3 × Fin 3) → Prop) [DecidablePred event] :
    ((Finset.univ.filter event).card : ℚ) =
      (9 : ℚ) ^ level * uniformProbability event := by
  calc
    ((Finset.univ.filter event).card : ℚ) =
        (Fintype.card (Fin level → Fin 3 × Fin 3) : ℚ) *
          uniformProbability event :=
      card_filter_eq_card_mul_uniformProbability event
    _ = (9 : ℚ) ^ level * uniformProbability event := by
      rw [card_level_words]
      norm_num

end UniformCounting

section FullDimensionContradiction

/-- The conclusion supplied by the Corso--Shmerkin theorem for one fixed
measure and one fixed value of `q`.  Exponential separation and
`q`-unsaturation remain explicit hypotheses.

This proposition is the sole paper-specific external input used below. -/
def CorsoShmerkinInput (exponentialSeparation unsaturatedOnLines : Prop)
    (dimension symbolicDimension : ℝ) : Prop :=
  exponentialSeparation → unsaturatedOnLines → dimension = symbolicDimension

/-- The supercritical contradiction, with the Corso--Shmerkin input displayed
as a named hypothesis. -/
theorem dimension_eq_ambient_of_corsoShmerkin
    (ambientDimension dimension symbolicDimension : ℝ)
    (exponentialSeparation unsaturatedOnLines : Prop)
    (dimension_le_ambient : dimension ≤ ambientDimension)
    (ambient_lt_symbolicDimension : ambientDimension < symbolicDimension)
    (subfull_is_unsaturated : dimension < ambientDimension → unsaturatedOnLines)
    (corsoShmerkin : CorsoShmerkinInput exponentialSeparation
      unsaturatedOnLines dimension symbolicDimension)
    (has_exponentialSeparation : exponentialSeparation) :
    dimension = ambientDimension := by
  rcases lt_or_eq_of_le dimension_le_ambient with
    dimension_lt_ambient | dimension_eq_ambient
  · have dimension_eq_symbolicDimension :=
      corsoShmerkin has_exponentialSeparation
        (subfull_is_unsaturated dimension_lt_ambient)
    linarith
  · exact dimension_eq_ambient

/-- The logical core of Proposition 3: if any sub-full dimension would trigger
a strictly supercritical value, the only possible planar dimension is two. -/
theorem dimension_eq_two_of_supercritical_contradiction
    (dimension symbolicDimension : ℝ)
    (dimension_le_two : dimension ≤ 2)
    (two_lt_symbolicDimension : 2 < symbolicDimension)
    (subfull_forces_symbolic : dimension < 2 → dimension = symbolicDimension) :
    dimension = 2 := by
  rcases lt_or_eq_of_le dimension_le_two with dimension_lt_two | dimension_eq_two
  · rw [subfull_forces_symbolic dimension_lt_two] at dimension_le_two
    linarith
  · exact dimension_eq_two

/-- If one factor in the projected convolution has full line dimension and
convolution does not decrease either factor's dimension, then the projected
difference measure has line dimension one. -/
theorem projected_difference_dimension_eq_one
    (firstFactorDimension secondFactorDimension
      projectedDifferenceDimension : ℝ)
    (one_factor_full : firstFactorDimension = 1 ∨ secondFactorDimension = 1)
    (firstFactorDimension_le :
      firstFactorDimension ≤ projectedDifferenceDimension)
    (secondFactorDimension_le :
      secondFactorDimension ≤ projectedDifferenceDimension)
    (projectedDifferenceDimension_le_one :
      projectedDifferenceDimension ≤ 1) :
    projectedDifferenceDimension = 1 := by
  rcases one_factor_full with firstFactorDimension_eq_one |
      secondFactorDimension_eq_one
  · linarith
  · linarith

/-- Lemma 3's line-projection conclusion in scalar form.  The directional
dichotomy chooses a factor to which the explicit Corso--Shmerkin input applies;
monotonicity under convolution then makes the projected difference measure
full-dimensional on the line. -/
theorem projected_difference_dimension_eq_one_of_corsoShmerkin
    (firstFactorDimension secondFactorDimension
      projectedDifferenceDimension symbolicDimension : ℝ)
    (firstExponentialSeparation secondExponentialSeparation
      firstUnsaturatedOnLines secondUnsaturatedOnLines : Prop)
    (firstFactorDimension_le_one : firstFactorDimension ≤ 1)
    (secondFactorDimension_le_one : secondFactorDimension ≤ 1)
    (one_lt_symbolicDimension : 1 < symbolicDimension)
    (first_subfull_is_unsaturated :
      firstFactorDimension < 1 → firstUnsaturatedOnLines)
    (second_subfull_is_unsaturated :
      secondFactorDimension < 1 → secondUnsaturatedOnLines)
    (firstCorsoShmerkin : CorsoShmerkinInput firstExponentialSeparation
      firstUnsaturatedOnLines firstFactorDimension symbolicDimension)
    (secondCorsoShmerkin : CorsoShmerkinInput secondExponentialSeparation
      secondUnsaturatedOnLines secondFactorDimension symbolicDimension)
    (directionalDichotomy :
      firstExponentialSeparation ∨ secondExponentialSeparation)
    (firstFactorDimension_le_projectedDifferenceDimension :
      firstFactorDimension ≤ projectedDifferenceDimension)
    (secondFactorDimension_le_projectedDifferenceDimension :
      secondFactorDimension ≤ projectedDifferenceDimension)
    (projectedDifferenceDimension_le_one :
      projectedDifferenceDimension ≤ 1) :
    projectedDifferenceDimension = 1 := by
  have one_factor_full :
      firstFactorDimension = 1 ∨ secondFactorDimension = 1 := by
    rcases directionalDichotomy with
      first_has_exponentialSeparation | second_has_exponentialSeparation
    · left
      exact dimension_eq_ambient_of_corsoShmerkin 1 firstFactorDimension
        symbolicDimension firstExponentialSeparation firstUnsaturatedOnLines
        firstFactorDimension_le_one one_lt_symbolicDimension
        first_subfull_is_unsaturated firstCorsoShmerkin
        first_has_exponentialSeparation
    · right
      exact dimension_eq_ambient_of_corsoShmerkin 1 secondFactorDimension
        symbolicDimension secondExponentialSeparation secondUnsaturatedOnLines
        secondFactorDimension_le_one one_lt_symbolicDimension
        second_subfull_is_unsaturated secondCorsoShmerkin
        second_has_exponentialSeparation
  exact projected_difference_dimension_eq_one firstFactorDimension
    secondFactorDimension projectedDifferenceDimension one_factor_full
    firstFactorDimension_le_projectedDifferenceDimension
    secondFactorDimension_le_projectedDifferenceDimension
    projectedDifferenceDimension_le_one

/-- Full one-dimensional projections imply `q`-unsaturation whenever the
planar dimension is strictly below two. -/
theorem unsaturated_on_lines_of_full_projection_dimensions
    {Direction : Type*} (planarDimension : ℝ)
    (projectionDimension : Direction → ℝ)
    (planarDimension_lt_two : planarDimension < 2)
    (projectionDimension_eq_one :
      ∀ direction, projectionDimension direction = 1) :
    ∀ direction, planarDimension < projectionDimension direction + 1 := by
  intro direction
  rw [projectionDimension_eq_one direction]
  norm_num at planarDimension_lt_two ⊢
  exact planarDimension_lt_two

/-- Proposition 3 in its scalar dimension form.  The only paper-specific
external hypothesis is `corsoShmerkin`; the preceding projection lemma is what
supplies unsaturation below the ambient dimension. -/
theorem planar_dimension_eq_two_of_corsoShmerkin
    {Direction : Type*} (planarDimension symbolicDimension : ℝ)
    (projectionDimension : Direction → ℝ)
    (exponentialSeparation : Prop)
    (planarDimension_le_two : planarDimension ≤ 2)
    (two_lt_symbolicDimension : 2 < symbolicDimension)
    (projectionDimension_eq_one :
      ∀ direction, projectionDimension direction = 1)
    (corsoShmerkin : CorsoShmerkinInput exponentialSeparation
      (∀ direction, planarDimension < projectionDimension direction + 1)
      planarDimension symbolicDimension)
    (has_exponentialSeparation : exponentialSeparation) :
    planarDimension = 2 := by
  apply dimension_eq_ambient_of_corsoShmerkin 2 planarDimension
    symbolicDimension exponentialSeparation
    (∀ direction, planarDimension < projectionDimension direction + 1)
    planarDimension_le_two two_lt_symbolicDimension
  · intro planarDimension_lt_two
    exact unsaturated_on_lines_of_full_projection_dimensions planarDimension
      projectionDimension planarDimension_lt_two projectionDimension_eq_one
  · exact corsoShmerkin
  · exact has_exponentialSeparation

/-- The two limiting operations in the final proof: if the box dimension is
bounded by the main exponent plus `2/q + ε` for every `q > 1` and every
`ε > 0`, then both error terms can be removed. -/
theorem upper_box_dimension_le_of_all_q
    (upperBoxDimension mainExponent : ℝ)
    (upper_bound : ∀ q : ℝ, 1 < q → ∀ ε : ℝ, 0 < ε →
      upperBoxDimension ≤ mainExponent + 2 / q + ε) :
    upperBoxDimension ≤ mainExponent := by
  apply le_of_forall_pos_le_add
  intro ε ε_pos
  have one_lt_q : 1 < 1 + 4 / ε := by
    have four_div_epsilon_pos : 0 < 4 / ε := div_pos (by norm_num) ε_pos
    linarith
  have two_div_q_lt_half_epsilon : 2 / (1 + 4 / ε) < ε / 2 := by
    rw [div_lt_iff₀ (by linarith : 0 < 1 + 4 / ε)]
    have four_div_epsilon_mul_epsilon : (4 / ε) * ε = 4 := by
      field_simp
    nlinarith
  have dimension_bound := upper_bound (1 + 4 / ε) one_lt_q
    (ε / 2) (by linarith)
  linarith

/-- The exponent `log(9/4)/log 2` equals the codimension expression
`2 log 3 / log 2 - 2`. -/
theorem transverse_exponent_identity :
    Real.log ((9 : ℝ) / 4) / Real.log 2 =
      2 * (Real.log 3 / Real.log 2) - 2 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have log_two_ne_zero : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

/-- The last displayed inequality in the upper-bound section, after identifying the
Hausdorff dimension of the gasket with `log 3 / log 2`. -/
theorem upper_box_dimension_le_expected_codimension
    (upperBoxDimension gasketHausdorffDimension : ℝ)
    (gasketHausdorffDimension_eq :
      gasketHausdorffDimension = Real.log 3 / Real.log 2)
    (upperBoxDimension_le :
      upperBoxDimension ≤ Real.log ((9 : ℝ) / 4) / Real.log 2) :
    upperBoxDimension ≤ 2 * gasketHausdorffDimension - 2 := by
  rw [gasketHausdorffDimension_eq]
  rw [← transverse_exponent_identity]
  exact upperBoxDimension_le

end FullDimensionContradiction

section AlmostEveryConclusion

variable {Angle : Type*} [MeasurableSpace Angle]

/-- The two angle-exception arguments may be intersected without creating a
new exceptional set of positive measure. -/
theorem ae_both_separation_properties (measure : Measure Angle)
    (exponentialSeparation projectionDichotomy : Angle → Prop)
    (ae_exponentialSeparation : ∀ᵐ angle ∂measure,
      exponentialSeparation angle)
    (ae_projectionDichotomy : ∀ᵐ angle ∂measure,
      projectionDichotomy angle) :
    ∀ᵐ angle ∂measure,
      exponentialSeparation angle ∧ projectionDichotomy angle := by
  filter_upwards [ae_exponentialSeparation, ae_projectionDichotomy]
    with angle angle_has_exponentialSeparation angle_has_projectionDichotomy
  exact ⟨angle_has_exponentialSeparation, angle_has_projectionDichotomy⟩

/-- Almost-everywhere version of the final `q → ∞`, `ε ↓ 0` deduction. -/
theorem ae_upper_box_dimension_le (measure : Measure Angle)
    (upperBoxDimension mainExponent : Angle → ℝ)
    (ae_upper_bound : ∀ᵐ angle ∂measure,
      ∀ q : ℝ, 1 < q → ∀ ε : ℝ, 0 < ε →
        upperBoxDimension angle ≤ mainExponent angle + 2 / q + ε) :
    ∀ᵐ angle ∂measure,
      upperBoxDimension angle ≤ mainExponent angle := by
  filter_upwards [ae_upper_bound] with angle angle_upper_bound
  exact upper_box_dimension_le_of_all_q
    (upperBoxDimension angle) (mainExponent angle) angle_upper_bound

end AlmostEveryConclusion

end MoireSection3
