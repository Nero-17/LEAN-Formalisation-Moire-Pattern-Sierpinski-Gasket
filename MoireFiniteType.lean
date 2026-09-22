import MoireConcrete
import MoireDimension
import Mathlib.Topology.Instances.Int
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp

namespace MoireFiniteType

open MoireSection2 MoireLatticeWords MoireEisenstein MoireGeometry

noncomputable section

theorem coordinate_conjugate (point : LatticePoint) :
    star (complexCoordinates point) =
      complexCoordinates (point.1 - point.2, -point.2) := by
  apply Complex.ext <;>
    simp [complexCoordinates, omega, Complex.mul_re, Complex.mul_im] <;> ring

theorem coordinate_mul_conjugate (point : LatticePoint) :
    complexCoordinates point * complexCoordinates (point.1 - point.2, -point.2) =
      ((point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2 : ℤ) : ℂ) := by
  rw [complexCoordinates_mul]
  simp [complexCoordinates]
  push_cast
  ring

theorem coordinate_norm_positive (point : LatticePoint)
    (nonzero : complexCoordinates point ≠ 0) :
    0 < point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2 := by
  have point_nonzero : point ≠ 0 := by
    intro h
    apply nonzero
    simp [h]
  have positive : 0 < (point.1 : ℝ) ^ 2 - point.1 * point.2 + point.2 ^ 2 := by
    by_contra h
    have hx := sq_nonneg (point.1 : ℝ)
    have hy := sq_nonneg (point.2 : ℝ)
    have hxy := sq_nonneg ((point.1 : ℝ) - point.2)
    have hx0 : (point.1 : ℝ) = 0 := by nlinarith
    have hy0 : (point.2 : ℝ) = 0 := by nlinarith
    apply point_nonzero
    apply Prod.ext
    · change point.1 = 0
      exact_mod_cast hx0
    · change point.2 = 0
      exact_mod_cast hy0
  exact_mod_cast positive

/-- Clearing denominators in the actual generated Eisenstein field. -/
theorem exists_positive_integer_multiplier (value : ℂ)
    (member : value ∈ eisensteinField) :
    ∃ q : ℤ, 0 < q ∧ (q : ℂ) * value ∈ eisensteinLattice := by
  have ratio_member : value ∈ ratioClosure eisensteinLattice := by
    rw [ratioClosure_eq_eisensteinField]
    exact member
  obtain ⟨numerator, denominator, denominator_ne, value_eq⟩ := ratio_member
  obtain ⟨point, point_eq⟩ := latticeCoordinates_surjective denominator
  have denominator_eq : complexCoordinates point = (denominator : ℂ) :=
    congrArg Subtype.val point_eq
  refine ⟨point.1 ^ 2 - point.1 * point.2 + point.2 ^ 2,
    coordinate_norm_positive point (by simpa [denominator_eq] using denominator_ne), ?_⟩
  have product_eq := coordinate_mul_conjugate point
  rw [denominator_eq] at product_eq
  rw [value_eq, ← product_eq]
  have cancel : (denominator : ℂ) *
      complexCoordinates (point.1 - point.2, -point.2) *
      ((numerator : ℂ) / denominator) =
      (numerator : ℂ) * complexCoordinates (point.1 - point.2, -point.2) := by
    field_simp
  rw [cancel]
  exact eisensteinLattice.mul_mem numerator.property
    (complexCoordinates_mem_eisensteinLattice _)

/-- Conditions (1) and (4) of Proposition 2.6, for any complex multiplier. -/
theorem field_iff_lattice_multiplier (value : ℂ) :
    value ∈ eisensteinField ↔
      ∃ q : ℤ, 0 < q ∧ ∀ point ∈ eisensteinLattice,
        (q : ℂ) * (value * point) ∈ eisensteinLattice := by
  constructor
  · intro member
    obtain ⟨q, positive, multiple_mem⟩ := exists_positive_integer_multiplier value member
    refine ⟨q, positive, fun point point_mem => ?_⟩
    rw [← mul_assoc]
    exact eisensteinLattice.mul_mem multiple_mem point_mem
  · rintro ⟨q, positive, inclusion⟩
    have product_mem := inclusion 1 eisensteinLattice.one_mem
    simp only [mul_one] at product_mem
    have q_ne : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
    have field_product := eisensteinLattice_le_eisensteinField product_mem
    have quotient := eisensteinField.div_mem field_product
      (eisensteinLattice_le_eisensteinField (intCast_mem eisensteinLattice q))
    simpa [mul_div_cancel_left₀ _ q_ne] using quotient

theorem integer_coordinates_bounded (point : LatticePoint) (radius : ℝ)
    (bound : ‖complexCoordinates point‖ ≤ radius) :
    |(point.1 : ℝ)| ≤ 2 * radius ∧ |(point.2 : ℝ)| ≤ 2 * radius := by
  have radius_nonneg : 0 ≤ radius := (norm_nonneg _).trans bound
  have sqrt_ge : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have imaginary_bound := (Complex.abs_im_le_norm (complexCoordinates point)).trans bound
  have imaginary_eq : |(complexCoordinates point).im| =
      |(point.2 : ℝ)| * Real.sqrt 3 / 2 := by
    simp [complexCoordinates, omega, abs_mul, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg (3 : ℝ))]
    ring
  rw [imaginary_eq] at imaginary_bound
  have second_bound : |(point.2 : ℝ)| ≤ 2 * radius := by
    nlinarith [mul_le_mul_of_nonneg_left sqrt_ge (abs_nonneg (point.2 : ℝ))]
  have real_bound := (Complex.abs_re_le_norm (complexCoordinates point)).trans bound
  have real_eq : (complexCoordinates point).re = (point.1 : ℝ) - point.2 / 2 := by
    simp [complexCoordinates, omega]
    ring
  rw [real_eq] at real_bound
  refine ⟨?_, second_bound⟩
  rw [abs_le] at real_bound second_bound ⊢
  constructor <;> linarith

/-- A bounded part of the actual complex Eisenstein lattice is finite. -/
theorem finite_lattice_ball (radius : ℝ) :
    {point : ℂ | point ∈ eisensteinLattice ∧ ‖point‖ ≤ radius}.Finite := by
  apply (((Set.finite_Icc (-⌈2 * radius⌉) ⌈2 * radius⌉).prod
    (Set.finite_Icc (-⌈2 * radius⌉) ⌈2 * radius⌉)).image complexCoordinates).subset
  rintro point ⟨point_mem, bound⟩
  have range_mem : point ∈ Set.range complexCoordinates := by
    rw [← eisensteinLattice_eq_range]
    exact point_mem
  obtain ⟨coordinates, rfl⟩ := range_mem
  refine ⟨coordinates, ?_, rfl⟩
  obtain ⟨first_bound, second_bound⟩ := integer_coordinates_bounded coordinates radius bound
  have ceil_bound : 2 * radius ≤ (⌈2 * radius⌉ : ℤ) := Int.le_ceil _
  have first_interval : -(⌈2 * radius⌉ : ℤ) ≤ coordinates.1 ∧
      coordinates.1 ≤ (⌈2 * radius⌉ : ℤ) := by
    rw [abs_le] at first_bound
    constructor
    · exact_mod_cast (by linarith : -((⌈2 * radius⌉ : ℤ) : ℝ) ≤ (coordinates.1 : ℝ))
    · exact_mod_cast (by linarith : (coordinates.1 : ℝ) ≤ ((⌈2 * radius⌉ : ℤ) : ℝ))
  have second_interval : -(⌈2 * radius⌉ : ℤ) ≤ coordinates.2 ∧
      coordinates.2 ≤ (⌈2 * radius⌉ : ℤ) := by
    rw [abs_le] at second_bound
    constructor
    · exact_mod_cast (by linarith : -((⌈2 * radius⌉ : ℤ) : ℝ) ≤ (coordinates.2 : ℝ))
    · exact_mod_cast (by linarith : (coordinates.2 : ℝ) ≤ ((⌈2 * radius⌉ : ℤ) : ℝ))
  exact ⟨first_interval, second_interval⟩

/-- Every reachable displacement has the same cleared denominator. -/
theorem reachable_multiple_mem (value : ℂ) (q : ℤ)
    (multiple_mem : (q : ℂ) * value ∈ eisensteinLattice)
    {displacement : ℂ}
    (reachable : ReachableCarry eisensteinLattice latticeCoordinates value displacement) :
    (q : ℂ) * displacement ∈ eisensteinLattice := by
  induction reachable with
  | initial => simp
  | @step displacement previous digits inductionHypothesis =>
      have step_eq : (q : ℂ) *
          carryStep eisensteinLattice latticeCoordinates value displacement digits =
          2 * ((q : ℂ) * displacement) +
          (q : ℂ) * (latticeCoordinates (vertexPiThird digits.1) : ℂ) -
          ((q : ℂ) * value) * (latticeCoordinates (vertexPiThird digits.2) : ℂ) := by
        simp only [carryStep]
        ring
      rw [step_eq]
      exact eisensteinLattice.sub_mem
        (eisensteinLattice.add_mem
          (eisensteinLattice.mul_mem (by norm_num) inductionHypothesis)
          (eisensteinLattice.mul_mem (intCast_mem eisensteinLattice q)
            (latticeCoordinates (vertexPiThird digits.1)).property))
        (eisensteinLattice.mul_mem multiple_mem
          (latticeCoordinates (vertexPiThird digits.2)).property)

theorem live_displacement_norm_bound (value displacement : ℂ)
    (live : (shiftedIntersection gasket (LinearMap.mulLeft ℚ value) displacement).Nonempty) :
    ‖displacement‖ ≤ ‖value‖ + 1 := by
  obtain ⟨bluePoint, blue_mem, redPoint, red_mem, point_eq⟩ := live
  have displacement_eq : displacement = value * redPoint - bluePoint := by
    change bluePoint = value * redPoint - displacement at point_eq
    linear_combination point_eq
  rw [displacement_eq]
  calc
    ‖value * redPoint - bluePoint‖ ≤ ‖value * redPoint‖ + ‖bluePoint‖ := norm_sub_le _ _
    _ = ‖value‖ * ‖redPoint‖ + ‖bluePoint‖ := by rw [norm_mul]
    _ ≤ ‖value‖ * 1 + 1 := add_le_add
      (mul_le_mul_of_nonneg_left (MoireDimension.norm_le_one_of_mem_gasket red_mem)
        (norm_nonneg _))
      (MoireDimension.norm_le_one_of_mem_gasket blue_mem)
    _ = ‖value‖ + 1 := by ring

/-- The forward finite-type implication for the actual gasket. No finite
state, boundedness, or denominator hypothesis is supplied by the caller. -/
theorem field_implies_finite_liveReachable (value : ℂ)
    (member : value ∈ eisensteinField) :
    (liveReachable eisensteinLattice latticeCoordinates value gasket).Finite := by
  obtain ⟨q, positive, multiple_mem⟩ := exists_positive_integer_multiplier value member
  have q_ne : (q : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  have finite_preimage :
      ((fun point : ℂ => (q : ℂ) * point) ⁻¹'
        {point : ℂ | point ∈ eisensteinLattice ∧
          ‖point‖ ≤ ‖(q : ℂ)‖ * (‖value‖ + 1)}).Finite :=
    (finite_lattice_ball _).preimage
      (fun first _ second _ equal => mul_left_cancel₀ q_ne equal)
  apply finite_preimage.subset
  rintro displacement ⟨reachable, live⟩
  refine ⟨reachable_multiple_mem value q multiple_mem reachable, ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (live_displacement_norm_bound value displacement live)
    (norm_nonneg _)

theorem resonant_implies_finite_type (angle : ℝ)
    (resonant : Complex.exp (angle * Complex.I) ∈ eisensteinField) :
    (liveReachable eisensteinLattice latticeCoordinates
      (Complex.exp (angle * Complex.I)) gasket).Finite :=
  field_implies_finite_liveReachable _ resonant

theorem finite_type_iff_resonant_of_nonempty (angle : ℝ)
    (initial_live : (shiftedIntersection gasket (rotation angle) 0).Nonempty) :
    (liveReachable eisensteinLattice latticeCoordinates
      (Complex.exp (angle * Complex.I)) gasket).Finite ↔
      Complex.exp (angle * Complex.I) ∈ eisensteinField :=
  ⟨MoireConcrete.finite_type_implies_commensurable angle initial_live,
    resonant_implies_finite_type angle⟩

end
end MoireFiniteType
