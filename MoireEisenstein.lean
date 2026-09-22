import MoireLatticeWords
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The actual complex Eisenstein lattice

This file removes the abstract coordinate-embedding hypothesis from the lattice
word and finite-live-carry theorems.  The explicit vertex is
`ω = -1/2 + (sqrt 3)/2 * I`, the lattice is the subring `ℤ[ω]`, and the
arithmetic field is the subfield `ℚ(ω)`, both defined by their universal closure
operations in `ℂ`.
-/

namespace MoireEisenstein

open MoireSection2 MoireLatticeWords

/-- The positive-imaginary primitive cube root of unity. -/
noncomputable def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

@[simp] theorem omega_re : omega.re = -1 / 2 := rfl
@[simp] theorem omega_im : omega.im = Real.sqrt 3 / 2 := rfl

theorem omega_im_pos : 0 < omega.im := by
  rw [omega_im]
  positivity

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  have sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [pow_two, omega, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · ring

theorem omega_cube : omega ^ 3 = 1 := by
  calc
    omega ^ 3 = omega * (omega ^ 2 + omega + 1) -
        (omega ^ 2 + omega + 1) + 1 := by ring
    _ = 1 := by rw [omega_sq_add_omega_add_one]; ring

theorem omega_ne_one : omega ≠ 1 := by
  intro omega_eq
  have imaginaryPart_pos := omega_im_pos
  simp [omega_eq] at imaginaryPart_pos

/-- The concrete coordinate vertex is exactly the exponential used in the paper. -/
theorem omega_eq_exp_two_pi_third :
    omega = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  have angle_eq : 2 * Real.pi / 3 = 2 * (Real.pi / 3) := by ring
  apply Complex.ext
  · rw [omega_re, Complex.exp_ofReal_mul_I_re, angle_eq,
      Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  · rw [omega_im, Complex.exp_ofReal_mul_I_im, angle_eq,
      Real.sin_two_mul, Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring

/-- Integer coordinates in the geometric basis `(1, ω)`. -/
noncomputable def complexCoordinates : LatticePoint →+ ℂ where
  toFun point := (point.1 : ℂ) + (point.2 : ℂ) * omega
  map_zero' := by simp
  map_add' firstPoint secondPoint := by
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring

@[simp] theorem complexCoordinates_vertex_zero :
    complexCoordinates (vertexPiThird 0) = 1 := by
  norm_num [complexCoordinates, vertexPiThird]

@[simp] theorem complexCoordinates_vertex_one :
    complexCoordinates (vertexPiThird 1) = omega := by
  norm_num [complexCoordinates, vertexPiThird]

@[simp] theorem complexCoordinates_vertex_two :
    complexCoordinates (vertexPiThird 2) = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  apply Complex.ext <;> norm_num [complexCoordinates, vertexPiThird, omega]

theorem complexCoordinates_injective : Function.Injective complexCoordinates := by
  intro firstPoint secondPoint coordinates_eq
  have imaginaryParts_eq := congrArg Complex.im coordinates_eq
  have realParts_eq := congrArg Complex.re coordinates_eq
  simp only [complexCoordinates, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    zero_mul, add_zero, zero_add] at imaginaryParts_eq
  have secondCoordinates_real_eq : (firstPoint.2 : ℝ) = (secondPoint.2 : ℝ) :=
    mul_right_cancel₀ (ne_of_gt omega_im_pos) imaginaryParts_eq
  have secondCoordinates_eq : firstPoint.2 = secondPoint.2 := by
    exact_mod_cast secondCoordinates_real_eq
  apply Prod.ext _ secondCoordinates_eq
  simp only [complexCoordinates, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im,
    zero_mul, sub_zero, secondCoordinates_eq] at realParts_eq
  exact_mod_cast (add_right_cancel realParts_eq)

/-- Multiplication has the usual Eisenstein coordinate formula. -/
theorem complexCoordinates_mul (firstPoint secondPoint : LatticePoint) :
    complexCoordinates firstPoint * complexCoordinates secondPoint =
      complexCoordinates
        (firstPoint.1 * secondPoint.1 - firstPoint.2 * secondPoint.2,
          firstPoint.1 * secondPoint.2 + firstPoint.2 * secondPoint.1 -
            firstPoint.2 * secondPoint.2) := by
  simp only [complexCoordinates, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Int.cast_sub, Int.cast_mul, Int.cast_add]
  linear_combination (firstPoint.2 : ℂ) * (secondPoint.2 : ℂ) * omega_sq_add_omega_add_one

/-- The Eisenstein integer subring `ℤ[ω]` inside `ℂ`. -/
noncomputable def eisensteinLattice : Subring ℂ := Subring.closure {omega}

theorem omega_mem_eisensteinLattice : omega ∈ eisensteinLattice :=
  Subring.subset_closure (Set.mem_singleton omega)

theorem complexCoordinates_mem_eisensteinLattice (point : LatticePoint) :
    complexCoordinates point ∈ eisensteinLattice := by
  exact eisensteinLattice.add_mem (intCast_mem eisensteinLattice point.1)
    (eisensteinLattice.mul_mem (intCast_mem eisensteinLattice point.2)
      omega_mem_eisensteinLattice)

/-- The subring definition is exactly the geometric lattice `ℤ + ℤω`. -/
theorem eisensteinLattice_eq_range :
    (eisensteinLattice : Set ℂ) = Set.range complexCoordinates := by
  ext point
  constructor
  · intro point_mem
    change point ∈ Subring.closure {omega} at point_mem
    refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ point_mem
    · intro generator generator_mem
      have generator_eq := Set.mem_singleton_iff.mp generator_mem
      subst generator
      exact ⟨(0, 1), by simp [complexCoordinates]⟩
    · exact ⟨0, map_zero complexCoordinates⟩
    · exact ⟨(1, 0), by simp [complexCoordinates]⟩
    · intro firstValue secondValue _ _ first_mem second_mem
      obtain ⟨firstPoint, first_eq⟩ := first_mem
      obtain ⟨secondPoint, second_eq⟩ := second_mem
      exact ⟨firstPoint + secondPoint, by rw [map_add, first_eq, second_eq]⟩
    · intro value _ value_mem
      obtain ⟨point, point_eq⟩ := value_mem
      exact ⟨-point, by rw [map_neg, point_eq]⟩
    · intro firstValue secondValue _ _ first_mem second_mem
      obtain ⟨firstPoint, first_eq⟩ := first_mem
      obtain ⟨secondPoint, second_eq⟩ := second_mem
      refine ⟨(firstPoint.1 * secondPoint.1 - firstPoint.2 * secondPoint.2,
        firstPoint.1 * secondPoint.2 + firstPoint.2 * secondPoint.1 -
          firstPoint.2 * secondPoint.2), ?_⟩
      rw [← complexCoordinates_mul, first_eq, second_eq]
  · rintro ⟨coordinates, rfl⟩
    exact complexCoordinates_mem_eisensteinLattice coordinates

/-- The concrete embedding required by the finite-carry argument. -/
noncomputable def latticeCoordinates : LatticePoint →+ eisensteinLattice where
  toFun point := ⟨complexCoordinates point, complexCoordinates_mem_eisensteinLattice point⟩
  map_zero' := Subtype.ext (map_zero complexCoordinates)
  map_add' firstPoint secondPoint := Subtype.ext (map_add complexCoordinates firstPoint secondPoint)

@[simp] theorem latticeCoordinates_coe (point : LatticePoint) :
    (latticeCoordinates point : ℂ) = complexCoordinates point := rfl

theorem latticeCoordinates_injective : Function.Injective latticeCoordinates := by
  intro firstPoint secondPoint coordinates_eq
  exact complexCoordinates_injective (congrArg Subtype.val coordinates_eq)

theorem latticeCoordinates_surjective : Function.Surjective latticeCoordinates := by
  intro latticePoint
  have in_range : (latticePoint : ℂ) ∈ Set.range complexCoordinates := by
    rw [← eisensteinLattice_eq_range]
    exact latticePoint.property
  obtain ⟨coordinates, coordinates_eq⟩ := in_range
  exact ⟨coordinates, Subtype.ext coordinates_eq⟩

/-- The smallest subfield of `ℂ` containing `ω`, namely `ℚ(ω)`. -/
noncomputable def eisensteinField : Subfield ℂ := Subfield.closure {omega}

theorem eisensteinLattice_le_eisensteinField :
    eisensteinLattice ≤ eisensteinField.toSubring := by
  apply Subring.closure_le.mpr
  intro point point_mem
  exact Subfield.subset_closure point_mem

theorem ratioClosure_subset_eisensteinField :
    ratioClosure eisensteinLattice ⊆ (eisensteinField : Set ℂ) := by
  rintro value ⟨numerator, denominator, _, value_eq⟩
  rw [value_eq]
  exact eisensteinField.div_mem
    (eisensteinLattice_le_eisensteinField numerator.property)
    (eisensteinLattice_le_eisensteinField denominator.property)

/-- The manuscript's quotient description and generated-subfield description
of `ℚ(ω)` agree, including the value zero. -/
theorem ratioClosure_eq_eisensteinField :
    ratioClosure eisensteinLattice = (eisensteinField : Set ℂ) := by
  apply Set.Subset.antisymm ratioClosure_subset_eisensteinField
  intro value value_mem
  obtain ⟨numerator, numerator_mem, denominator, denominator_mem, quotient_eq⟩ :=
    Subfield.mem_closure_iff.mp value_mem
  by_cases denominator_zero : denominator = 0
  · have value_zero : value = 0 := by simpa [denominator_zero] using quotient_eq.symm
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    · simpa using value_zero
  · exact ⟨⟨numerator, numerator_mem⟩, ⟨denominator, denominator_mem⟩,
      denominator_zero, quotient_eq.symm⟩

/-- Finitely many live complex carries imply membership in the actual
Eisenstein number field; no coordinate injectivity assumption remains. -/
theorem rotation_mem_eisensteinField_of_finite_live_carries
    (rotation : ℂ) (live : Set ℂ) (live_finite : live.Finite)
    (zero_live : (0 : ℂ) ∈ live)
    (successor_live : ∀ carry ∈ live, ∃ digits : Fin 3 × Fin 3,
      carryStep eisensteinLattice latticeCoordinates rotation carry digits ∈ live) :
    rotation ∈ eisensteinField := by
  apply ratioClosure_subset_eisensteinField
  exact rotation_mem_ratioClosure_of_finite_live_carries
    eisensteinLattice latticeCoordinates latticeCoordinates_injective
    rotation live live_finite zero_live successor_live

/-- The converse finite-type theorem in the actual complex Eisenstein model.
Its assumptions are self-similarity, a live initial intersection, and finiteness
of the live reachable displacements, exactly as in the manuscript. -/
theorem rotation_mem_eisensteinField_of_finite_liveReachable
    (rotation : ℂ) (gasket : Set ℂ)
    (selfSimilar : gasket = ⋃ digit,
      cornerMap (fieldVertex eisensteinLattice latticeCoordinates) digit '' gasket)
    (zero_live :
      (shiftedIntersection gasket (LinearMap.mulLeft ℚ rotation) 0).Nonempty)
    (live_finite :
      (liveReachable eisensteinLattice latticeCoordinates rotation gasket).Finite) :
    rotation ∈ eisensteinField := by
  apply ratioClosure_subset_eisensteinField
  exact rotation_mem_ratioClosure_of_finite_liveReachable
    eisensteinLattice latticeCoordinates latticeCoordinates_injective
    rotation gasket selfSimilar zero_live live_finite

end MoireEisenstein
