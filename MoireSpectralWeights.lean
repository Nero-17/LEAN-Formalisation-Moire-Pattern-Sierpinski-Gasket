import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace MoireSpectralWeights

open scoped Matrix.Norms.Operator NNReal ENNReal

variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

/-- Taking absolute values of a maximal-modulus eigenvector supplies the
nonnegative weights needed for a path measure, without assuming Perron--Frobenius. -/
theorem exists_nonnegative_spectral_weights (adjacency : Matrix State State ℕ) :
    ∃ weights : State → ℝ,
      (∀ state, 0 ≤ weights state) ∧ weights ≠ 0 ∧
      ∀ state,
        (spectralRadius ℂ (A := Matrix State State ℂ) (adjacency.map (Nat.cast : ℕ → ℂ))).toReal *
          weights state ≤ ∑ target, (adjacency state target : ℝ) * weights target := by
  obtain ⟨eigenvalue, member, modulus⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (adjacency.map (Nat.cast : ℕ → ℂ))
  have eigen : Module.End.HasEigenvalue
      (Matrix.toLin' (adjacency.map (Nat.cast : ℕ → ℂ))) eigenvalue := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rwa [Matrix.spectrum_toLin']
  obtain ⟨vector, vector_equation, vector_nonzero⟩ := eigen.exists_hasEigenvector
  refine ⟨fun state => ‖vector state‖, fun state => norm_nonneg _, ?_, ?_⟩
  · intro zero
    apply vector_nonzero
    ext state
    exact norm_eq_zero.mp (congrFun zero state)
  · intro state
    have scalar_equation : eigenvalue * vector state =
        ∑ target, (adjacency state target : ℂ) * vector target := by
      exact (congrFun (Module.End.mem_eigenspace_iff.mp vector_equation) state).symm
    have modulus_real : ‖eigenvalue‖ =
        (spectralRadius ℂ (A := Matrix State State ℂ)
          (adjacency.map (Nat.cast : ℕ → ℂ))).toReal := by
      rw [← modulus]
      rfl
    rw [← modulus_real, ← norm_mul, scalar_equation]
    calc
      ‖∑ target, (adjacency state target : ℂ) * vector target‖ ≤
          ∑ target, ‖(adjacency state target : ℂ) * vector target‖ := norm_sum_le _ _
      _ = ∑ target, (adjacency state target : ℝ) * ‖vector target‖ := by
        simp only [norm_mul, Complex.norm_natCast]

/-- On the positive support, normalized outgoing weights form a probability row.
An individual labelled edge has weight `weights target / outgoingWeight source`;
the factor `adjacency source target` counts parallel labels. -/
theorem normalized_row_sum (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ state, growth * weights state ≤
      ∑ target, (adjacency state target : ℝ) * weights target)
    (source : State) (source_positive : 0 < weights source) :
    0 < ∑ target, (adjacency source target : ℝ) * weights target ∧
      (∑ target, (adjacency source target : ℝ) *
        (weights target / (∑ next, (adjacency source next : ℝ) * weights next))) = 1 ∧
      ∀ target, 0 ≤ weights target / (∑ next, (adjacency source next : ℝ) * weights next) ∧
        weights target / (∑ next, (adjacency source next : ℝ) * weights next) ≤
          weights target / (growth * weights source) := by
  have outgoing_pos : 0 < ∑ target, (adjacency source target : ℝ) * weights target :=
    lt_of_lt_of_le (mul_pos growth_pos source_positive) (subeigen source)
  refine ⟨outgoing_pos, ?_, ?_⟩
  · simp_rw [← mul_div_assoc, ← Finset.sum_div]
    exact div_self (ne_of_gt outgoing_pos)
  · intro target
    exact ⟨div_nonneg (weights_nonneg target) outgoing_pos.le,
      div_le_div_of_nonneg_left (weights_nonneg target)
        (mul_pos growth_pos source_positive) (subeigen source)⟩

/-- Cylinder probabilities telescope along any positive-weight state path.
The numerator has no adjacency multiplicity because one labelled edge is selected. -/
theorem path_probability_bound (adjacency : Matrix State State ℕ) (weights : State → ℝ)
    (weights_nonneg : ∀ state, 0 ≤ weights state) (growth : ℝ) (growth_pos : 0 < growth)
    (subeigen : ∀ state, growth * weights state ≤
      ∑ target, (adjacency state target : ℝ) * weights target)
    (path : ℕ → State) (path_positive : ∀ level, 0 < weights (path level)) (length : ℕ) :
    (∏ level ∈ Finset.range length,
      weights (path (level + 1)) /
        (∑ target, (adjacency (path level) target : ℝ) * weights target)) ≤
      weights (path length) / (growth ^ length * weights (path 0)) := by
  induction length with
  | zero => simp [ne_of_gt (path_positive 0)]
  | succ length inductionHypothesis =>
      rw [Finset.prod_range_succ]
      have row := (normalized_row_sum adjacency weights weights_nonneg growth growth_pos
        subeigen (path length) (path_positive length)).2.2 (path (length + 1))
      calc
        _ ≤ (weights (path length) / (growth ^ length * weights (path 0))) *
            (weights (path (length + 1)) /
              (∑ target, (adjacency (path length) target : ℝ) * weights target)) :=
          mul_le_mul_of_nonneg_right inductionHypothesis row.1
        _ ≤ (weights (path length) / (growth ^ length * weights (path 0))) *
            (weights (path (length + 1)) / (growth * weights (path length))) :=
          mul_le_mul_of_nonneg_left row.2
            (div_nonneg (weights_nonneg _) (mul_nonneg (pow_nonneg growth_pos.le _) (weights_nonneg _)))
        _ = _ := by
          rw [pow_succ]
          field_simp [ne_of_gt growth_pos, ne_of_gt (path_positive 0),
            ne_of_gt (path_positive length)]

end MoireSpectralWeights
