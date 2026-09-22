import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! # The convex endpoint criterion, with labelled digit sequences

The geometric filling theorem is not assumed silently: this result applies
to a convex window containing every negative displacement digit.
-/

namespace MoireEndpoint

set_option autoImplicit false

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def relativeDisplacement (initial : V) (digits : ℕ → V) : ℕ → V
  | 0 => initial
  | level + 1 => (2 : ℝ) • relativeDisplacement initial digits level + digits level

/-- One backward step is a convex average of the endpoint and a negative digit. -/
theorem predecessor_mem (window : Set V) (window_convex : Convex ℝ window)
    (displacement digit : V) (next_mem : (2 : ℝ) • displacement + digit ∈ window)
    (negative_digit_mem : -digit ∈ window) : displacement ∈ window := by
  have average_mem := window_convex next_mem negative_digit_mem
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have average_eq : (1 / 2 : ℝ) • ((2 : ℝ) • displacement + digit) +
      (1 / 2 : ℝ) • (-digit) = displacement := by module
  rwa [average_eq] at average_mem

/-- Endpoint membership implies every earlier membership; even the initial
membership follows, so it is not needed as an extra assumption. -/
theorem all_prefixes_mem_of_endpoint_mem
    (window : Set V) (window_convex : Convex ℝ window)
    (initial : V) (digits : ℕ → V) (length : ℕ)
    (negative_digits_mem : ∀ level < length, -digits level ∈ window)
    (endpoint_mem : relativeDisplacement initial digits length ∈ window) :
    ∀ level ≤ length, relativeDisplacement initial digits level ∈ window := by
  induction length with
  | zero =>
      intro level level_le
      have level_eq : level = 0 := Nat.eq_zero_of_le_zero level_le
      simpa [level_eq] using endpoint_mem
  | succ length inductionHypothesis =>
      have predecessor_in_window : relativeDisplacement initial digits length ∈ window :=
        predecessor_mem window window_convex _ _ endpoint_mem
          (negative_digits_mem length (Nat.lt_succ_self _))
      intro level level_le
      rcases Nat.eq_or_lt_of_le level_le with level_eq | level_lt
      · simpa [level_eq] using endpoint_mem
      · exact inductionHypothesis
          (fun index index_lt => negative_digits_mem index (Nat.lt_trans index_lt (Nat.lt_succ_self _)))
          predecessor_in_window level (Nat.le_of_lt_succ level_lt)

theorem legal_iff_endpoint_mem
    (window : Set V) (window_convex : Convex ℝ window)
    (initial : V) (digits : ℕ → V) (length : ℕ)
    (negative_digits_mem : ∀ level < length, -digits level ∈ window) :
    (∀ level ≤ length, relativeDisplacement initial digits level ∈ window) ↔
      relativeDisplacement initial digits length ∈ window := by
  exact ⟨fun legal => legal length le_rfl,
    all_prefixes_mem_of_endpoint_mem window window_convex initial digits length negative_digits_mem⟩

end MoireEndpoint
