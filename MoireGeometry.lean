import MoireSection2
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An actual gasket, constructed from convergent address series

Unlike the earlier generic recursion lemma, self-similarity is proved here
from a concrete definition. No self-similarity axiom is assumed.
-/

namespace MoireGeometry

noncomputable section

/-- The three centred equilateral vertices, with counterclockwise ordering. -/
def vertex : Fin 3 → ℂ
  | 0 => 1
  | 1 => ⟨-1 / 2, Real.sqrt 3 / 2⟩
  | 2 => ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩

/-- The point encoded by an infinite sequence of corners. -/
def addressPoint (vertices : Fin 3 → ℂ) (address : ℕ → Fin 3) : ℂ :=
  ∑' level : ℕ, ((1 / 2 : ℝ) ^ (level + 1)) • vertices (address level)

/-- The concrete gasket consists of all infinite address sums. -/
def gasket : Set ℂ := Set.range (addressPoint vertex)

theorem address_summable (vertices : Fin 3 → ℂ) (address : ℕ → Fin 3) :
    Summable (fun level : ℕ =>
      ((1 / 2 : ℝ) ^ (level + 1)) • vertices (address level)) := by
  apply Summable.of_norm_bounded
    (((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2)).mul_right
        (∑ digit : Fin 3, ‖vertices digit‖))
  intro level
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have vertex_bound : ‖vertices (address level)‖ ≤ ∑ digit : Fin 3, ‖vertices digit‖ :=
    Finset.single_le_sum (fun digit _ => norm_nonneg (vertices digit)) (Finset.mem_univ _)
  calc
    _ ≤ ((1 / 2 : ℝ) ^ (level + 1)) * (∑ digit : Fin 3, ‖vertices digit‖) :=
      mul_le_mul_of_nonneg_left vertex_bound (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem addressPoint_split (vertices : Fin 3 → ℂ) (address : ℕ → Fin 3) :
    addressPoint vertices address = (1 / 2 : ℝ) •
      (addressPoint vertices (fun level => address (level + 1)) + vertices (address 0)) := by
  unfold addressPoint
  rw [(address_summable vertices address).tsum_eq_zero_add]
  simp only [zero_add, pow_one, smul_add]
  rw [add_comm]
  congr 1
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro level
  rw [smul_smul, pow_succ]
  congr 1
  ring

theorem addressPoint_prepend (vertices : Fin 3 → ℂ) (digit : Fin 3)
    (address : ℕ → Fin 3) :
    addressPoint vertices (Nat.rec digit (fun level _ => address level)) =
      (1 / 2 : ℝ) • (addressPoint vertices address + vertices digit) := by
  rw [addressPoint_split]
  rfl

theorem addressPoint_constant (vertices : Fin 3 → ℂ) (digit : Fin 3) :
    addressPoint vertices (fun _ => digit) = vertices digit := by
  have fixed_point := addressPoint_split vertices (fun _ => digit)
  change addressPoint vertices (fun _ => digit) =
    (1 / 2 : ℝ) • (addressPoint vertices (fun _ => digit) + vertices digit) at fixed_point
  calc
    addressPoint vertices (fun _ => digit) =
      (2 : ℝ) • addressPoint vertices (fun _ => digit) -
        addressPoint vertices (fun _ => digit) := by module
    _ = (2 : ℝ) • ((1 / 2 : ℝ) •
        (addressPoint vertices (fun _ => digit) + vertices digit)) -
        addressPoint vertices (fun _ => digit) := by rw [← fixed_point]
    _ = vertices digit := by module

theorem vertex_mem_gasket (digit : Fin 3) : vertex digit ∈ gasket :=
  ⟨fun _ => digit, addressPoint_constant vertex digit⟩

theorem real_half_smul (point : ℂ) :
    (1 / 2 : ℝ) • point = (1 / 2 : ℚ) • point := by
  simp [Complex.real_smul, Rat.smul_def]

/-- Self-similarity follows by removing or prepending an address symbol. -/
theorem gasket_selfSimilar :
    gasket = ⋃ digit, MoireSection2.cornerMap vertex digit '' gasket := by
  ext point
  constructor
  · rintro ⟨address, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨address 0, addressPoint vertex (fun level => address (level + 1)),
      ⟨fun level => address (level + 1), rfl⟩, ?_⟩
    rw [addressPoint_split vertex address]
    exact (real_half_smul _).symm
  · intro point_mem
    obtain ⟨digit, predecessor, ⟨address, rfl⟩, rfl⟩ := Set.mem_iUnion.mp point_mem
    refine ⟨Nat.rec digit (fun level _ => address level), ?_⟩
    rw [addressPoint_prepend]
    exact real_half_smul _

/-- Multiplication by `exp(iθ)`, considered as a rational linear map. -/
def rotation (angle : ℝ) : Module.End ℚ ℂ where
  toFun point := Complex.exp (angle * Complex.I) * point
  map_add' := by intros; ring
  map_smul' := by intros; simp

@[simp] theorem rotation_zero (point : ℂ) : rotation 0 point = point := by
  simp [rotation]

theorem rotation_isometry (angle : ℝ) : Isometry (rotation angle) := by
  apply Isometry.of_dist_eq
  intro firstPoint secondPoint
  change dist (Complex.exp (angle * Complex.I) * firstPoint)
    (Complex.exp (angle * Complex.I) * secondPoint) = dist firstPoint secondPoint
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Lemma 2.1 for the actual complex-plane gasket and actual rotations. -/
theorem gasket_intersection_recursion (angle : ℝ) (displacement : ℂ) :
    MoireSection2.shiftedIntersection gasket (rotation angle) displacement =
      ⋃ blueDigit, ⋃ redDigit,
        MoireSection2.cornerMap vertex blueDigit ''
          MoireSection2.shiftedIntersection gasket (rotation angle)
            ((2 : ℚ) • displacement + vertex blueDigit - rotation angle (vertex redDigit)) :=
  MoireSection2.shiftedIntersection_eq_iUnion vertex gasket (rotation angle)
    displacement gasket_selfSimilar

end
end MoireGeometry
