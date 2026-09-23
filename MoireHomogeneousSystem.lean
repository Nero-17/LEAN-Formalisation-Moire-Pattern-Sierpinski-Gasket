import MoireMeasureSimilarity
import MoireAlmostEverySeparation

/-! Genuine uniform half-scale systems and their cylinder translations.
These definitions provide the interface for cited self-similar-measure results. -/
namespace MoireHomogeneousSystem

open MeasureTheory Filter MoireGeometry MoireWordPacking MoireGraphCoding
open MoireProjectionSeparation MoireAlmostEverySeparation MoireMeasureSimilarity
open scoped ENNReal
noncomputable section

def cylinderCenter {α : Type*} (vertices : α → ℂ) {n : ℕ} (word : Fin n → α) : ℂ :=
  ∑ k : Fin n, ((1 / 2 : ℝ) ^ (k.val + 1)) • vertices (word k)

def UniformSelfSimilar {α : Type*} [Fintype α]
    (μ : Measure ℂ) (vertices : α → ℂ) : Prop :=
  μ = Measure.sum (fun digit => (Fintype.card α : ℝ≥0∞)⁻¹ •
    μ.map (fun point => (1 / 2 : ℝ) • (point + vertices digit)))

def ExponentialSeparation {α : Type*} (vertices : α → ℂ) : Prop :=
  ∃ rate : ℝ, 0 < rate ∧ rate < 1 ∧ ∃ᶠ n in atTop,
    ∀ first second : Fin n → α, first ≠ second →
      rate ^ n ≤ ‖cylinderCenter vertices first - cylinderCenter vertices second‖

theorem prefixMap_eq_sum (address : ℕ → Fin 3) (n : ℕ) :
    prefixMap address n 0 =
      ∑ k ∈ Finset.range n, ((1 / 2 : ℝ) ^ (k + 1)) • vertex (address k) := by
  induction n with
  | zero => simp [prefixMap]
  | succ n ih =>
    rw [prefixMap, MoirePrefixGeometry.prefixMap_affine, ih, Finset.sum_range_succ]
    simp only [MoireSection2.cornerMap, zero_add, ← real_half_smul, smul_smul, pow_succ]
    module

theorem cylinderCenter_vertex {n : ℕ} (word : Fin n → Fin 3) :
    cylinderCenter vertex word = wordCenter word := by
  let address : ℕ → Fin 3 := fun k => if h : k < n then word ⟨k, h⟩ else 0
  have restriction : (fun k : Fin n => address k) = word := by funext k; simp [address]
  rw [← restriction, MoireIntersectionCounting.center_prefix, prefixMap_eq_sum]
  exact Fin.sum_univ_eq_sum_range (fun k => ((1 / 2 : ℝ) ^ (k + 1)) • vertex (address k)) n

theorem cylinderCenter_linear {α : Type*} (linear : ℂ →L[ℝ] ℂ)
    (vertices : α → ℂ) {n : ℕ} (word : Fin n → α) :
    cylinderCenter (fun digit => linear (vertices digit)) word =
      linear (cylinderCenter vertices word) := by
  simp only [cylinderCenter, map_sum, map_smul]

def rotationMap (angle : ℝ) : ℂ →L[ℝ] ℂ where
  toFun := rotation angle
  map_add' := (rotation angle).map_add
  map_smul' := by intros; simp [rotation, Complex.real_smul]; ring
  cont := (rotation_isometry angle).continuous

theorem cylinderCenter_difference (angle : ℝ) {n : ℕ}
    (word : Fin n → Fin 3 × Fin 3) :
    cylinderCenter (fun digit : Fin 3 × Fin 3 =>
      vertex digit.1 - rotation angle (vertex digit.2)) word =
      differenceTranslation angle word := by
  unfold cylinderCenter differenceTranslation
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← cylinderCenter_vertex, ← cylinderCenter_vertex]
  congr 1
  exact (cylinderCenter_linear (rotationMap angle) vertex (fun k => (word k).2))

theorem difference_selfSimilar (angle : ℝ) :
    UniformSelfSimilar (MoireDifferenceMeasure.differenceMeasure angle)
      (fun digit : Fin 3 × Fin 3 => vertex digit.1 - rotation angle (vertex digit.2)) := by
  unfold UniformSelfSimilar
  conv_lhs => rw [MoireMeasureSimilarity.differenceMeasure_selfSimilar]
  rw [Measure.sum_sum]
  simp only [Fintype.card_prod, Fintype.card_fin]
  norm_num
  congr 1
  funext pair
  congr 2
  funext point
  congr 1
  ring
theorem difference_separation (angle : ℝ) (separated : DifferenceExponentiallySeparated angle) :
    ExponentialSeparation
      (fun digit : Fin 3 × Fin 3 => vertex digit.1 - rotation angle (vertex digit.2)) := by
  simpa only [ExponentialSeparation, DifferenceExponentiallySeparated, cylinderCenter_difference] using separated

end
end MoireHomogeneousSystem
