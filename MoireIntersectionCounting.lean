import MoireDifferenceMeasure
import MoireBoxDimension

namespace MoireIntersectionCounting

open MoireGeometry MoireSection2 MoireWordPacking MoireDifferenceMeasure
open MoireBoxDimension MeasureTheory
open scoped ENNReal

noncomputable section

/-- An actual gasket cylinder, retaining its symbolic pairPrefix at boundary points. -/
def cell {length : ℕ} (word : Fin length → Fin 3) : Set ℂ :=
  {point | ∃ address : ℕ → Fin 3,
    (∀ k : Fin length, address k = word k) ∧ addressPoint vertex address = point}

theorem center_prefix (address : ℕ → Fin 3) (length : ℕ) :
    wordCenter (fun k : Fin length => address k) =
      MoireGraphCoding.prefixMap address length 0 := by
  rw [MoirePrefixGeometry.prefixMap_center_coordinates]
  unfold wordCenter
  rw [MoireSmallBalls.prefix_as_finite_word]

theorem cell_dist_center {length : ℕ} (word : Fin length → Fin 3)
    {point : ℂ} (member : point ∈ cell word) :
    dist point (wordCenter word) ≤ (1 / 2 : ℝ) ^ length := by
  obtain ⟨address, prefix_eq, rfl⟩ := member
  have equality : (fun k : Fin length => address k) = word := funext prefix_eq
  rw [← equality, center_prefix]
  exact MoirePrefixGeometry.addressPoint_center_dist address length

theorem cell_dist {length : ℕ} (word : Fin length → Fin 3)
    {first second : ℂ} (first_mem : first ∈ cell word) (second_mem : second ∈ cell word) :
    dist first second ≤ 2 * (1 / 2 : ℝ) ^ length := by
  have first_bound := cell_dist_center word first_mem
  have second_bound := cell_dist_center word second_mem
  have triangle := dist_triangle first (wordCenter word) second
  rw [dist_comm (wordCenter word) second] at triangle
  linarith

def Intersects (angle : ℝ) {length : ℕ} (word : Fin length → Fin 3 × Fin 3) : Prop :=
  ∃ blue ∈ cell (fun k => (word k).1),
    ∃ red ∈ cell (fun k => (word k).2), blue = rotation angle red

def intersectingWords (angle : ℝ) (length : ℕ) : Finset (Fin length → Fin 3 × Fin 3) :=
  @Finset.filter _ (Intersects angle) (Classical.decPred _) Finset.univ

def intersectionCount (angle : ℝ) (length : ℕ) : ℕ :=
  (intersectingWords angle length).card

/-- Every address pair with an intersecting pairPrefix lies in a small difference ball. -/
theorem differencePoint_small (angle : ℝ) (length : ℕ) (address : ℕ → Fin 3 × Fin 3)
    (intersects : Intersects angle (pairPrefix length address)) :
    dist (differencePoint angle address) 0 ≤ 4 * (1 / 2 : ℝ) ^ length := by
  obtain ⟨blue, blue_mem, red, red_mem, common⟩ := intersects
  have blue_bound := cell_dist (fun k => (pairPrefix length address k).1)
    (show addressPoint vertex (fun k => (address k).1) ∈ cell _ from ⟨_, fun _ => rfl, rfl⟩) blue_mem
  have red_bound := cell_dist (fun k => (pairPrefix length address k).2)
    red_mem (show addressPoint vertex (fun k => (address k).2) ∈ cell _ from ⟨_, fun _ => rfl, rfl⟩)
  have triangle := dist_triangle (addressPoint vertex (fun k => (address k).1)) blue
    (rotation angle (addressPoint vertex (fun k => (address k).2)))
  rw [common, (rotation_isometry angle).dist_eq] at triangle
  rw [common] at blue_bound
  rw [differencePoint, dist_zero_right, ← dist_eq_norm]
  linarith

/-- The manuscript's pairPrefix probability inequality for the actual planar measure.
The radius 4·2⁻ⁿ follows from the previously proved unit circumdisk bound. -/
theorem count_le_small_ball (angle : ℝ) (length : ℕ) :
    (intersectionCount angle length : ℝ≥0∞) * (9 : ℝ≥0∞)⁻¹ ^ length ≤
      differenceMeasure angle (Metric.closedBall 0 (4 * (1 / 2 : ℝ) ^ length)) := by
  classical
  rw [intersectionCount, differenceMeasure, Measure.map_apply (differencePoint_measurable angle) measurableSet_closedBall,
    ← prefix_event_probability length (intersectingWords angle length)]
  apply measure_mono
  intro address member
  exact differencePoint_small angle length address ((Finset.mem_filter.mp member).2)

def intersectionCenters (angle : ℝ) (length : ℕ) : List ℂ :=
  (intersectingWords angle length).toList.map (fun word => wordCenter (fun k => (word k).1))

theorem intersectionCenters_length (angle : ℝ) (length : ℕ) :
    (intersectionCenters angle length).length = intersectionCount angle length := by
  simp [intersectionCenters, intersectionCount]

/-- A concrete cover of the actual intersection by at most Q_n dyadic balls. -/
theorem intersectionCenters_cover (angle : ℝ) (length : ℕ) :
    Covers (shiftedIntersection gasket (rotation angle) 0) length (intersectionCenters angle length) := by
  classical
  rintro point ⟨⟨blueAddress, rfl⟩, red, ⟨redAddress, rfl⟩, common⟩
  let word : Fin length → Fin 3 × Fin 3 := fun k => (blueAddress k, redAddress k)
  have word_mem : word ∈ intersectingWords angle length := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, addressPoint vertex blueAddress, ⟨blueAddress, fun _ => rfl, rfl⟩,
      addressPoint vertex redAddress, ⟨redAddress, fun _ => rfl, rfl⟩, ?_⟩
    simpa only [sub_zero] using common
  refine ⟨wordCenter (fun k => (word k).1), List.mem_map.mpr
    ⟨word, Finset.mem_toList.mpr word_mem, rfl⟩, ?_⟩
  exact cell_dist_center _ ⟨blueAddress, fun _ => rfl, rfl⟩

end
end MoireIntersectionCounting
