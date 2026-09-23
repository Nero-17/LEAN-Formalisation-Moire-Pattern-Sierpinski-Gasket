import MoireWordPacking
import MoireDeterministicPaths

namespace MoireSmallBalls

open MoireGeometry MoireLatticeWords MoireGraphCoding MoireWordPacking MoireDeterministicPaths
open MeasureTheory
open scoped ENNReal

theorem prefix_as_finite_word (address : ℕ → Fin 3) (length : ℕ) :
    List.ofFn (fun time : Fin length => address time) = addressPrefix address length := by
  simpa [addressPrefix] using List.ofFn_getElem_eq_map (List.range length) address

theorem wordCenter_blueWord {State : Type*} (path : ℕ → State × Fin 3) (length : ℕ) :
    wordCenter (blueWord path length) = prefixMap (fun time => (path (time + 1)).2) length 0 := by
  rw [MoirePrefixGeometry.prefixMap_center_coordinates]
  unfold wordCenter blueWord
  rw [prefix_as_finite_word (fun time => (path (time + 1)).2) length]

/-- A blue-cylinder probability bound gives a Euclidean small-ball bound with
a constant independent of depth, graph size, and the location of the ball. -/
theorem dyadic_ball_mass_le {State : Type*} [MeasurableSpace State]
    (measure : Measure (ℕ → State × Fin 3)) (length : ℕ) (bound : ℝ≥0∞)
    (word_mass : ∀ word : Fin length → Fin 3,
      measure {path | blueWord path length = word} ≤ bound) (center : ℂ) :
    measure {path | dist (addressPoint vertex (fun time => (path (time + 1)).2)) center ≤
      (1 / 2 : ℝ) ^ length} ≤ 289 * bound := by
  classical
  let nearby : Finset (Fin length → Fin 3) := Finset.univ.filter
    (fun word => dist (wordCenter word) center ≤ 2 * (1 / 2 : ℝ) ^ length)
  have cardinality : nearby.card ≤ 289 := nearby_words_card_le length nearby center
    (fun _ member => (Finset.mem_filter.mp member).2)
  have covered : {path : ℕ → State × Fin 3 | dist (addressPoint vertex (fun time => (path (time + 1)).2)) center ≤
      (1 / 2 : ℝ) ^ length} ⊆
      ⋃ word ∈ nearby, {path | blueWord path length = word} := by
    intro path member
    refine Set.mem_iUnion.mpr ⟨blueWord path length, Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [wordCenter_blueWord]
    have tail := MoirePrefixGeometry.addressPoint_center_dist (fun time => (path (time + 1)).2) length
    have triangle := dist_triangle (prefixMap (fun time => (path (time + 1)).2) length 0)
      (addressPoint vertex (fun time => (path (time + 1)).2)) center
    rw [dist_comm] at tail
    exact triangle.trans (by change dist _ center ≤ _ at member; linarith)
  calc
    _ ≤ measure (⋃ word ∈ nearby, {path | blueWord path length = word}) := measure_mono covered
    _ ≤ ∑ word ∈ nearby, measure {path | blueWord path length = word} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _word ∈ nearby, bound := Finset.sum_le_sum fun word _ => word_mass word
    _ = (nearby.card : ℝ≥0∞) * bound := by simp
    _ ≤ 289 * bound := mul_le_mul_right' (by exact_mod_cast cardinality) _

end MoireSmallBalls
