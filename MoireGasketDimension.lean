import MoireDifferenceLaw
import MoireIntersectionCounting
import MoireMassDistribution
import MoireHausdorffLower
import MoireHausdorffUpper

namespace MoireGasketDimension

open MoireGeometry MoireSection2 MoireWordPacking MoireDifferenceMeasure MoireDifferenceLaw
open MoireIntersectionCounting MeasureTheory
open scoped ENNReal Matrix.Norms.Operator

theorem uniform_ball_mass (length : ℕ) (center : ℂ) :
    gasketMeasure (Metric.closedBall center ((1 / 2 : ℝ) ^ length)) ≤
      289 * (3 : ℝ≥0∞)⁻¹ ^ length := by
  classical
  let nearby : Finset (Fin length → Fin 3) := Finset.univ.filter
    (fun word => dist (wordCenter word) center ≤ 2 * (1 / 2 : ℝ) ^ length)
  have cardinality : nearby.card ≤ 289 := nearby_words_card_le length nearby center
    (fun _ member => (Finset.mem_filter.mp member).2)
  rw [gasketMeasure, Measure.map_apply (MoireDimension.continuous_addressPoint vertex).measurable
    measurableSet_closedBall]
  have covered : addressPoint vertex ⁻¹' Metric.closedBall center ((1 / 2 : ℝ) ^ length) ⊆
      ⋃ word ∈ nearby, {address | (fun k : Fin length => address k) = word} := by
    intro address inside
    refine Set.mem_iUnion.mpr ⟨(fun k : Fin length => address k), Set.mem_iUnion.mpr ⟨?_, rfl⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [center_prefix]
    have tail := MoirePrefixGeometry.addressPoint_center_dist address length
    have triangle := dist_triangle (MoireGraphCoding.prefixMap address length 0)
      (addressPoint vertex address) center
    rw [dist_comm] at tail
    change dist (addressPoint vertex address) center ≤ _ at inside
    linarith
  calc
    _ ≤ singleAddressMeasure (⋃ word ∈ nearby, {address | (fun k : Fin length => address k) = word}) :=
      measure_mono covered
    _ ≤ ∑ word ∈ nearby, singleAddressMeasure {address | (fun k : Fin length => address k) = word} :=
      measure_biUnion_finset_le _ _
    _ = (nearby.card : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ ^ length := by simp [single_prefix_probability]
    _ ≤ _ := mul_le_mul_right' (by exact_mod_cast cardinality) _

theorem uniform_ball_power (length : ℕ) (center : ℂ) :
    gasketMeasure (Metric.closedBall center ((1 / 2 : ℝ) ^ length)) ≤
      ENNReal.ofReal (289 * ((1 / 2 : ℝ) ^ length) ^ (Real.log 3 / Real.log 2)) := by
  have bound := uniform_ball_mass length center
  rw [MoireHausdorffLower.dyadic_spectral_power 3 (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num)]
  simpa only [ENNReal.ofReal_ofNat, ENNReal.inv_pow] using bound

theorem gasket_dimH_lower : ENNReal.ofReal (Real.log 3 / Real.log 2) ≤ dimH gasket := by
  exact MoireMassDistribution.le_dimH_of_dyadic_mass gasketMeasure (Real.log 3 / Real.log 2) 289
    (div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))) (by norm_num)
    uniform_ball_power gasket (by rw [gasketMeasure_gasket]; norm_num)

theorem one_state_radius :
    spectralRadius ℂ (A := Matrix Unit Unit ℂ)
      ((MoireGraphCovers.adjacency (fun (_ : Unit) (_ : Fin 3) (_ : Unit) => True)).map (Nat.cast : ℕ → ℂ)) = 3 := by
  have matrix_eq :
      (MoireGraphCovers.adjacency (fun (_ : Unit) (_ : Fin 3) (_ : Unit) => True)).map (Nat.cast : ℕ → ℂ) =
        algebraMap ℂ (Matrix Unit Unit ℂ) 3 := by
    ext first second
    have : first = second := Subsingleton.elim _ _
    subst second
    simp [MoireGraphCovers.adjacency, Matrix.algebraMap_eq_diagonal]
  rw [matrix_eq, spectralRadius, spectrum.scalar_eq]
  simp

theorem gasket_dimH_upper : dimH gasket ≤ ENNReal.ofReal (Real.log 3 / Real.log 2) := by
  have recursion : ∀ _source : Unit, gasket ⊆ ⋃ _target : Unit, ⋃ digit : Fin 3,
      ⋃ (_ : True), cornerMap vertex digit '' gasket := by
    intro source point member
    rw [gasket_selfSimilar] at member
    obtain ⟨digit, point_mem⟩ := Set.mem_iUnion.mp member
    exact Set.mem_iUnion.mpr ⟨(), Set.mem_iUnion.mpr ⟨digit, Set.mem_iUnion.mpr ⟨True.intro, point_mem⟩⟩⟩
  have upper := MoireHausdorffUpper.graph_dimH_le
    (fun (_ : Unit) (_ : Fin 3) (_ : Unit) => True) (fun _ => gasket)
    (fun _ _ member => MoireDimension.norm_le_one_of_mem_gasket member) recursion
    (by rw [one_state_radius]; norm_num) ()
  simpa only [one_state_radius, ENNReal.toReal_ofNat] using upper

theorem gasket_dimH : dimH gasket = ENNReal.ofReal (Real.log 3 / Real.log 2) :=
  le_antisymm gasket_dimH_upper gasket_dimH_lower

end MoireGasketDimension
