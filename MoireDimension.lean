import MoireGeometry
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Analytic prerequisites for the graph-directed dimension theorem

These results concern the actual gasket defined by address sums and mathlib's
Hausdorff dimension. The graph-directed dimension formula is not assumed.
-/

namespace MoireDimension

open MoireGeometry MoireSection2 MeasureTheory
open scoped NNReal

noncomputable section

/-- Every vertex of the centred gasket lies on the unit circle. -/
theorem vertex_norm (digit : Fin 3) : ‖vertex digit‖ = 1 := by
  have sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have norm_sq : ‖vertex digit‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    fin_cases digit <;> simp [vertex, Complex.normSq_apply] <;> nlinarith
  have norm_nonnegative := norm_nonneg (vertex digit)
  nlinarith

/-- A uniform bound for every term of every gasket address series. -/
theorem address_term_norm (address : ℕ → Fin 3) (level : ℕ) :
    ‖((1 / 2 : ℝ) ^ (level + 1)) • vertex (address level)‖ =
      (1 / 2 : ℝ) ^ (level + 1) := by
  rw [norm_smul, vertex_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- Every point of the actual gasket lies in the closed unit disk. -/
theorem norm_le_one_of_mem_gasket {point : ℂ} (point_mem : point ∈ gasket) :
    ‖point‖ ≤ 1 := by
  obtain ⟨address, rfl⟩ := point_mem
  have term_summable : Summable (fun level : ℕ => (1 / 2 : ℝ) ^ (level + 1)) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp_injective Nat.succ_injective
  have norm_summable : Summable (fun level : ℕ =>
      ‖((1 / 2 : ℝ) ^ (level + 1)) • vertex (address level)‖) := by
    simpa only [address_term_norm] using term_summable
  calc
    ‖addressPoint vertex address‖ ≤
        ∑' level : ℕ, ‖((1 / 2 : ℝ) ^ (level + 1)) • vertex (address level)‖ :=
      norm_tsum_le_tsum_norm norm_summable
    _ = ∑' level : ℕ, (1 / 2 : ℝ) ^ (level + 1) := by
      simp only [address_term_norm]
    _ = 1 := by
      rw [show (fun level : ℕ => (1 / 2 : ℝ) ^ (level + 1)) =
        (fun level : ℕ => (1 / 2 : ℝ) ^ level * (1 / 2 : ℝ)) by
          funext level; exact pow_succ _ _, tsum_mul_right,
        tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
      norm_num

/-- The address map is continuous for the product topology on addresses. -/
theorem continuous_addressPoint (vertices : Fin 3 → ℂ) :
    Continuous (addressPoint vertices) := by
  unfold addressPoint
  refine continuous_tsum (fun level => ?_)
    (((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2)).mul_right
        (∑ digit : Fin 3, ‖vertices digit‖)) ?_
  · exact (continuous_const : Continuous
        (fun _ : ℕ → Fin 3 => (1 / 2 : ℝ) ^ (level + 1))).smul
      ((continuous_of_discreteTopology : Continuous vertices).comp
        (continuous_apply level : Continuous (fun address : ℕ → Fin 3 => address level)))
  intro level address
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have vertex_bound : ‖vertices (address level)‖ ≤ ∑ digit : Fin 3, ‖vertices digit‖ :=
    Finset.single_le_sum (fun digit _ => norm_nonneg (vertices digit)) (Finset.mem_univ _)
  calc
    _ ≤ ((1 / 2 : ℝ) ^ (level + 1)) * (∑ digit : Fin 3, ‖vertices digit‖) :=
      mul_le_mul_of_nonneg_left vertex_bound (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- The gasket is a compact set, as the continuous image of the compact address space. -/
theorem isCompact_gasket : IsCompact gasket :=
  isCompact_range (continuous_addressPoint vertex)

/-- The shifted intersection is an ordinary intersection with an affine image. -/
theorem shiftedIntersection_eq_inter_image (angle : ℝ) (displacement : ℂ) :
    shiftedIntersection gasket (rotation angle) displacement =
      gasket ∩ (fun point => rotation angle point - displacement) '' gasket := by
  ext point
  constructor
  · rintro ⟨point_mem, redPoint, redPoint_mem, point_eq⟩
    exact ⟨point_mem, redPoint, redPoint_mem, point_eq.symm⟩
  · rintro ⟨point_mem, redPoint, redPoint_mem, point_eq⟩
    exact ⟨point_mem, redPoint, redPoint_mem, point_eq.symm⟩

/-- Every relative-displacement intersection is compact. -/
theorem isCompact_shiftedIntersection (angle : ℝ) (displacement : ℂ) :
    IsCompact (shiftedIntersection gasket (rotation angle) displacement) := by
  rw [shiftedIntersection_eq_inter_image]
  exact isCompact_gasket.inter (isCompact_gasket.image
    ((rotation_isometry angle).continuous.sub continuous_const))

/-- The corner maps are similarities of ratio exactly one half. -/
theorem cornerMap_dist (vertices : Fin 3 → ℂ) (digit : Fin 3)
    (firstPoint secondPoint : ℂ) :
    dist (cornerMap vertices digit firstPoint) (cornerMap vertices digit secondPoint) =
      (1 / 2 : ℝ) * dist firstPoint secondPoint := by
  simp only [cornerMap, ← real_half_smul]
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  simp only [add_sub_add_right_eq_sub, dist_eq_norm]

/-- The Lipschitz constant of a corner map is one half. -/
theorem cornerMap_lipschitz (vertices : Fin 3 → ℂ) (digit : Fin 3) :
    LipschitzWith (1 / 2 : ℝ≥0) (cornerMap vertices digit) := by
  apply LipschitzWith.of_dist_le_mul
  intro firstPoint secondPoint
  simp only [cornerMap_dist, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, le_refl]

/-- A corner map has inverse distance expansion factor two. -/
theorem cornerMap_antilipschitz (vertices : Fin 3 → ℂ) (digit : Fin 3) :
    AntilipschitzWith 2 (cornerMap vertices digit) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro firstPoint secondPoint
  rw [cornerMap_dist]
  norm_num
  linarith

/-- Corner similarities preserve the actual Hausdorff dimension. -/
theorem dimH_cornerMap_image (vertices : Fin 3 → ℂ) (digit : Fin 3) (set : Set ℂ) :
    dimH (cornerMap vertices digit '' set) = dimH set :=
  le_antisymm ((cornerMap_lipschitz vertices digit).dimH_image_le set)
    ((cornerMap_antilipschitz vertices digit).le_dimH_image set)

/-- The concrete carry recursion also gives an exact identity for Hausdorff dimensions. -/
theorem dimH_shiftedIntersection_recursion (angle : ℝ) (displacement : ℂ) :
    dimH (shiftedIntersection gasket (rotation angle) displacement) =
      ⨆ blueDigit : Fin 3, ⨆ redDigit : Fin 3,
        dimH (shiftedIntersection gasket (rotation angle)
          ((2 : ℚ) • displacement + vertex blueDigit - rotation angle (vertex redDigit))) := by
  rw [gasket_intersection_recursion, dimH_iUnion]
  simp only [dimH_iUnion, dimH_cornerMap_image]

end
end MoireDimension
