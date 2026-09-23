import MoireRigidTriangles
import MoireMeasureSupport

namespace MoirePolygonFilling
open MoireGeometry MoireTriangleBoundary MoireTriangleTopology MoireRigidTriangles
open Set

/-- Intersecting congruent triangles have a common boundary point. The proof uses
connectedness of the perimeter and the equal circumradius, with no area assumption. -/
theorem boundaries_meet (angle : ℝ) (shift : ℂ)
    (blue red : ℂ) (blue_mem : blue ∈ closedTriangle) (red_mem : red ∈ closedTriangle)
    (common : blue = rigid angle shift red) :
    ∃ blueBoundary ∈ triangleBoundary, ∃ redBoundary ∈ triangleBoundary,
      blueBoundary = rigid angle shift redBoundary := by
  obtain ⟨digit, outside⟩ := vertex_not_interior angle shift
  have path_continuous : Continuous (fun t : ℝ =>
      triangleLevel (rigid angle shift ((1 - t) • red + t • vertex digit))) :=
    continuous_triangleLevel.comp ((rigid_continuous angle shift).comp (by fun_prop))
  have interval : (0 : ℝ) ∈ Icc
      (triangleLevel (rigid angle shift ((1 - (1 : ℝ)) • red + (1 : ℝ) • vertex digit)))
      (triangleLevel (rigid angle shift ((1 - (0 : ℝ)) • red + (0 : ℝ) • vertex digit))) := by
    simp only [sub_self, zero_smul, one_smul, zero_add, sub_zero, zero_smul, add_zero]
    exact ⟨outside, common ▸ (mem_triangle_iff_level blue).mp blue_mem⟩
  obtain ⟨t, t_mem, level_zero⟩ :=
    intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) path_continuous.continuousOn interval
  have parent_mem : (1 - t) • red + t • vertex digit ∈ closedTriangle :=
    triangle_mix red_mem (vertex_boundary digit).1 t_mem.1 t_mem.2
  have boundary_mem : rigid angle shift ((1 - t) • red + t • vertex digit) ∈ triangleBoundary :=
    (mem_boundary_iff_level _).mpr level_zero
  by_contra no_common
  have nonzero : ∀ point ∈ triangleBoundary,
      triangleLevel (rigid (-angle) (-rotation (-angle) shift) point) ≠ 0 := by
    intro point member zero
    apply no_common
    exact ⟨point, member, rigid (-angle) (-rotation (-angle) shift) point,
      (mem_boundary_iff_level _).mpr zero, (rigid_inverse_right angle shift point).symm⟩
  have positive : 0 < triangleLevel
      (rigid (-angle) (-rotation (-angle) shift)
        (rigid angle shift ((1 - t) • red + t • vertex digit))) := by
    have nonnegative := (mem_triangle_iff_level _).mp parent_mem
    have not_zero := nonzero _ boundary_mem
    rw [rigid_inverse] at not_zero ⊢
    exact lt_of_le_of_ne nonnegative (Ne.symm not_zero)
  have all_positive : ∀ point ∈ triangleBoundary,
      0 < triangleLevel (rigid (-angle) (-rotation (-angle) shift) point) := by
    intro point member
    exact boundary_preconnected.lt_of_ne
      (continuous_triangleLevel.comp (rigid_continuous _ _)).continuousOn nonzero
      ⟨_, boundary_mem, positive⟩ member
  obtain ⟨opposite, not_positive⟩ := vertex_not_interior (-angle) (-rotation (-angle) shift)
  exact (not_lt_of_ge not_positive) (all_positive _ (vertex_boundary opposite))

/-- The manuscript's polygon-filling lemma for every angle and every displacement. -/
theorem gasket_difference_eq_triangle_difference (angle : ℝ) :
    {point | ∃ blue ∈ gasket, ∃ red ∈ gasket, point = blue - rotation angle red} =
      {point | ∃ blue ∈ closedTriangle, ∃ red ∈ closedTriangle,
        point = blue - rotation angle red} := by
  ext point
  constructor
  · rintro ⟨blue, blue_mem, red, red_mem, equality⟩
    exact ⟨blue, gasket_subset_triangle blue_mem, red, gasket_subset_triangle red_mem, equality⟩
  · rintro ⟨blue, blue_mem, red, red_mem, equality⟩
    obtain ⟨blueBoundary, blue_boundary, redBoundary, red_boundary, common⟩ :=
      boundaries_meet angle point blue red blue_mem red_mem (by rw [equality, rigid]; abel)
    refine ⟨blueBoundary, boundary_subset_gasket blue_boundary,
      redBoundary, boundary_subset_gasket red_boundary, ?_⟩
    rw [common, rigid]
    abel

theorem differenceMeasure_support_polygon (angle : ℝ) :
    (MoireDifferenceMeasure.differenceMeasure angle).support =
      {point | ∃ blue ∈ closedTriangle, ∃ red ∈ closedTriangle,
        point = blue - rotation angle red} := by
  rw [MoireMeasureSupport.differenceMeasure_support, gasket_difference_eq_triangle_difference]

theorem support_contains_zero (angle : ℝ) :
    (0 : ℂ) ∈ (MoireDifferenceMeasure.differenceMeasure angle).support := by
  rw [differenceMeasure_support_polygon]
  have zero_mem : (0 : ℂ) ∈ closedTriangle := by
    intro digit
    fin_cases digit <;> norm_num [MoireTriangle.barycentric]
  exact ⟨0, zero_mem, 0, zero_mem, by simp⟩

theorem support_convex (angle : ℝ) :
    Convex ℝ (MoireDifferenceMeasure.differenceMeasure angle).support := by
  rw [differenceMeasure_support_polygon]
  intro first first_mem second second_mem a b a_nonnegative b_nonnegative total
  obtain ⟨blueFirst, blueFirst_mem, redFirst, redFirst_mem, rfl⟩ := first_mem
  obtain ⟨blueSecond, blueSecond_mem, redSecond, redSecond_mem, rfl⟩ := second_mem
  have a_eq : a = 1 - b := by linarith
  have b_le : b ≤ 1 := by linarith
  refine ⟨(1 - b) • blueFirst + b • blueSecond,
    triangle_mix blueFirst_mem blueSecond_mem b_nonnegative b_le,
    (1 - b) • redFirst + b • redSecond,
    triangle_mix redFirst_mem redSecond_mem b_nonnegative b_le, ?_⟩
  rw [a_eq]
  simp only [rotation, LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul]
  ring

/-- Negating either side of the filled difference-set identity gives the companion identity. -/
theorem negative_gasket_difference_eq (angle : ℝ) :
    {point | ∃ blue ∈ gasket, ∃ red ∈ gasket, point = rotation angle red - blue} =
      {point | ∃ blue ∈ closedTriangle, ∃ red ∈ closedTriangle,
        point = rotation angle red - blue} := by
  have identity := gasket_difference_eq_triangle_difference angle
  ext point
  have membership := congrArg (fun set : Set ℂ => -point ∈ set) identity
  have negate : ∀ first second : ℂ, -point = first - second ↔ point = second - first := by
    intro first second
    constructor <;> intro equality <;> linear_combination -equality
  simpa only [mem_setOf_eq, negate] using (iff_of_eq membership)

end MoirePolygonFilling
