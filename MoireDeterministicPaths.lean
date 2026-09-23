import MoirePathCylinders

namespace MoireDeterministicPaths

open MeasureTheory Filter
open scoped ENNReal

variable {State : Type*}

def blueWord (path : ℕ → State × Fin 3) (length : ℕ) : Fin length → Fin 3 :=
  fun time => (path (time + 1)).2

/-- The initial vertex and blue labels determine every subsequent vertex. -/
theorem paths_agree (edge : State → Fin 3 → State → Prop)
    (deterministic : ∀ source digit first second, edge source digit first →
      edge source digit second → first = second)
    (first second : ℕ → State × Fin 3) (initial : first 0 = second 0)
    (first_edges : ∀ time, edge (first time).1 (first (time + 1)).2 (first (time + 1)).1)
    (second_edges : ∀ time, edge (second time).1 (second (time + 1)).2 (second (time + 1)).1)
    (length : ℕ) (labels : blueWord first length = blueWord second length) :
    first ∈ MoirePathCylinders.cylinder second length := by
  intro time bound
  induction time with
  | zero => exact initial
  | succ time ih =>
      have previous := ih (Nat.le_trans (Nat.le_succ _) bound)
      have label_eq := congrFun labels ⟨time, Nat.lt_of_succ_le bound⟩
      change (first (time + 1)).2 = (second (time + 1)).2 at label_eq
      apply Prod.ext
      · apply deterministic (first time).1 (first (time + 1)).2 _ _ (first_edges time)
        simpa only [previous, label_eq] using second_edges time
      · exact label_eq

variable [Fintype State] [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A labelled prefix has at most the mass of one state-path cylinder. This is
where determinization, rather than counting red/blue digit pairs, is essential. -/
theorem blueWord_mass_le (measure : Measure (ℕ → State × Fin 3))
    (edge : State → Fin 3 → State → Prop)
    (deterministic : ∀ source digit first second, edge source digit first →
      edge source digit second → first = second)
    (good : Set (ℕ → State × Fin 3)) (full : ∀ᵐ path ∂measure, path ∈ good)
    (initial : State × Fin 3) (starts : ∀ path ∈ good, path 0 = initial)
    (edges : ∀ path ∈ good, ∀ time, edge (path time).1 (path (time + 1)).2 (path (time + 1)).1)
    (length : ℕ) (bound : ℝ≥0∞)
    (cylinders : ∀ path ∈ good, measure (MoirePathCylinders.cylinder path length) ≤ bound)
    (word : Fin length → Fin 3) :
    measure {path | blueWord path length = word} ≤ bound := by
  classical
  by_cases realized : ∃ path ∈ good, blueWord path length = word
  · obtain ⟨representative, member, representative_word⟩ := realized
    apply (measure_mono_ae (full.mono fun path path_good => ?_)).trans (cylinders representative member)
    intro path_word
    exact paths_agree edge deterministic path representative
      ((starts path path_good).trans (starts representative member).symm)
      (edges path path_good) (edges representative member) length
      (path_word.trans representative_word.symm)
  · have zero : measure {path | blueWord path length = word} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      exact full.mono fun path path_good path_word => realized ⟨path, path_good, path_word⟩
    rw [zero]
    exact bot_le

end MoireDeterministicPaths
