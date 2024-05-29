import Mathlib.Combinatorics.SimpleGraph.Metric

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {G}

lemma Reachable.of_dist_ne_zero {u v : V} (h : G.dist u v ≠ 0) : G.Reachable u v := by
  apply dist_eq_zero_iff_eq_or_not_reachable.not.mp at h
  push_neg at h
  exact h.2

lemma exists_walk_of_dist_ne_zero {u v : V} (h : G.dist u v ≠ 0) :
    ∃ p : G.Walk u v, p.length = G.dist u v :=
  (Reachable.of_dist_ne_zero h).exists_walk_of_dist

namespace Walk

/-- Distinct vertices are not reachable in the empty graph. -/
@[simp]
lemma reachable_bot {u v : V} : (⊥ : SimpleGraph V).Reachable u v ↔ u = v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply h.elim
    intro p
    match p with
    | .nil => rfl
  · rw [h]
