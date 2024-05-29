import Mathlib.Combinatorics.SimpleGraph.Metric
import LeanHS1960.Distance.Reachable
import LeanHS1960.Distance.WalkLength

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {G}

/- The distance between vertices is equal to `1` if and only if these vertices are adjacent. -/
theorem dist_eq_one_iff_adj {u v : V} : G.dist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let ⟨w, hw⟩ := exists_walk_of_dist_ne_zero <| ne_zero_of_eq_one h
    exact w.adj_of_length_eq_one <| h ▸ hw
  · have : h.toWalk.length = 1 := Walk.length_cons _ _
    exact ge_antisymm (h.reachable.pos_dist_of_ne h.ne) (this ▸ dist_le _)

theorem dist_eq_two_iff {u v : V} :
    G.dist u v = 2 ↔ u ≠ v ∧ ¬ G.Adj u v ∧ Nonempty (G.commonNeighbors u v) := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ ?_⟩
  · have : G.dist u v ≠ 0 := by simp [h]
    rw [ne_eq, ← Reachable.dist_eq_zero_iff (Reachable.of_dist_ne_zero this), ← ne_eq]
    exact this
  · rw [← dist_eq_one_iff_adj, h]
    omega
  · have : G.dist u v ≠ 0 := by simp [h]
    obtain ⟨w, hw⟩ := exists_walk_of_dist_ne_zero this
    rw [h] at hw
    exact w.commonNeighbors_of_length_eq_two hw
  · obtain ⟨hn, ha, _, h⟩ := h
    rw [mem_commonNeighbors] at h
    let w : G.Walk u v := .cons h.1 (.cons h.2.symm .nil)
    apply LE.le.antisymm
    · have : w.length = 2 := by tauto
      rw [← this]
      apply dist_le
    · rw [ne_eq, ← Reachable.dist_eq_zero_iff (w.reachable)] at hn
      rw [← dist_eq_one_iff_adj] at ha
      simp [Nat.two_le_iff, hn, ha]

theorem two_lt_dist_iff {u v : V} :
    2 < G.dist u v ↔ u ≠ v ∧ ¬G.Adj u v ∧ IsEmpty (G.commonNeighbors u v) ∧ G.Reachable u v := by
  refine ⟨fun h ↦ ⟨?c, ?b, ?a, ?_⟩, fun h ↦ ?_⟩
  case a =>
    by_contra con
    have hn : u ≠ v := ?c
    have ha : ¬G.Adj u v := ?b
    have : G.dist u v ≠ 2 := by omega
    rw [ne_eq, dist_eq_two_iff] at this
    push_neg at this
    simp only [ne_eq, hn, not_false_eq_true, ha, forall_true_left] at this
    rw [not_isEmpty_iff] at con
    exact this con
  case b =>
    have : G.dist u v ≠ 1 := by omega
    rw [ne_eq, dist_eq_one_iff_adj.not] at this
    exact this
  case c =>
    have : G.dist u v ≠ 0 := by omega
    rw [ne_eq, ← Reachable.dist_eq_zero_iff (Reachable.of_dist_ne_zero this), ← ne_eq]
    exact this
  · have : G.dist u v ≠ 0 := by omega
    exact Reachable.of_dist_ne_zero this
  · obtain ⟨hn, ha, h, hr⟩ := h
    apply LE.le.lt_of_ne
    · rw [← dist_eq_one_iff_adj.not] at ha
      rw [ne_eq, ← Reachable.dist_eq_zero_iff hr] at hn
      simp [Nat.two_le_iff, hn, ha]
    · symm
      rw [ne_eq, dist_eq_two_iff.not]
      aesop

lemma dist_bot : ∀ u v, (⊥ : SimpleGraph V).dist u v = 0 :=
  fun u v => by by_cases h : u = v <;> simp [h]

/-- Supergraphs have smaller or equal distances to their subgraphs. -/
lemma dist_le_subgraph_dist {G' : SimpleGraph V} {u v : V} (h : G ≤ G') (hr : G.Reachable u v) :
    G'.dist u v ≤ G.dist u v := by
  obtain ⟨_, hw⟩ := Reachable.exists_walk_of_dist hr
  rw [← hw, ← Walk.length_map (Hom.mapSpanningSubgraphs h)]
  apply dist_le
