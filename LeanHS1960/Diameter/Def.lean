import LeanHS1960.Distance.Values

/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Lattice

/-!
# Diameter of a simple graph

This file defines the diameter of a simple graph as the greatest distance between any two vertices
in the graph.

## Main definitions

- `SimpleGraph.diam` is the graph diameter.

- `SimpleGraph.ediam` is the graph extended diameter.

## Todo

- Prove that `ENat.toNat G.girth ≤ 2 * G.diam + 1` when the diameter is non-zero.

-/

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

/-- The diameter is the greatest distance between any two vertices, with the value `0` in case the
distances are not bounded above. -/
noncomputable def diam (G : SimpleGraph α) : ℕ :=
  sSup {d | ∃ u v, d = G.dist u v}

lemma diam_ne_zero_nonempty (h : ∃ G : SimpleGraph α, G.diam ≠ 0) : Nonempty α := by
  contrapose h
  unfold diam
  aesop

private lemma not_bddAbove_diam_eq_zero (h : ¬BddAbove {d | ∃ u v, d = G.dist u v}) :
    G.diam = 0 := by
  apply Set.infinite_of_not_bddAbove at h
  rw [diam, Set.Infinite.Nat.sSup_eq_zero h]

lemma diam_exists [Nonempty α] : ∃ u v, G.dist u v = G.diam := by
  let s := {d | ∃ u v, d = G.dist u v}
  let u := Classical.arbitrary α
  by_cases h : BddAbove s
  · have : s.Nonempty := ⟨0, u, u, dist_self.symm⟩
    obtain ⟨u, v, huv⟩ := Nat.sSup_mem this h
    use u, v, huv.symm
  · rw [not_bddAbove_diam_eq_zero h]
    use u, u, dist_self

lemma bddAbove_dist_le_diam (h : BddAbove {d | ∃ u v, d = G.dist u v}) :
    ∀ u v, G.dist u v ≤ G.diam := by
  rw [diam, Nat.sSup_def h]
  aesop

lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  unfold diam
  by_cases h : Nonempty α
  · have : {d | ∃ u v, d = (⊥ : SimpleGraph α).dist u v} = {0} := by
      ext d
      rw [Set.mem_setOf_eq, Set.mem_singleton_iff]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · obtain ⟨_, _, h⟩ := h
        rw [h, dist_bot]
      · let u := Classical.arbitrary α
        use u, u
        rw [dist_bot, h]
    rw [this, csSup_singleton]
  · convert_to sSup ∅ = 0
    · aesop
    · rw [csSup_empty, bot_eq_zero']

lemma diam_eq_zero :
    G.diam = 0 ↔ ¬BddAbove {d | ∃ u v, d = G.dist u v} ∨ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases h' : G = ⊥
    · apply Or.inr h'
    · apply Or.inl
      have : ∃ u v, G.Adj u v := by
        by_contra
        have : G = emptyGraph α := by
          unfold emptyGraph
          aesop
        rw [emptyGraph_eq_bot] at this
        exact h' this
      obtain ⟨u, v, huv⟩ := this
      rw [← dist_eq_one_iff_adj] at huv
      by_contra con
      apply bddAbove_dist_le_diam at con
      have := con u v
      rw [huv, h] at this
      omega
  · cases' h with h h
    · apply not_bddAbove_diam_eq_zero h
    · rw [h, diam_bot]

lemma diam_le (h : G.diam ≠ 0) : ∀ u v, G.dist u v ≤ G.diam := by
  intro u v
  apply le_csSup
  rw [ne_eq, diam_eq_zero] at h
  push_neg at h
  exact h.1
  aesop

lemma diam_le_subgraph_diam [Nonempty α] (hg: G.Connected) (hz : G.diam ≠ 0) (h : G ≤ G') :
    G'.diam ≤ G.diam := by
  obtain ⟨u, v, huv⟩ := G'.diam_exists
  rw [← huv]
  exact LE.le.trans (dist_le_subgraph_dist h (hg u v)) (G.diam_le hz u v)
