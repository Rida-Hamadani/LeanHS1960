import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Girth

namespace SimpleGraph

variable {G : SimpleGraph α}

lemma is3Clique_girth_eq_three {s : Finset α} (h : G.IsNClique 3 s) : G.girth = 3 := by
  have : ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length = 3 := by
    apply is3Clique_iff_exists_cycle_length_three.mp
    use s
  have : ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ 4 > w.length := by aesop
  have ge_girth (n : ℕ∞) : ¬(n ≤ G.girth) ↔ ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ ¬(n ≤ w.length)
  := by
    simp only [le_girth, not_forall, not_le, exists_prop]
  push_neg at ge_girth
  have : girth G < 4 := by simp [ge_girth, this]
  symm
  rw [← LE.le.ge_iff_eq three_le_girth]
  rw [←  three_add_one_eq_four, ← ENat.succ_def] at this
  apply Order.le_of_lt_succ
  exact this
