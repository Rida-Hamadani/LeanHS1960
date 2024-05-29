import Mathlib.Combinatorics.SimpleGraph.Connectivity

namespace SimpleGraph
namespace Walk

variable {V : Type u} (G : SimpleGraph V) {G}

theorem adj_of_length_eq_one {u v : V} :
    ∀ {p : G.Walk u v}, p.length = 1 → G.Adj u v
  | nil => by simp
  | cons h nil => fun _ => h
  | cons h _ => fun l => (eq_of_length_eq_zero <| add_left_eq_self.mp <| length_cons _ _ ▸ l) ▸ h

theorem commonNeighbors_of_length_eq_two {u v : V} :
    ∀ {p : G.Walk u v}, p.length = 2 → Nonempty (G.commonNeighbors u v)
  | nil => by simp
  | cons _ nil => by simp
  | cons _ (cons _ nil) => by rw [nonempty_subtype]; tauto
  | cons _ (cons _ (cons _ _)) => by simp
