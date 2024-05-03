import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.BigOperators.Basic
import LeanHS1960.Diameter.Def

namespace SimpleGraph

variable [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj] {d : ℕ}

open BigOperators

def IsMoore (d : ℕ) : Prop :=
  G.IsRegularOfDegree d ∧ G.girth = 2 * G.diam + 1

theorem card_of_isMoore {d : ℕ} (h : G.IsMoore d) :
    Fintype.card α = 1 + d * ∑ i : Fin G.diam, (d-1) ^ i.1 := by
  sorry
