import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic
import LeanHS1960.Moore.Def
import LeanHS1960.Girth.Is3Clique

namespace SimpleGraph

variable [Fintype α] [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj] {d : ℕ}

variable (hm : G.IsMoore d) (hg : G.girth = 5)

lemma diam_eq_two : G.diam = 2 := by
  have : G.girth = 2 * G.diam + 1 := hm.2
  rw [hg] at this
  norm_cast at this
  omega

lemma nonempty_vertices : Nonempty α := by
  apply diam_ne_zero_nonempty
  use G
  rw [diam_eq_two hm hg]
  exact two_ne_zero

lemma size_eq_degree_sqr_plus_one : Fintype.card α = d^2 + 1 := by
  rw [card_of_isMoore hm, diam_eq_two hm hg]
  simp only [Fin.sum_univ_two, Fin.isValue, Fin.val_zero, pow_zero, Fin.val_one, pow_one, mul_add]
  rw [mul_one, Nat.mul_sub_left_distrib , ← add_assoc]
  ring_nf
  sorry

lemma adj_no_neighbors {v w : α} (hvw : G.Adj v w) : G.commonNeighbors v w = ∅ := by
  by_contra hcon
  rw [← ne_eq, ← Set.nonempty_iff_ne_empty, Set.nonempty_def] at hcon
  obtain ⟨x, _, _⟩ := hcon
  have hwx : G.Adj w x := by rwa [← mem_neighborSet]
  have hvx : G.Adj v x := by rwa [← mem_neighborSet]
  let s : Finset α := {x, v, w}
  have hs : s = {x, v, w} := by constructor
  have h3 : G.IsNClique 3 s := by
    rw [is3Clique_iff]
    use x, v, w
    exact And.intro (Adj.symm hvx) (And.intro (Adj.symm hwx) (And.intro hvw hs))
  apply is3Clique_girth_eq_three at h3
  rw [hg] at h3
  contradiction

variable (hc : G.Connected)

open Walk Matrix

lemma not_adj_one_neighbor {v w : α} (hneq : v ≠ w) (hvw : ¬G.Adj v w) :
    Fintype.card (G.commonNeighbors v w) = 1 := by
  have := nonempty_vertices hm hg
  apply LE.le.antisymm'
  · rw [Nat.one_le_iff_ne_zero, ← pos_iff_ne_zero, Fintype.card_pos_iff]
    have : G.dist v w ≤ 2 := by
        rw [← diam_eq_two hm hg]
        apply diam_le
        rw [diam_eq_two hm hg]
        exact two_ne_zero
    contrapose! this
    rw [Set.nonempty_iff_ne_empty'.not, ne_eq, not_not] at this
    simp [two_lt_dist_iff, hc v w, *]
  · by_contra! con
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩ , hab⟩ := Fintype.exists_pair_of_one_lt_card con
    rw [mem_commonNeighbors] at ha hb
    let p : G.Walk v v := .cons ha.1 (.cons ha.2.symm (.cons hb.2 (.cons hb.1.symm .nil)))
    have hp : p.IsCycle := by
      rw [isCycle_def]
      refine ⟨?_, ?_, ?_⟩
      · aesop
      · simp
      · constructor
        · intro x hx
          simp only [support_cons, support_nil, List.mem_cons, List.mem_singleton] at hx
          cases' hx with hx hx
          · rw [hx]
            apply Adj.ne' ha.2
          · cases' hx with hx hx
            · rw [hx]
              rw [ne_eq, Subtype.mk.injEq] at hab
              exact hab
            · cases' hx with hx hx
              · rw [hx]
                apply Adj.ne' ha.1
              · tauto
        · simp only [ne_eq, support_cons, support_nil, List.pairwise_cons, List.mem_cons,
          List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil, IsEmpty.forall_iff,
          forall_const, List.Pairwise.nil, and_self, and_true]
          exact And.intro (And.intro (Adj.ne hb.2) hneq.symm) (Adj.ne' hb.1)
    symm at hg
    apply Eq.le at hg
    rw [le_girth] at hg
    apply hg at hp
    simp only [Nat.ofNat_le_cast] at hp
    have : p.length = 4 := by constructor
    omega

lemma strongly_regular : G.IsSRGWith (d^2 + 1) d 0 1 where
  card := size_eq_degree_sqr_plus_one hm hg
  regular := hm.1
  of_adj := fun u v h => by simp [adj_no_neighbors hg h]
  of_not_adj := fun u v h h' => not_adj_one_neighbor hm hg hc h h'

theorem hoffman_singleton [RCLike β] : d ∈ ({2, 3, 7, 57} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  let A := G.adjMatrix β
  have : A ^ 2 = d • 1 + 0 • A + 1 • Gᶜ.adjMatrix β :=
    (strongly_regular hm hg hc).matrix_eq
  rw [nsmul_eq_mul, mul_one, zero_smul, add_zero, one_smul] at this
  have : A.compl = A ^ 2 - d • 1 := by
    unfold Matrix.compl
    aesop
  have : 1 + A + (A ^ 2 - d • 1) = Matrix.of fun _ _ ↦ 1 := by
    rw [← this, one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes]
  let f : α → β := fun _ ↦ 1
  have allOnesVector {v : α} : (A *ᵥ f) v = d := by
    simp only [adjMatrix_mulVec_apply, Finset.sum_const, card_neighborFinset_eq_degree,
      nsmul_eq_mul, mul_one, Nat.cast_inj, A, f]
    apply hm.1
  --you probably have to use: Matrix.IsHermitian.eigenvalues_eq
  have onesEigenspace : f ∈ Module.End.eigenspace (Matrix.toLin' A) d := by
    rw [Module.End.mem_eigenspace_iff]
    ext
    simp [allOnesVector, f]
  have {e : α → β} {l : β} (he : e ∈ Module.End.eigenspace (Matrix.toLin' A) l) (ho : f ⬝ᵥ e = 0)
      (hnz : e ≠ 0) : l ^ 2 + l - (d - 1) = 0 := by
    rw [Module.End.mem_eigenspace_iff, toLin'_apply', mulVecLin_apply] at he
    have hesqr : (A ^ 2) *ᵥ e = (l ^ 2) • e := by
      repeat rw [pow_succ, pow_one]
      rw [← mulVec_mulVec, he, mulVec_smul_assoc, he, ← smul_assoc, smul_eq_mul]
    apply_fun (fun x ↦ x *ᵥ e) at this
    rw [add_mulVec, add_mulVec, sub_mulVec, he, hesqr] at this
    have foo : d *ᵥ e = (d : β) • e := by
      change diagonal d *ᵥ e = _
      ext
      simp [mulVec_diagonal]
    have : (l ^ 2 + l - (↑d - 1)) • e = 0 := by
      convert this using 1
      · simp only [sub_smul, add_smul, one_smul, one_mulVec, nsmul_eq_mul, mul_one, foo]
        ring
      · ext i
        simp [mulVec, ho]
    rw [smul_eq_zero_iff_left hnz] at this
    exact this
  have hA' : IsHermitian A := by
    dsimp only [A];
    ext
    rw [conjTranspose, RCLike.star_def, transpose_adjMatrix, map_apply, adjMatrix_apply,
      RingHom.map_ite_one_zero]
  let s : β := √(4 * d - 3)
  have ein (i : α) : hA'.eigenvalues i = 1 ∨ hA'.eigenvalues i = (- s - 1) / 2
      ∨ hA'.eigenvalues i = (s - 1) / 2 := by
      by_cases hi : hA'.eigenvalues i = 1
      · apply Or.inl hi
      · have ho : f ⬝ᵥ (hA'.eigenvectorMatrix i) = 0 := by -- orthonormal eigenvectorMatrix
          sorry
        have hein : (hA'.eigenvectorMatrix i) ∈ Module.End.eigenspace
            (Matrix.toLin' A) (hA'.eigenvalues i) := by
          rw [Module.End.mem_eigenspace_iff, toLin'_apply]
          simp [hA'.eigenvalues_eq]
          sorry
        sorry
  sorry
