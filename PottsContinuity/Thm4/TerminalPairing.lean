/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/FiniteTerminalPairing.lean`.
Adaptation: namespace relocation only.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
A finite graph component containing a degree-one vertex has another degree-one
vertex when the ambient graph has maximum degree two.  The proof applies the
finite handshaking theorem to the induced graph on the actual reachable
component; no path-shape hypothesis is used.
-/

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open SimpleGraph

private theorem walk_support_reachable_from {V : Type*} (G : SimpleGraph V)
    {s u v : V} (hus : G.Reachable s u) (p : G.Walk u v) :
    ∀ x ∈ p.support, G.Reachable s x := by
  induction p with
  | nil =>
    intro x hx
    simp only [Walk.support_nil, List.mem_singleton] at hx
    subst x
    exact hus
  | @cons u w v huw p ih =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hus
    · exact ih (hus.trans huw.reachable) x hx

/-- In a finite graph of maximum degree at most two, every degree-one vertex is
reachable from a distinct degree-one vertex. -/
theorem exists_ne_reachable_degree_one_of_degree_le_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v ≤ 2) (s : V) (hs : G.degree s = 1) :
    ∃ t : V, t ≠ s ∧ G.degree t = 1 ∧ G.Reachable s t := by
  classical
  let C : Type _ := {v : V // G.Reachable s v}
  let H : SimpleGraph C := G.induce (fun v : V => G.Reachable s v)
  let sC : C := ⟨s, Reachable.refl s⟩
  have hclosed (v : C) : G.neighborSet v.1 ⊆ {x : V | G.Reachable s x} := by
    intro x hx
    rw [mem_neighborSet] at hx
    exact v.2.trans hx.reachable
  have hdegree (v : C) : H.degree v = G.degree v.1 := by
    dsimp [H, C]
    exact G.degree_induce_of_neighborSet_subset (hclosed v)
  have hsC : H.degree sC = 1 := by
    rw [hdegree]
    exact hs
  have hodd : Odd (H.degree sC) := by
    rw [hsC]
    exact ⟨0, rfl⟩
  obtain ⟨tC, hts, htodd⟩ := exists_ne_odd_degree_of_exists_odd_degree H sC hodd
  have htbound : H.degree tC ≤ 2 := by
    rw [hdegree]
    exact hdeg tC.1
  have htC : H.degree tC = 1 := by
    rcases htodd with ⟨k, hk⟩
    rw [hk] at htbound
    omega
  refine ⟨tC.1, ?_, ?_, tC.2⟩
  · intro h
    apply hts
    apply Subtype.ext
    exact h
  · rw [← hdegree tC]
    exact htC

/-- The reachable component of a finite graph of maximum degree at most two
has exactly two degree-one vertices, provided it has one. -/
theorem existsUnique_ne_reachable_degree_one_of_degree_le_two
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v : V, G.degree v ≤ 2) (s : V) (hs : G.degree s = 1) :
    ∃! t : V, t ≠ s ∧ G.degree t = 1 ∧ G.Reachable s t := by
  classical
  obtain ⟨t, hts, ht, hst⟩ :=
    exists_ne_reachable_degree_one_of_degree_le_two G hdeg s hs
  refine ⟨t, ⟨hts, ht, hst⟩, ?_⟩
  intro u hu
  rcases hu with ⟨hus, hdu, hreach⟩
  by_cases hut : u = t
  · exact hut
  ·
  -- Work in the full reachable component; it is connected by construction.
    let C : Type _ := {v : V // G.Reachable s v}
    let H : SimpleGraph C := G.induce (fun v : V => G.Reachable s v)
    let sC : C := ⟨s, Reachable.refl s⟩
    let tC : C := ⟨t, hst⟩
    let uC : C := ⟨u, hreach⟩
    have hclosed (v : C) : G.neighborSet v.1 ⊆ {x : V | G.Reachable s x} := by
      intro x hx
      rw [mem_neighborSet] at hx
      exact v.2.trans hx.reachable
    have hdegree (v : C) : H.degree v = G.degree v.1 := by
      dsimp [H, C]
      exact G.degree_induce_of_neighborSet_subset (hclosed v)
    have hconn : H.Connected := by
      apply H.connected_iff_exists_forall_reachable.mpr
      refine ⟨sC, ?_⟩
      intro v
      rcases v.2 with ⟨p⟩
      have hsupport : ∀ x ∈ p.support, G.Reachable s x :=
        walk_support_reachable_from G (Reachable.refl s) p
      exact ⟨p.induce (fun x : V => G.Reachable s x) (fun x hx => hsupport x hx)⟩
    have hstC : tC ≠ sC := by
      intro h
      exact hts (congrArg Subtype.val h)
    have husC : uC ≠ sC := by
      intro h
      exact hus (congrArg Subtype.val h)
    let : Nontrivial C := ⟨⟨sC, tC, hstC.symm⟩⟩
    have hpos (v : C) : 0 < H.degree v :=
      hconn.preconnected.degree_pos_of_nontrivial v
    have hleaf (v : C) : H.degree v = 1 ∨ H.degree v = 2 := by
      have hbound : H.degree v ≤ 2 := by rw [hdegree]; exact hdeg v.1
      have hpositive := hpos v
      omega
    let leaves : Finset C := Finset.univ.filter fun v => H.degree v = 1
    have hsum : (∑ v : C, H.degree v) + leaves.card = 2 * Fintype.card C := by
      have hpoint (v : C) : H.degree v + (if v ∈ leaves then 1 else 0) = 2 := by
        simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hleaf v with h | h <;> simp [h]
      calc
        (∑ v : C, H.degree v) + leaves.card
            = (∑ v : C, H.degree v) + ∑ v : C, if v ∈ leaves then 1 else 0 := by simp [leaves]
        _ = ∑ v : C, (H.degree v + (if v ∈ leaves then 1 else 0)) := by rw [Finset.sum_add_distrib]
        _ = ∑ _v : C, (2 : ℕ) := by apply Finset.sum_congr rfl; intro v _; exact hpoint v
        _ = Fintype.card C * 2 := by simp
        _ = 2 * Fintype.card C := by omega
    have hhand := H.sum_degrees_eq_twice_card_edges
    have hcard := hconn.card_vert_le_card_edgeSet_add_one
    have hcard' : Fintype.card C ≤ H.edgeFinset.card + 1 := by
      simpa [Nat.card_eq_fintype_card, H.edgeFinset_card] using hcard
    have hleaves : leaves.card ≤ 2 := by
      have hsum' := hsum
      rw [hhand] at hsum'
      omega
    have hmem_t : tC ∈ leaves := by
      simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hdegree]
      exact ht
    have hmem_u : uC ∈ leaves := by
      simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hdegree]
      exact hdu
    have hmem_s : sC ∈ leaves := by
      simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hdegree]
      exact hs
    have hsu : sC ≠ uC := fun h => hus (congrArg Subtype.val h.symm)
    have hst' : sC ≠ tC := hstC.symm
    have htu : tC ≠ uC := by
      intro h
      apply hut
      exact congrArg Subtype.val h.symm
    have hthree : ({sC, tC, uC} : Finset C).card ≤ leaves.card := by
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hmem_s
      · exact hmem_t
      · exact hmem_u
    have hthreecard : ({sC, tC, uC} : Finset C).card = 3 := by
      simp [htu, hsu, hst']
    have hcard3 : 3 ≤ leaves.card := by
      rw [← hthreecard]
      exact hthree
    omega

end PottsContinuity.Thm4.Medial
