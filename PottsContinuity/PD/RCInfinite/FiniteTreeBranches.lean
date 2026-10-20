-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/FiniteTreeBranches.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.TerminalSeparation
public import PottsContinuity.PD.RCInfinite.TreeCounting

@[expose] public section

open Set

namespace PottsContinuity.PD.RCInfinite
noncomputable section
open scoped Classical

/-- Distinct neighbors in a tree cannot be connected after removing their
common neighbor. -/
theorem tree_distinct_neighbors_separated_after_delete
    {V : Type*} (G : SimpleGraph V) (hG : G.IsTree)
    {v u w : V} (huv : G.Adj v u) (hvw : G.Adj v w) (huw : u ≠ w) :
    ¬(G.deleteIncidenceSet v).Reachable u w := by
  intro hreach
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  let pG : G.Walk u w := p.transfer G fun e he =>
    SimpleGraph.edgeSet_mono (SimpleGraph.deleteIncidenceSet_le G v)
      (p.edges_subset_edgeSet he)
  have hpG : pG.IsPath := by simpa [pG] using hp
  have hvAvoidP : v ∉ p.support := by
    intro hvp
    have hnonil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne huw
    have hvSupport : v ∈ (G.deleteIncidenceSet v).support :=
      (G.deleteIncidenceSet v).mem_support_of_mem_walk_support p hnonil hvp
    have hsubset := SimpleGraph.support_deleteIncidenceSet_subset G v hvSupport
    change v ∈ G.support ∧ v ∉ ({v} : Set V) at hsubset
    exact hsubset.2 (by simp)
  have hvAvoid : v ∉ pG.support := by
    simpa [pG, SimpleGraph.Walk.transfer] using hvAvoidP
  let pLong : G.Walk v w := SimpleGraph.Walk.cons huv pG
  have hpLong : pLong.IsPath := by
    exact (SimpleGraph.Walk.cons_isPath_iff huv pG).2 ⟨hpG, hvAvoid⟩
  let pShort : G.Walk v w := SimpleGraph.Walk.cons hvw SimpleGraph.Walk.nil
  have hpShort : pShort.IsPath := by
    simp [pShort, SimpleGraph.Walk.cons_isPath_iff, hvw.ne]
  obtain ⟨pUnique, hpUnique, hUnique⟩ := hG.existsUnique_path v w
  have hlongEq : pLong = pUnique := hUnique pLong hpLong
  have hshortEq : pShort = pUnique := hUnique pShort hpShort
  have hlength : pLong.length = pShort.length :=
    congrArg SimpleGraph.Walk.length (hlongEq.trans hshortEq.symm)
  have hpos : 0 < pG.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact huw (pG.eq_of_length_eq_zero hzero)
  simp only [pLong, pShort, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_nil] at hlength
  omega

/-- Every branch of a finite tree after deleting a vertex contains an original
leaf. -/
theorem tree_neighbor_deleted_component_contains_leaf
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (v u : V) (huv : G.Adj v u) :
    ∃ w, (G.deleteIncidenceSet v).Reachable u w ∧ G.degree w = 1 := by
  classical
  let Q := G.deleteIncidenceSet v
  let C : Q.ConnectedComponent := Q.connectedComponentMk u
  have huvne : u ≠ v := huv.ne.symm
  have huC : u ∈ C.supp := by simp [C]
  have hvC : v ∉ C.supp := by
    intro hmem
    have hreach : Q.Reachable v u := C.reachable_of_mem_supp hmem huC
    have hsupport : v ∈ Q.support := Q.mem_support_of_reachable (Ne.symm huvne) hreach
    have hsubset := SimpleGraph.support_deleteIncidenceSet_subset G v hsupport
    change v ∈ G.support ∧ v ∉ ({v} : Set V) at hsubset
    exact hsubset.2 (by simp)
  have hCconnQ : (Q.induce C.supp).Connected := by
    have h := C.connected_toSubgraph.induce_verts
    change (Q.induce C.supp).Connected at h
    exact h
  have hCconnG : (G.induce C.supp).Connected := by
    apply hCconnQ.mono
    intro a b hab
    exact SimpleGraph.deleteIncidenceSet_le G v hab
  have hpair : (G.induce ({u, v} : Set V)).Connected :=
    SimpleGraph.induce_pair_connected_of_adj huv.symm
  have hinter : (C.supp ∩ ({u, v} : Set V)).Nonempty := ⟨u, huC, by simp⟩
  let S : Set V := C.supp ∪ {u, v}
  have hSconn : (G.induce S).Connected := by
    exact G.induce_union_connected hCconnG.preconnected hpair.preconnected hinter
  have huS : u ∈ S := by simp [S, huC]
  have hvS : v ∈ S := by simp [S]
  let : Fintype S := Subtype.fintype (Membership.mem S)
  let : G.LocallyFinite := fun w => Subtype.fintype (Membership.mem (G.neighborSet w))
  let : (G.induce S).LocallyFinite :=
    fun w => Subtype.fintype (Membership.mem ((G.induce S).neighborSet w))
  have htree : (G.induce S).IsTree :=
    ⟨hSconn, hG.isAcyclic.induce S⟩
  let : Nontrivial S := ⟨⟨⟨u, huS⟩, ⟨v, hvS⟩,
    fun heq => huvne (congrArg Subtype.val heq)⟩⟩
  obtain ⟨a, b, hab, ha, hb⟩ := htree.exists_ne_and_degree_eq_one
  have chooseLeaf : ∀ w : S, (G.induce S).degree w = 1 → w.val ≠ v →
      ∃ x, x ∈ C.supp ∧ x ≠ v ∧ G.degree x = 1 := by
    intro w hwdeg hwne
    have hwC : w.val ∈ C.supp := by
      have hwmem := w.property
      simp only [S, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
      rcases hwmem with h | h | h
      · exact h
      · have hval : w.val = u := h
        simpa [hval] using huC
      · have hval : w.val = v := h
        rw [hval] at hwne
        exact (hwne rfl).elim
    have hneighbors : G.neighborSet w.val ⊆ S := by
      intro x hx
      by_cases hxv : x = v
      · simp [S, hxv]
      · have hQ : Q.Adj w.val x := by
          exact SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hx, hwne, hxv⟩
        have hxC : x ∈ C.supp := C.mem_supp_of_adj_mem_supp hwC hQ
        exact Set.mem_union_left _ hxC
    have hdeg : (G.induce S).degree w = G.degree w :=
      G.degree_induce_of_neighborSet_subset hneighbors
    exact ⟨w.val, hwC, hwne, hdeg.symm ▸ hwdeg⟩
  by_cases hav : a.val = v
  · have hbv : b.val ≠ v := by
      intro heq
      apply hab
      exact Subtype.ext (hav.trans heq.symm)
    obtain ⟨w, hwC, hwne, hwdeg⟩ := chooseLeaf b hb hbv
    have hreach := C.reachable_of_mem_supp huC hwC
    exact ⟨w, hreach, hwdeg⟩
  · obtain ⟨w, hwC, hwne, hwdeg⟩ := chooseLeaf a ha hav
    have hreach := C.reachable_of_mem_supp huC hwC
    exact ⟨w, hreach, hwdeg⟩

/-- In a finite tree with exactly three designated leaves, some vertex
separates the three terminal branches. -/
theorem tree_three_leaves_have_separator
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (T : Finset V) (hTcard : T.card = 3)
    (hleaf : ∀ v, G.degree v = 1 → v ∈ T)
    (hTleaf : ∀ v ∈ T, G.degree v = 1) :
    ∃ v, SeparatesThreeTerminals G (T : Set V) v := by
  classical
  let : G.LocallyFinite := fun v => Subtype.fintype (Membership.mem (G.neighborSet v))
  obtain ⟨a₀, b₀, ha₀, hb₀, hne₀⟩ :=
    Finset.one_lt_card_iff.mp (by omega : 1 < T.card)
  let : Nontrivial V := ⟨⟨a₀, b₀, hne₀⟩⟩
  let L : Finset V := Finset.univ.filter fun v => G.degree v = 1
  have hLT : L ⊆ T := by
    intro v hv
    exact hleaf v (Finset.mem_filter.mp hv).2
  have hTL : T ⊆ L := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hTleaf v hv⟩
  have hLcard : L.card = 3 := by
    have hle := Finset.card_le_card hLT
    have hge := Finset.card_le_card hTL
    omega
  let B : Finset V := Finset.univ.filter fun v => 3 ≤ G.degree v
  have hBbound : B.card + 2 ≤ L.card := by
    change (Finset.univ.filter fun v : V => 3 ≤ G.degree v).card + 2 ≤ L.card
    exact tree_branch_card_add_two_le_leaf_card G hG
  have hBne : B.card ≠ 0 := by
    intro hBzero
    have hno (w : V) : ¬ 3 ≤ G.degree w := by
      intro hw
      have hwB : w ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
      have : 0 < B.card := Finset.card_pos.mpr ⟨w, hwB⟩
      omega
    have hpos (w : V) : 0 < G.degree w :=
      lt_of_lt_of_le hG.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree w)
    have hpoint (w : V) :
        G.degree w + (if G.degree w = 1 then 1 else 0) = 2 := by
      have hp := hpos w
      have hn := hno w
      split_ifs with hleafw
      · omega
      · have hge : 2 ≤ G.degree w := by omega
        have hlt : G.degree w < 3 := by omega
        omega
    have hsum := Finset.sum_congr (rfl : Finset.univ = Finset.univ)
      (fun w _ => hpoint w)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Finset.sum_boole, Nat.cast_id] at hsum
    have hdegrees := G.sum_degrees_eq_twice_card_edges
    have hcard := hG.card_edgeFinset
    rw [hLcard] at hsum
    omega
  have hBpos : 0 < B.card := Nat.pos_of_ne_zero hBne
  obtain ⟨v, hvB⟩ := Finset.card_pos.mp hBpos
  have hvdeg : 3 ≤ G.degree v := (Finset.mem_filter.mp hvB).2
  have hNcard : 3 ≤ Fintype.card (G.neighborSet v) := by
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using hvdeg
  let s : Finset (G.neighborSet v) := Finset.univ
  have hscard : 3 ≤ s.card := by simpa [s] using hNcard
  obtain ⟨s₃, hs₃, hs₃card⟩ := Finset.exists_subset_card_eq hscard
  obtain ⟨a, b, c, hab, hac, hbc, hsEq⟩ := Finset.card_eq_three.mp hs₃card
  let ys : Fin 3 → V := fun j =>
    if j.val = 0 then a.val else if j.val = 1 then b.val else c.val
  have hAdj (j : Fin 3) : G.Adj v (ys j) := by
    fin_cases j
    · change G.Adj v a.val
      exact a.property
    · change G.Adj v b.val
      exact b.property
    · change G.Adj v c.val
      exact c.property
  have hys_inj : Function.Injective ys := by
    intro j k hEq
    fin_cases j <;> fin_cases k <;> simp [ys] at hEq ⊢
    all_goals first
      | exact (hab (Subtype.ext hEq)).elim
      | exact (hab.symm (Subtype.ext hEq)).elim
      | exact (hac (Subtype.ext hEq)).elim
      | exact (hac.symm (Subtype.ext hEq)).elim
      | exact (hbc (Subtype.ext hEq)).elim
      | exact (hbc.symm (Subtype.ext hEq)).elim
  have hbranch (j : Fin 3) :
      ∃ t, (G.deleteIncidenceSet v).Reachable (ys j) t ∧ t ∈ T := by
    obtain ⟨t, hreach, hdeg⟩ :=
      tree_neighbor_deleted_component_contains_leaf G hG v (ys j) (hAdj j)
    exact ⟨t, hreach, hleaf t hdeg⟩
  choose ts hreach hterm using hbranch
  refine ⟨v, ?_⟩
  refine ⟨ts, ?_, ?_⟩
  · intro j
    have hreachG : G.Reachable (ys j) (ts j) :=
      (hreach j).mono (SimpleGraph.deleteIncidenceSet_le G v)
    have htv : ts j ≠ v := by
      intro heq
      have hdeg := hTleaf (ts j) (hterm j)
      rw [heq] at hdeg
      omega
    exact ⟨(hAdj j).reachable.trans hreachG, hterm j, htv⟩
  · intro j k hjk hconn
    have hconn' : (G.deleteIncidenceSet v).Reachable (ys j) (ys k) :=
      ((hreach j).trans hconn).trans (hreach k).symm
    exact (tree_distinct_neighbors_separated_after_delete G hG
      (hAdj j) (hAdj k) (fun heq => hjk (hys_inj heq))) hconn'

end
end PottsContinuity.PD.RCInfinite
