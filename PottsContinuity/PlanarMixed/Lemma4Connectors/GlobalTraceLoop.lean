module

public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import PottsContinuity.PlanarTopology.ArchRayIndex
public import PottsContinuity.Thm3.RSW.FiniteDualScreen

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality RSW PlanarTopology
noncomputable section

/-- Close the two full original traces along the two exterior columns.
No cropped trace, simplicity, or monotonicity of either trace is needed. -/
theorem exists_betweenTraceLoop (l r lo hi midlo midhi : ℤ)
    (hmid : midlo ≤ midhi)
    (a b c d : ℤ)
    (p : PD.FK.squareLattice.Walk (l,a) (r,b))
    (q : PD.FK.squareLattice.Walk (r,c) (l,d))
    (hp : ∀ z ∈ p.support, lo ≤ z.2 ∧ z.2 < midlo)
    (hq : ∀ z ∈ q.support, midhi ≤ z.2 ∧ z.2 ≤ hi) :
    ∃ P : PD.FK.squareLattice.Walk (l,a) (l,a),
      (∀ z ∈ P.support, lo ≤ z.2 ∧ z.2 ≤ hi) ∧
      (∀ e ∈ P.edges, e ∈ p.edges ∨ e ∈ q.edges ∨
        (∀ z ∈ e, z.1 = l) ∨ (∀ z ∈ e, z.1 = r)) ∧
      (∀ v : LatticeVertex, l < v.1 → v.1 ≤ r → midlo ≤ v.2 → v.2 ≤ midhi →
        rayIndex v P = 1) := by
  have ha := hp _ p.start_mem_support
  have hb := hp _ p.end_mem_support
  have hc := hq _ q.start_mem_support
  have hd := hq _ q.end_mem_support
  obtain ⟨R,hR⟩ := vertical_walk_between r b c
  obtain ⟨L,hL⟩ := vertical_walk_between l d a
  let P := p.append (R.append (q.append L))
  refine ⟨P,?_,?_,?_⟩
  · intro z hz
    simp only [P,SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz | hz | hz
    · exact ⟨(hp z hz).1,by have := hp z hz; omega⟩
    · have h := hR z hz
      rw [min_eq_left (by omega : b ≤ c),max_eq_right (by omega : b ≤ c)] at h
      exact ⟨by omega,by omega⟩
    · exact ⟨by have := hq z hz; omega,(hq z hz).2⟩
    · have h := hL z hz
      rw [min_eq_right (by omega : a ≤ d),max_eq_left (by omega : a ≤ d)] at h
      exact ⟨by omega,by omega⟩
  · intro e he
    simp only [P,SimpleGraph.Walk.edges_append,List.mem_append] at he
    rcases he with he | he | he | he
    · exact Or.inl he
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      intro z hz
      have hends := R.mem_support_of_mem_edges he hz
      exact (hR z hends).1
    · exact Or.inr (Or.inl he)
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      intro z hz
      exact (hL z (L.mem_support_of_mem_edges he hz)).1
  · intro v hvl hvr hvlo hvhi
    have hpidx : rayIndex v p = 0 := by
      apply rayIndex_zero_of_level v p 1
      intro z hz
      exact ite_eq_left (by have := hp z hz; omega)
    have hqidx : rayIndex v q = 0 := by
      apply rayIndex_zero_of_level v q 0
      intro z hz
      exact ite_eq_right (by have := hq z hz; omega)
    have hLidx : rayIndex v L = 0 := by
      apply rayIndex_zero_of_right v L
      intro z hz
      have := (hL z hz).1
      omega
    have hRidx : rayIndex v R = 1 := by
      rw [rayIndex_left_telescope v R (by
        intro z hz
        have := (hR z hz).1
        omega)]
      simp only [ite_eq_left (by omega : b < v.2),ite_eq_right (by omega : ¬ c < v.2)]
      norm_num
    simp only [P,rayIndex_append,hpidx,hqidx,hLidx,hRidx]
    norm_num

/-- A nonzero-index component of any closed original-bond trace loop stays
in its strict lower/inclusive upper vertical range. -/
theorem closedTraceLoop_component_strip
    (V : Finset LatticeVertex)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    {s : LatticeVertex} (P : PD.FK.squareLattice.Walk s s)
    (hclosed : finiteDualWalkClosed V A P) (lo hi : ℤ)
    (hsupport : ∀ z ∈ P.support, lo ≤ z.2 ∧ z.2 ≤ hi)
    {u w : (V : Set LatticeVertex)} (hu : rayIndex u.val P ≠ 0)
    (huw : ActualConnected _ A u w) :
    rayIndex w.val P ≠ 0 ∧ lo < w.val.2 ∧ w.val.2 ≤ hi := by
  have heq := rayIndex_eq_of_avoidance_reachable P
    (huw.map (finiteDualScreenOpenHom V A P hclosed))
  change rayIndex u.val P = rayIndex w.val P at heq
  have hw : rayIndex w.val P ≠ 0 := by rw [← heq]; exact hu
  refine ⟨hw,?_,?_⟩
  · by_contra hn
    apply hw
    apply rayIndex_zero_of_level w.val P 0
    intro z hz
    exact ite_eq_right (by have := hsupport z hz; omega)
  · by_contra hn
    apply hw
    apply rayIndex_zero_of_level w.val P 1
    intro z hz
    exact ite_eq_left (by have := hsupport z hz; omega)

/-- Exterior vertical closure columns cross no sampled bond of the source. -/
theorem exterior_column_crossed_bond_absent
    (V : Finset LatticeVertex) (l r : ℤ)
    (hV : ∀ v ∈ V, l < v.1 ∧ v.1 ≤ r)
    (b : LatticeBond)
    (hcol : (∀ z ∈ (dualBondOfPrimal b).toSym2, z.1 = l) ∨
      (∀ z ∈ (dualBondOfPrimal b).toSym2, z.1 = r))
    (e : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (heq : Sym2.map Subtype.val e.val = b.toSym2) : False := by
  have hsource : b.source ∈ V := by
    have hm : b.source ∈ Sym2.map Subtype.val e.val := by
      rw [heq]
      exact Sym2.mem_mk_left _ _
    obtain ⟨v,_,hv⟩ := Sym2.mem_map.mp hm
    rw [← hv]
    exact v.property
  have htarget : b.target ∈ V := by
    have hm : b.target ∈ Sym2.map Subtype.val e.val := by
      rw [heq]
      exact Sym2.mem_mk_right _ _
    obtain ⟨v,_,hv⟩ := Sym2.mem_map.mp hm
    rw [← hv]
    exact v.property
  have hs := hV _ hsource
  have ht := hV _ htarget
  have hds : (dualBondOfPrimal b).source ∈ (dualBondOfPrimal b).toSym2 := Sym2.mem_mk_left _ _
  have hdt : (dualBondOfPrimal b).target ∈ (dualBondOfPrimal b).toSym2 := Sym2.mem_mk_right _ _
  rcases hcol with hcol | hcol
  all_goals
    have hc₁ := hcol _ hds
    have hc₂ := hcol _ hdt
    rcases b with ⟨⟨x,y⟩,axis⟩
    cases axis <;> simp only [dualBondOfPrimal,LatticeBond.source,LatticeBond.target] at hc₁ hc₂ hs ht <;> omega

/-- The loop retains only the two original closed traces and exterior caps;
all of its crossed sampled primal bonds are therefore actually closed. -/
theorem betweenTraceLoop_closed
    (V : Finset LatticeVertex)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    (l r : ℤ) (hV : ∀ v ∈ V, l < v.1 ∧ v.1 ≤ r)
    {a b c d s : LatticeVertex}
    (p : PD.FK.squareLattice.Walk a b) (q : PD.FK.squareLattice.Walk c d)
    (P : PD.FK.squareLattice.Walk s s)
    (hP : ∀ e ∈ P.edges, e ∈ p.edges ∨ e ∈ q.edges ∨
      (∀ z ∈ e, z.1 = l) ∨ (∀ z ∈ e, z.1 = r))
    (hp : ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ p.edges →
      ∀ e : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet,
        Sym2.map Subtype.val e.val = b.toSym2 → e ∉ A)
    (hq : ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ q.edges →
      ∀ e : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet,
        Sym2.map Subtype.val e.val = b.toSym2 → e ∉ A) :
    finiteDualWalkClosed V A P := by
  intro b hb e heq heA
  rcases hP _ hb with h | h | h | h
  · exact hp b h e heq heA
  · exact hq b h e heq heA
  · exact exterior_column_crossed_bond_absent V l r hV b (Or.inl h) e heq
  · exact exterior_column_crossed_bond_absent V l r hV b (Or.inr h) e heq

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
