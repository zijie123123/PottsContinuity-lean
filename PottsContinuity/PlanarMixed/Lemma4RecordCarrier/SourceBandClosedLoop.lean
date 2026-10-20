module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.SourceTraceStrip
public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.SourceBandStoppingRecords
public import PottsContinuity.Thm3.RSW.FiniteClosedDualWalk

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality RSW
noncomputable section

/-- A genuine open dual walk crosses only absent original sampled bonds.
Closing it by reversal invokes the existing finite closure theorem. -/
theorem finiteClosedDualWalk_crossed_edge_absent
    (V : Finset LatticeVertex)
    (A : Configuration (PD.FK.squareLattice.induce (V : Set LatticeVertex)))
    {u v : LatticeVertex}
    (p : (wholePlaneClosedDualGraph (PD.RCInfinite.finiteSubgraphConfiguration V 0 A)).Walk u v)
    (b : LatticeBond) (hb : (dualBondOfPrimal b).toSym2 ∈
      (p.map (finiteClosedDualLatticeHom V A)).edges)
    (e : (PD.FK.squareLattice.induce (V : Set LatticeVertex)).edgeSet)
    (heq : Sym2.map Subtype.val e.val=b.toSym2) : e ∉ A := by
  have h := finiteDualWalkClosed_of_closedDualWalk V A (p.append p.reverse)
  apply h b _ e heq
  rw [SimpleGraph.Walk.map_append,SimpleGraph.Walk.edges_append,List.mem_append]
  exact Or.inl hb

/-- The exact source B_n supplies an actual closed loop around both entire
cores. No highest-crossing selector or record premise occurs. -/
theorem lemma4_source_band_exists_closed_core_loop
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n) :
    ∃ s : LatticeVertex, ∃ P : PD.FK.squareLattice.Walk s s,
      finiteDualWalkClosed (box (56*n)) A P ∧
      (∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1) ∧
      (∀ z ∈ ({(-5*(n:ℤ),0),(5*(n:ℤ),0)} : Set LatticeVertex),
        ∀ u ∈ vertexBoxRegion (box (56*n)) z (2*n), ∀ w,
          ActualConnected _ A u w → rayIndex w.val P=1 ∧
            -3*(n:ℤ) < w.val.2 ∧ w.val.2 < 3*(n:ℤ)) := by
  obtain ⟨u,v,upper,hu,hv,hupper⟩ := hA.2.1
  obtain ⟨s,t,lower,hs,ht,hlower⟩ := hA.2.2
  let f := finiteClosedDualLatticeHom (box (56*n)) A
  let p : PD.FK.squareLattice.Walk (-56*(n:ℤ)-1,s.2) (56*(n:ℤ),t.2) :=
    (lower.map f).copy (Prod.ext hs rfl) (Prod.ext ht rfl)
  let q : PD.FK.squareLattice.Walk (56*(n:ℤ),v.2) (-56*(n:ℤ)-1,u.2) :=
    (upper.reverse.map f).copy (Prod.ext hv rfl) (Prod.ext hu rfl)
  have hpS : p.support=lower.support := by
    simp only [p,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map]
    change List.map id lower.support=lower.support
    exact List.map_id _
  have hqS : q.support=upper.support.reverse := by
    simp only [q,SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_reverse]
    change List.map id upper.support.reverse=upper.support.reverse
    exact List.map_id _
  have hp : ∀ z ∈ p.support, -3*(n:ℤ) ≤ z.2 ∧ z.2 < -2*(n:ℤ) := by
    intro z hz
    rw [hpS] at hz
    have h := hlower z hz
    exact ⟨h.2.2.1,by omega⟩
  have hq : ∀ z ∈ q.support, 2*(n:ℤ) ≤ z.2 ∧ z.2 ≤ 3*(n:ℤ)-1 := by
    intro z hz
    rw [hqS,List.mem_reverse] at hz
    exact (hupper z hz).2.2
  have hpclosed : ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ p.edges →
      ∀ e : (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)).edgeSet,
        Sym2.map Subtype.val e.val=b.toSym2 → e ∉ A := by
    intro b hb e heq
    apply finiteClosedDualWalk_crossed_edge_absent (box (56*n)) A lower b _ e heq
    simpa only [p,SimpleGraph.Walk.edges_copy] using hb
  have hqclosed : ∀ b : LatticeBond, (dualBondOfPrimal b).toSym2 ∈ q.edges →
      ∀ e : (PD.FK.squareLattice.induce (box (56*n) : Set LatticeVertex)).edgeSet,
        Sym2.map Subtype.val e.val=b.toSym2 → e ∉ A := by
    intro b hb e heq
    apply finiteClosedDualWalk_crossed_edge_absent (box (56*n)) A upper.reverse b _ e heq
    simpa only [q,SimpleGraph.Walk.edges_copy] using hb
  obtain ⟨P,hclosed,hstrip,hcore⟩ := lemma4_closed_trace_pair_core_strip n hn A
    s.2 t.2 v.2 u.2 p q hp hq hpclosed hqclosed
  exact ⟨_,P,hclosed,hstrip,hcore⟩

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
