module

public import PottsContinuity.PlanarMixed.FiniteSlit.Domain
public import PottsContinuity.PlanarTopology.DisjointRayIndex

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality PlanarTopology
noncomputable section

/-- The allowed dual return edges of a slit crosscut: the actual trace,
its bottom attachment, the tip attachment, the deleted seam and the exterior. -/
def slitBarrierEdges (M : ℕ) (x y a : ℤ) {t : LatticeVertex}
    (p : PD.FK.squareLattice.Walk (a,0) t) : Set (Sym2 LatticeVertex) :=
  {e | e ∈ p.edges ∨ e = s((a,-1),(a,0)) ∨
    (e = s((x-1,y),(x,y)) ∧ (x,y) ∈ p.support) ∨
    ∃ u v : LatticeVertex, e = s(u,v) ∧
      ((u.1 = x-1 ∧ v.1 = x-1 ∧ y ≤ u.2 ∧ y ≤ v.2) ∨
       (u.2 < 0 ∧ v.2 < 0) ∨ ((M:ℤ) < u.2 ∧ (M:ℤ) < v.2) ∨
       (u.1 < x-(M:ℤ) ∧ v.1 < x-(M:ℤ)) ∨
       (x+(M:ℤ)-1 < u.1 ∧ x+(M:ℤ)-1 < v.1))}

/-- An allowed dual barrier edge can cross a retained bond only at a vertex
of the actual crosscut. In particular the left slit tip itself is retained. -/
theorem slitBarrier_crossing_touches_trace
    (M : ℕ) (x y a : ℤ) (hM : 2 ≤ M) {t : LatticeVertex}
    (p : PD.FK.squareLattice.Walk (a,0) t) (b : LatticeBond)
    (hb : (dualBondOfPrimal b).toSym2 ∈ slitBarrierEdges M x y a p)
    (u v : Vertex M x) (hG : (graph M x y).Adj u v)
    (he : b.toSym2 = s(u.val,v.val)) : b.source ∈ p.support := by
  have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hv := (mem_rectangle_iff M x (by omega) v.val).mp v.property
  rcases hb with hp | hroot | ⟨htip,ht⟩ | ⟨r,s,hrs,hout⟩
  · have hh := p.snd_mem_support_of_mem_edges hp
    rwa [dualBond_target_eq_source] at hh
  · have hh : (dualBondOfPrimal b).target = (a,0) := by
      rcases b with ⟨⟨i,j⟩,ax⟩
      cases ax <;> simp only [dualBondOfPrimal,LatticeBond.toSym2,
        LatticeBond.source,LatticeBond.target,Sym2.eq_iff,Prod.mk.injEq] at hroot ⊢ <;>
        rcases hroot with h | h <;> obtain ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ := h <;>
        constructor <;> omega
    rw [dualBond_target_eq_source] at hh
    exact hh.symm ▸ p.start_mem_support
  · have hh : (dualBondOfPrimal b).target = (x,y) := by
      rcases b with ⟨⟨i,j⟩,ax⟩
      cases ax <;> simp only [dualBondOfPrimal,LatticeBond.toSym2,
        LatticeBond.source,LatticeBond.target,Sym2.eq_iff,Prod.mk.injEq] at htip ⊢ <;>
        rcases htip with h | h <;> obtain ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ := h <;>
        constructor <;> omega
    rw [dualBond_target_eq_source] at hh
    exact hh.symm ▸ ht
  · exfalso
    have hret := hG.2
    rcases b with ⟨⟨i,j⟩,ax⟩
    cases ax <;>
      simp only [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target,Sym2.eq_iff] at he hrs <;>
      rcases he with he | he <;> rcases hrs with hrs | hrs <;>
      obtain ⟨h1,h2⟩ := he <;> obtain ⟨h3,h4⟩ := hrs <;>
      have h1x := congrArg Prod.fst h1 <;> have h1y := congrArg Prod.snd h1 <;>
      have h2x := congrArg Prod.fst h2 <;> have h2y := congrArg Prod.snd h2 <;>
      have h3x := congrArg Prod.fst h3 <;> have h3y := congrArg Prod.snd h3 <;>
      have h4x := congrArg Prod.fst h4 <;> have h4y := congrArg Prod.snd h4 <;>
      rcases hout with hs | hs | hs | hs | hs <;> dsimp at * <;> omega

/-- Every retained slit walk avoiding the actual trace also avoids the dual
barrier. This permits a return along the deleted seam without a Jordan input. -/
theorem rayIndex_eq_of_slitBarrier
    (M : ℕ) (x y a : ℤ) (hM : 2 ≤ M) {t z : LatticeVertex}
    (p : PD.FK.squareLattice.Walk (a,0) t) (C : PD.FK.squareLattice.Walk z z)
    (hC : ∀ e ∈ C.edges, e ∈ slitBarrierEdges M x y a p)
    {u v : Vertex M x} (r : (graph M x y).Walk u v)
    (hdis : ∀ w ∈ r.support, w.val ∉ p.support) :
    rayIndex u.val C = rayIndex v.val C := by
  have hedge : ∀ {u v : Vertex M x}, (graph M x y).Adj u v →
      u.val ∉ p.support → v.val ∉ p.support →
      (circuitAvoidanceGraph C).Adj u.val v.val := by
    intro u v huv hu hv
    refine ⟨huv.1,?_⟩
    intro b hb hc
    have hsource := slitBarrier_crossing_touches_trace M x y a hM p b (hC _ hc) u v huv hb
    have hmem : b.source ∈ s(u.val,v.val) := by
      rw [← hb]
      exact Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact hu (h ▸ hsource)
    · exact hv (h ▸ hsource)
  have hr : (circuitAvoidanceGraph C).Reachable u.val v.val := by
    induction r with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u w v huw r ih =>
      exact (hedge huw (hdis _ (by simp)) (hdis _ (by simp))).reachable.trans
        (ih (fun z hz => hdis z (by simp [hz])))
  exact rayIndex_eq_of_avoidance_reachable C hr

end
end PottsContinuity.PlanarMixed.FiniteSlit
