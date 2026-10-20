module

public import PottsContinuity.PlanarTopology.OpenArchRayIndex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- A full vertical screen preserves its index across every uncrossed primal
bond whose lower row is different from both screen endpoint rows. -/
theorem screenIndex_eq_of_uncrossed_adj {s t u v : LatticeVertex}
    (p : squareLattice.Walk s t) (hadj : squareLattice.Adj u v)
    (hs : u.2 ≠ v.2 → s.2 ≠ min u.2 v.2)
    (ht : u.2 ≠ v.2 → t.2 ≠ min u.2 v.2)
    (havoid : ∀ b : LatticeBond, b.toSym2=s(u,v) →
      (dualBondOfPrimal b).toSym2 ∉ p.edges) :
    rayIndex u p=rayIndex v p := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  have hc := (squareLattice_adj_iff _ _).mp hadj
  dsimp only at hc hs ht
  rcases hc with ⟨hx | hx,hy⟩ | ⟨hx,hy | hy⟩
  · subst c; subst d
    exact rayIndex_horizontal_invariant a b p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(a,b),.horizontal⟩ rfl)
  · subst a; subst d
    exact (rayIndex_horizontal_invariant c b p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(c,b),.horizontal⟩ Sym2.eq_swap)).symm
  · subst c; subst d
    have hs' := hs (by omega)
    have ht' := ht (by omega)
    have hd := rayIndex_vertical_difference a b p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(a,b),.vertical⟩ rfl)
    change rayIndex (a,b+1) p-rayIndex (a,b) p =
      (if s.2=b ∧ a ≤ s.1 then 1 else 0)-(if t.2=b ∧ a ≤ t.1 then 1 else 0) at hd
    rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hd
    omega
  · subst c; subst b
    have hs' := hs (by omega)
    have ht' := ht (by omega)
    have hd := rayIndex_vertical_difference a d p
      (by simpa [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
        LatticeBond.target] using havoid ⟨(a,d),.vertical⟩ Sym2.eq_swap)
    change rayIndex (a,d+1) p-rayIndex (a,d) p =
      (if s.2=d ∧ a ≤ s.1 then 1 else 0)-(if t.2=d ∧ a ≤ t.1 then 1 else 0) at hd
    rw [ite_eq_right (by omega),ite_eq_right (by omega)] at hd
    omega

/-- Off a full screen trace, the lower two corners of a dual face have the
same screen index. -/
theorem screenIndex_face_bottom_corners {s t : LatticeVertex}
    (p : squareLattice.Walk s t) (z : LatticeVertex) (hz : z ∉ p.support) :
    rayIndex z p=rayIndex (z.1+1,z.2) p := by
  apply rayIndex_horizontal_invariant
  intro he
  exact hz (SimpleGraph.Walk.mem_support_of_mem_edges he (Sym2.mem_mk_right _ _))

/-- Off a full screen trace and away from its endpoint rows, the left two
corners of a dual face have the same screen index. -/
theorem screenIndex_face_left_corners {s t : LatticeVertex}
    (p : squareLattice.Walk s t) (z : LatticeVertex) (hz : z ∉ p.support)
    (hs : s.2 ≠ z.2) (ht : t.2 ≠ z.2) :
    rayIndex z p=rayIndex (z.1,z.2+1) p := by
  have hd := rayIndex_vertical_difference z.1 z.2 p (by
    intro he
    exact hz (SimpleGraph.Walk.mem_support_of_mem_edges he (Sym2.mem_mk_right _ _)))
  change rayIndex (z.1,z.2+1) p-rayIndex z p =
    (if s.2=z.2 ∧ z.1 ≤ s.1 then 1 else 0)-(if t.2=z.2 ∧ z.1 ≤ t.1 then 1 else 0) at hd
  rw [ite_eq_right (fun h => hs h.1),ite_eq_right (fun h => ht h.1)] at hd
  omega

/-- The lower-left-corner index is constant along a dual step avoiding every
vertex of the full screen trace. -/
theorem screenIndex_eq_of_dual_adj_off_trace {s t u v : LatticeVertex}
    (p : squareLattice.Walk s t) (hadj : squareLattice.Adj u v)
    (hu : u ∉ p.support) (hv : v ∉ p.support)
    (hs : s.2 ≠ min u.2 v.2) (ht : t.2 ≠ min u.2 v.2) :
    rayIndex u p=rayIndex v p := by
  have hc := (squareLattice_adj_iff _ _).mp hadj
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  dsimp only at hc hs ht
  rcases hc with ⟨hx | hx,hy⟩ | ⟨hx,hy | hy⟩
  · subst c; subst d
    exact screenIndex_face_bottom_corners p (a,b) hu
  · subst a; subst d
    exact (screenIndex_face_bottom_corners p (c,b) hv).symm
  · subst c; subst d
    exact screenIndex_face_left_corners p (a,b) hu (by omega) (by omega)
  · subst c; subst b
    exact (screenIndex_face_left_corners p (a,d) hv (by omega) (by omega)).symm

/-- A dual walk in the complement of the full screen trace stays on one side
of that screen. The walk may visit any number of detached square excursions. -/
theorem screenIndex_eq_of_dual_walk_off_trace {s t u v : LatticeVertex}
    (p : squareLattice.Walk s t) (q : squareLattice.Walk u v)
    (htrace : ∀ z ∈ q.support, z ∉ p.support)
    (hrows : ∀ z ∈ q.support, s.2 < z.2 ∧ z.2 < t.2) :
    rayIndex u p=rayIndex v p := by
  induction q with
  | nil => rfl
  | @cons u z v hadj q ih =>
    have hu := hrows u (by simp)
    have hz := hrows z (by simp)
    exact (screenIndex_eq_of_dual_adj_off_trace p hadj
      (htrace u (by simp)) (htrace z (by simp)) (by omega) (by omega)).trans
      (ih (fun a ha => htrace a (by simp [ha])) (fun a ha => hrows a (by simp [ha])))

/-- All four original primal corners of an off-trace dual face have the same
index. This includes the two corners of every primal bond touching that face. -/
theorem screenIndex_face_corners {s t : LatticeVertex}
    (p : squareLattice.Walk s t) (z w : LatticeVertex) (hz : z ∉ p.support)
    (hs : s.2 ≠ z.2) (ht : t.2 ≠ z.2)
    (hx : w.1=z.1 ∨ w.1=z.1+1) (hy : w.2=z.2 ∨ w.2=z.2+1) :
    rayIndex w p=rayIndex z p := by
  have hb := screenIndex_face_bottom_corners p z hz
  have hl := screenIndex_face_left_corners p z hz hs ht
  have hd := rayIndex_vertical_difference (z.1+1) z.2 p (by
    intro he
    apply hz
    apply SimpleGraph.Walk.mem_support_of_mem_edges he
    exact Sym2.mem_iff'.mpr (Or.inl (by ext <;> simp)))
  change rayIndex (z.1+1,z.2+1) p-rayIndex (z.1+1,z.2) p =
    (if s.2=z.2 ∧ z.1+1 ≤ s.1 then 1 else 0)-
    (if t.2=z.2 ∧ z.1+1 ≤ t.1 then 1 else 0) at hd
  rw [ite_eq_right (fun h => hs h.1),ite_eq_right (fun h => ht h.1)] at hd
  rcases w with ⟨x,y⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    dsimp only at hx hy <;> subst x <;> subst y
  · rfl
  · exact hl.symm
  · exact hb.symm
  · omega

/-- An original crossed bond incident to an off-trace face has the index of
that face at either primal endpoint. Original normalized bond labels are retained. -/
theorem screenIndex_crossedBond_endpoint {s t : LatticeVertex}
    (p : squareLattice.Walk s t) (b : LatticeBond) (z w : LatticeVertex)
    (hz : z ∉ p.support) (hs : s.2 ≠ z.2) (ht : t.2 ≠ z.2)
    (hzface : z ∈ (dualBondOfPrimal b).toSym2) (hwend : w ∈ b.toSym2) :
    rayIndex w p=rayIndex z p := by
  apply screenIndex_face_corners p z w hz hs ht <;>
    rcases Sym2.mem_iff'.mp hzface with rfl | rfl <;>
    rcases Sym2.mem_iff'.mp hwend with rfl | rfl <;>
    rcases b with ⟨⟨x,y⟩,a⟩ <;> cases a <;>
    simp [dualBondOfPrimal,LatticeBond.source,LatticeBond.target]

end
end PottsContinuity.Thm4Records
