module

public import PottsContinuity.Thm3.Push.SlitBarrierRowIndex
public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.Thm3.Push.IntervalArmDualPorts
public import PottsContinuity.Thm3.Push.SideCollarExtension

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality PlanarMixed.FiniteSlit

/-- The exact right/bottom raw-exploration ports all carry index minus one
for the constructed collar barrier, including isolated expanded corners. -/
theorem sideCollar_barrier_right_ports_index
    (w h : ℕ) (b r y : ℤ) (hb : 2 < b) (hbr : b ≤ r)
    (q : squareLattice.Walk (b,0) (2,y))
    (hq : ∀ z ∈ q.support, z.1 ≤ (w:ℤ)+2 ∧ 0 ≤ z.2)
    (p : squareLattice.Walk (b,0) (b,0))
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges (sideCollarSize w h+2) 2 y b q)
    (hβ : ∀ t : Vertex (sideCollarSize w h+2) 2,
      t ∈ beta (sideCollarSize w h+2) 2 y → t.val ∉ q.support → rayIndex t.val p = -1)
    (u : RectangleDualVertex (0,0) (sideCollarSize w h) (sideCollarSize w h))
    (hu : u ∈ intervalArmRightDualPorts (sideCollarSize w h) r) :
    rayIndex (faceIndexMark u.val) p = -1 := by
  let N := sideCollarSize w h
  let M := N+2
  have hN : (w:ℤ)+2 < (N:ℤ)+1 := by dsimp [N,sideCollarSize]; omega
  have hbN : b < (N:ℤ)+1 := lt_of_le_of_lt (hq _ q.start_mem_support).1 hN
  have hbound := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  change ((-1:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ -1+((N+1:ℕ):ℤ)) ∧
    ((-1:ℤ) ≤ u.val.2 ∧ u.val.2 ≤ -1+((N+1:ℕ):ℤ)) at hbound
  have houter (Y : ℤ) (hY0 : 0 ≤ Y) (hYM : Y ≤ (M:ℤ)) :
      rayIndex ((M:ℤ)+1,Y) p = -1 := by
    let v : Vertex M 2 := ⟨((M:ℤ)+1,Y),(mem_rectangle_iff M 2 (by dsimp [M,N,sideCollarSize]; omega) _).mpr
      ⟨by dsimp [M,N,sideCollarSize]; omega,by omega,hY0,hYM⟩⟩
    apply hβ v
    · exact Or.inl (by change (M:ℤ)+1 = 2+(M:ℤ)-1; omega)
    · intro hv
      have hh := (hq v.val hv).1
      change (M:ℤ)+1 ≤ (w:ℤ)+2 at hh
      dsimp [M] at hh
      omega
  rcases (mem_intervalArmRightDualPorts _ r u).mp hu with hur | ⟨huy,hr⟩
  · have hrow := slitBarrier_right_of_trace_index_eq_boundary M (by dsimp [M]; omega) b y (u.val.2+1) ((N:ℤ)+1)
      (by omega) (by dsimp [M]; omega) (by dsimp [N,sideCollarSize]; omega) hbN
      (by dsimp [M]; omega) q (fun z hz => lt_of_le_of_lt (hq z hz).1 hN) p hallowed
    have hidx := hrow.trans (houter _ (by omega) (by dsimp [M]; omega))
    simpa only [faceIndexMark,hur] using hidx
  · have hrow := slitBarrier_bottom_right_index_eq_boundary M (by dsimp [M]; omega) b y (u.val.1+1)
      hb (by omega) (by dsimp [M]; omega) q (fun z hz => (hq z hz).2) p hallowed
    have hidx := hrow.trans (houter 0 (by omega) (by dsimp [M]; omega))
    simpa only [faceIndexMark,huy,neg_add_cancel] using hidx

end PottsContinuity.Push
