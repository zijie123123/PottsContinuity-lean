module

public import PottsContinuity.PlanarMixed.FiniteSlit.RightBarrierLoop
public import PottsContinuity.PlanarMixed.OrderedCutRegions

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.Duality PlanarTopology
noncomputable section

/-- Coordinate projection retains exactly the bonds of the finite slit graph. -/
def toLattice (M : ℕ) (x y : ℤ) : graph M x y →g PD.FK.squareLattice where
  toFun := Subtype.val
  map_rel' := fun h => h.1

/-- The actual disjoint bottom-to-slit walks give the three ordered-cut
separation statements on the whole finite reference graph. No planar
separation or induced-boundary comparison is assumed. -/
theorem orderedCutPair_of_slit_crosscuts
    (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y)
    {a b u v : Vertex M x}
    (p : (graph M x y).Walk a u) (q : (graph M x y).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1)
    (hu : u.val.1 = x-1) (huy : y ≤ u.val.2) (hv : v.val = (x,y))
    (hp : ∀ w ∈ p.support,
      x-(M:ℤ) < w.val.1 ∧ w.val.1 < x+(M:ℤ)-1 ∧
      0 ≤ w.val.2 ∧ w.val.2 < (M:ℤ))
    (hq : ∀ w ∈ q.support,
      x ≤ w.val.1 ∧ w.val.1 < x+(M:ℤ)-1 ∧
      0 ≤ w.val.2 ∧ w.val.2 < (M:ℤ))
    (hdis : ∀ w ∈ p.support, w ∉ q.support) :
    OrderedCutPair (graph M x y) (alpha M x) (beta M x y)
      {w | w ∈ p.support} {w | w ∈ q.support} := by
  classical
  let P := (p.map (toLattice M x y)).copy
    (show a.val = (a.val.1,0) from Prod.ext rfl ha)
    (show u.val = (x-1,u.val.2) from Prod.ext hu rfl)
  let Q := (q.map (toLattice M x y)).copy
    (show b.val = (b.val.1,0) from Prod.ext rfl hb) hv
  have hsP : P.support = p.support.map Subtype.val := by
    calc
      P.support = (p.map (toLattice M x y)).support := SimpleGraph.Walk.support_copy _ _ _
      _ = p.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
  have hsQ : Q.support = q.support.map Subtype.val := by
    calc
      Q.support = (q.map (toLattice M x y)).support := SimpleGraph.Walk.support_copy _ _ _
      _ = q.support.map Subtype.val := SimpleGraph.Walk.support_map _ _
  have hP : ∀ w ∈ P.support,
      x-(M:ℤ) < w.1 ∧ w.1 < x+(M:ℤ)-1 ∧ 0 ≤ w.2 ∧ w.2 < (M:ℤ) := by
    intro w hw
    rw [hsP] at hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    exact hp z hz
  have hQ : ∀ w ∈ Q.support,
      x ≤ w.1 ∧ w.1 < x+(M:ℤ)-1 ∧ 0 ≤ w.2 ∧ w.2 < (M:ℤ) := by
    intro w hw
    rw [hsQ] at hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    exact hq z hz
  have hPm (w : Vertex M x) : w.val ∈ P.support ↔ w ∈ p.support := by
    rw [hsP,List.mem_map]
    constructor
    · rintro ⟨z,hz,hzw⟩
      exact Subtype.ext hzw ▸ hz
    · intro hw
      exact ⟨w,hw,rfl⟩
  have hQm (w : Vertex M x) : w.val ∈ Q.support ↔ w ∈ q.support := by
    rw [hsQ,List.mem_map]
    constructor
    · rintro ⟨z,hz,hzw⟩
      exact Subtype.ext hzw ▸ hz
    · intro hw
      exact ⟨w,hw,rfl⟩
  obtain ⟨CL,hCL,hCLalpha,hCLbottom⟩ := exists_left_slit_barrier M x y a.val.1 u.val.2
    hM hy huy hxa P hP
  obtain ⟨CR,hCR,hCRalpha,hCRbeta,hCRbottom⟩ := exists_right_slit_barrier M x y b.val.1
    hM hy (by omega) Q hQ
  have hCLq (z : Vertex M x) (hz : z ∈ q.support) : rayIndex z.val CL = 0 := by
    have hidx := rayIndex_eq_of_slitBarrier M x y a.val.1 hM P CL hCL
      (q.takeUntil z hz) (by
        intro w hw hwp
        exact hdis w ((hPm w).mp hwp) (q.support_takeUntil_subset_support hz hw))
    have hb0 : rayIndex b.val CL = 0 := by
      have he : b.val = (b.val.1,0) := Prod.ext rfl hb
      rw [he]
      exact hCLbottom _ hab
    exact hidx.symm.trans hb0
  have hCRp (z : Vertex M x) (hz : z ∈ p.support) : rayIndex z.val CR = 0 := by
    have hidx := rayIndex_eq_of_slitBarrier M x y b.val.1 hM Q CR hCR
      (p.takeUntil z hz) (by
        intro w hw hwq
        exact hdis w (p.support_takeUntil_subset_support hz hw) ((hQm w).mp hwq))
    have ha0 : rayIndex a.val CR = 0 := by
      have he : a.val = (a.val.1,0) := Prod.ext rfl ha
      rw [he]
      exact hCRbottom _ hab
    exact hidx.symm.trans ha0
  have hleft : ∀ l ∈ alpha M x, ∀ c ∈ q.support,
      ∀ r : (graph M x y).Walk l c, ∃ z ∈ r.support, z ∈ p.support := by
    intro l hl c hc r
    by_contra hn
    have hidx := rayIndex_eq_of_slitBarrier M x y a.val.1 hM P CL hCL r (by
      intro w hw hwp
      exact hn ⟨w,hw,(hPm w).mp hwp⟩)
    rw [hCLalpha l hl,hCLq c hc] at hidx
    norm_num at hidx
  have hright : ∀ c ∈ p.support, ∀ r ∈ beta M x y,
      ∀ s : (graph M x y).Walk c r, ∃ z ∈ s.support, z ∈ q.support := by
    intro c hc r hr s
    by_contra hn
    have hrq : r.val ∉ Q.support := by
      intro h
      exact hn ⟨r,s.end_mem_support,(hQm r).mp h⟩
    have hidx := rayIndex_eq_of_slitBarrier M x y b.val.1 hM Q CR hCR s (by
      intro w hw hwq
      exact hn ⟨w,hw,(hQm w).mp hwq⟩)
    rw [hCRp c hc,hCRbeta r hr hrq] at hidx
    norm_num at hidx
  refine ⟨Set.disjoint_left.mpr hdis,?_,hleft,hright⟩
  intro l hl r hr s
  have hhit : ∃ z ∈ s.support, z ∈ q.support := by
    by_contra hn
    have hrq : r.val ∉ Q.support := by
      intro h
      exact hn ⟨r,s.end_mem_support,(hQm r).mp h⟩
    have hidx := rayIndex_eq_of_slitBarrier M x y b.val.1 hM Q CR hCR s (by
      intro w hw hwq
      exact hn ⟨w,hw,(hQm w).mp hwq⟩)
    rw [hCRalpha l hl,hCRbeta r hr hrq] at hidx
    norm_num at hidx
  obtain ⟨z,hzs,hzq⟩ := hhit
  obtain ⟨w,hw,hwP⟩ := hleft l hl z hzq (s.takeUntil z hzs)
  exact ⟨w,s.support_takeUntil_subset_support hzs hw,hwP⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
