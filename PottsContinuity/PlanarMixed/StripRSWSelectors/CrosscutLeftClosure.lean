module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.LeftSlitClosure
public import PottsContinuity.PlanarMixed.StripRSWSelectors.PrefixBarrierIndices

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.Duality PlanarMixed.FiniteSlit
noncomputable section
/-- The left closure of actual slit crosscuts assigns index one to alpha
and index zero to beta. The beta computation uses its whole internal arc,
including the slit ray and the exterior top/right sides. -/
theorem crosscut_left_barrier_indices_with_support (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M:ℤ)) (D : CrosscutData M x y) :
    let P := (D.first.map (toLattice M x y)).copy
      (show D.firstStart.val = (D.firstStart.val.1,0) from Prod.ext rfl D.first_bottom)
      (show D.firstEnd.val = (x-1,D.firstEnd.val.2) from Prod.ext D.first_end_column rfl)
    ∃ L : squareLattice.Walk (D.firstStart.val.1,0) (D.firstStart.val.1,0),
      (∀ e ∈ L.edges, e ∈ slitBarrierEdges M x y D.firstStart.val.1 P) ∧
      (∀ v : Vertex M x, v ∈ alpha M x → rayIndex v.val L=1) ∧
      (∀ v : Vertex M x, v ∈ beta M x y → rayIndex v.val L=0) ∧
      (∀ w ∈ L.support,
        x-(M:ℤ) ≤ w.1 → w.1 ≤ x+(M:ℤ)-1 → 0 ≤ w.2 → w.2 ≤ (M:ℤ) →
        w ∈ P.support ∨ (w.1=x-1 ∧ D.firstEnd.val.2 ≤ w.2)) := by
  classical
  dsimp only
  let P := (D.first.map (toLattice M x y)).copy
    (show D.firstStart.val = (D.firstStart.val.1,0) from Prod.ext rfl D.first_bottom)
      (show D.firstEnd.val = (x-1,D.firstEnd.val.2) from Prod.ext D.first_end_column rfl)
  have hPs : P.support=D.first.support.map Subtype.val := by
    exact (SimpleGraph.Walk.support_copy _ _ _).trans (SimpleGraph.Walk.support_map _ _)
  have hPm (z : Vertex M x) : z.val ∈ P.support ↔ z ∈ D.first.support := by
    rw [hPs,List.mem_map]
    exact ⟨fun ⟨a,ha,he⟩ => (Subtype.ext he : a=z) ▸ ha,fun hz => ⟨z,hz,rfl⟩⟩
  have hPb : ∀ z ∈ P.support,
      x-(M:ℤ)<z.1 ∧ z.1<x+(M:ℤ)-1 ∧ 0≤z.2 ∧ z.2<(M:ℤ) := by
    intro z hz
    rw [hPs] at hz
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
    exact D.first_bounds v hv
  obtain ⟨L,hL,hLa,hLb,hsupport⟩ := exists_left_slit_barrier_with_support M x y D.firstStart.val.1 D.firstEnd.val.2
    hM hy D.first_end_height D.first_start_right P hPb
  have hQindex : rayIndex D.secondEnd.val L=0 := by
    have hidx := rayIndex_eq_of_slitBarrier M x y D.firstStart.val.1 hM P L hL D.second (by
      intro z hz hzp
      exact D.disjoint z ((hPm z).mp hzp) hz)
    have he : D.secondStart.val=(D.secondStart.val.1,0) := Prod.ext rfl D.second_bottom
    rw [he,hLb _ D.starts_order] at hidx
    exact hidx.symm
  refine ⟨L,hL,hLa,?_,hsupport⟩
  intro v hv
  have htip : D.secondEnd ∈ beta M x y :=
    Or.inr (Or.inr (by rw [D.second_end]; exact ⟨rfl,le_rfl⟩))
  obtain ⟨p⟩ := beta_internal_connected M x y hM hy hyM D.secondEnd v htip hv
  have hb := internalArc_walk_beta_support M x y hM hy hyM p htip
  have hidx := rayIndex_eq_of_slitBarrier M x y D.firstStart.val.1 hM P L hL
    (p.mapLe (openGraph_le _ _)) (by
      intro z hz hzp
      exact D.first_support_not_beta hM hy z ((hPm z).mp hzp)
        (hb z (by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hz)))
  exact hidx.symm.trans hQindex


end
end PottsContinuity.PlanarMixed.StripRSWSelectors
