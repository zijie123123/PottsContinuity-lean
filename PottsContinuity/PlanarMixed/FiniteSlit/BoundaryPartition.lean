module

public import PottsContinuity.PlanarMixed.FiniteSlit.BoundaryPaths
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition

/-! Separate outer-arc wiring realized by explicit auxiliary OPEN bonds.
The induced partition is proved on the full rectangular carrier. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 DualityExt
noncomputable section
local instance finiteSlitBoundaryPartitionEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Every pair of alpha vertices is joined by actual internal arc bonds. -/
theorem alpha_internal_connected (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y)
    (u v : Vertex M x) (hu : u ∈ alpha M x) (hv : v ∈ alpha M x) :
    ActualConnected (graph M x y) (internalEdges M x y) u v := by
  let p : Vertex M x := ⟨(x-(M : ℤ),(M : ℤ)),by
    apply (mem_rectangle_iff M x (by omega) _).mpr
    simp only
    omega⟩
  let b : Vertex M x := ⟨(x-(M : ℤ),0),by
    apply (mem_rectangle_iff M x (by omega) _).mpr
    simp only
    omega⟩
  have hto (z : Vertex M x) (hz : z ∈ alpha M x) :
      ActualConnected (graph M x y) (internalEdges M x y) z p := by
    rcases hz with hz | hz | hz
    · have hzb := horizontal_internal_connected M x y hM hy z b
        (by exact hz.1) (Or.inl ⟨hz.1,hz.2,by dsimp [b]; omega⟩)
      exact hzb.trans (leftSide_internal_connected M x y hM b p rfl rfl)
    · exact leftSide_internal_connected M x y hM z p hz rfl
    · exact horizontal_internal_connected M x y hM hy z p hz.1
        (Or.inr (Or.inl ⟨hz.1,hz.2,by dsimp [p]; omega⟩))
  exact (hto u hu).trans (hto v hv).symm

/-- Every pair of beta vertices is joined by actual internal arc bonds,
through the right top corner and the top of the K ray. -/
theorem beta_internal_connected (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (hy : 0 < y) (hyM : y < (M : ℤ))
    (u v : Vertex M x) (hu : u ∈ beta M x y) (hv : v ∈ beta M x y) :
    ActualConnected (graph M x y) (internalEdges M x y) u v := by
  let p : Vertex M x := ⟨(x+(M : ℤ)-1,(M : ℤ)),by
    apply (mem_rectangle_iff M x (by omega) _).mpr
    simp only
    omega⟩
  let k : Vertex M x := ⟨(x,(M : ℤ)),by
    apply (mem_rectangle_iff M x (by omega) _).mpr
    simp only
    omega⟩
  have hto (z : Vertex M x) (hz : z ∈ beta M x y) :
      ActualConnected (graph M x y) (internalEdges M x y) z p := by
    rcases hz with hz | hz | hz
    · exact vertical_internal_connected M x y hM z p hz (Or.inr (Or.inl hz))
    · exact horizontal_internal_connected M x y hM hy z p hz.1
        (Or.inr (Or.inr ⟨hz.1,hz.2,by dsimp [p]; omega⟩))
    · have hzk := vertical_internal_connected M x y hM z k hz.1
        (Or.inr (Or.inr ⟨hz.1,hz.2,hyM.le⟩))
      exact hzk.trans (horizontal_internal_connected M x y hM hy k p rfl
        (Or.inr (Or.inr ⟨rfl,le_rfl,by dsimp [p]; omega⟩)))
  exact (hto u hu).trans (hto v hv).symm

/-- Actual rectangular auxiliary state: internal alpha and beta bonds OPEN. -/
def rectangleArcBonds (M : ℕ) (x y : ℤ) :
    Configuration (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) :=
  internalBonds (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) (alpha M x) ∪
    internalBonds (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) (beta M x y)

/-- Physical paths in the slit auxiliary state persist in the rectangle. -/
theorem internalEdges_openGraph_le_rectangle (M : ℕ) (x y : ℤ) :
    openGraph (graph M x y) (internalEdges M x y) ≤
      openGraph (rectangleGraph (x-(M : ℤ),0) (2*M-1) M) (rectangleArcBonds M x y) := by
  intro u v huv
  obtain ⟨e,he,heuv⟩ := (openGraph_adj _ _ _ _).mp huv
  let e' : (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet :=
    ⟨e.val,SimpleGraph.edgeSet_mono (graph_le_rectangle M x y) e.property⟩
  have he' : e' ∈ rectangleArcBonds M x y := by
    simpa [internalEdges,rectangleArcBonds,internalBonds,e'] using he
  exact (openGraph_adj _ _ _ _).mpr ⟨e',he',heuv⟩

/-- Free rectangular boundary conditioned on this auxiliary state induces
EXACTLY the two separate outer classes, including every original vertex. -/
theorem rectangleArcBonds_frozen_partition (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) :
    (frozenBoundary (BoundaryCondition.free ∅) (rectangleArcBonds M x y)).partition =
      (boundary M x y hM hy hyM).partition := by
  apply frozenBoundary_partition_eq_twoBlock_of_class_connected
    (BoundaryCondition.free ∅) (rectangleArcBonds M x y)
    (alpha M x) (beta M x y) (alpha_disjoint_beta M x y hM hy hyM)
  · intro e he
    simpa only [rectangleArcBonds,internalBonds,Finset.mem_union,Finset.mem_filter,
      Finset.mem_univ,true_and] using he
  · exact bot_le
  · intro u v hu hv
    apply actualConnected_component
    exact (alpha_internal_connected M x y hM hy u v hu hv).mono
      (internalEdges_openGraph_le_rectangle M x y)
  · intro u v hu hv
    apply actualConnected_component
    exact (beta_internal_connected M x y hM hy hyM u v hu hv).mono
      (internalEdges_openGraph_le_rectangle M x y)

end
end PottsContinuity.PlanarMixed.FiniteSlit
