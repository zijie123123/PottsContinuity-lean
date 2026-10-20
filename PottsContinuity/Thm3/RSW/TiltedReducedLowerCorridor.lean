module

public import PottsContinuity.Thm3.RSW.TiltedReducedLowerEdges

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm3.Prop4
noncomputable section

private theorem host_dual_pair (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    Sym2.map Subtype.val (rectangleDualEdgeEquiv a w h e).val =
      (dualBondOfPrimal (rectanglePrimalEdgeBond a w h e)).toSym2 := by
  exact rectangleSubgraphDualEdgeEmbedding_crossingBond
    (G := rectangleGraph a w h) le_rfl e

/-- Each downward dual step in the lower staircase corridor is forced open. -/
theorem tiltedReducedLowerCorridor_step
    (N M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (x j : ℤ) (hx : -(M:ℤ) ≤ x ∧ x < M)
    (hj : -((M+N+2:ℕ):ℤ) ≤ j ∧ j ≤ (M+N+2:ℕ))
    (hlower : (j:ℝ)-t*x < if 0<t then t else 0)
    (u v : RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hu : u.val = (x,j-1)) (hv : v.val = (x,j)) :
    (openGraph (rectangleDualGraph (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2)))
      (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
        (tiltedReducedHostRemovedState N M t ht)).val).Adj u v := by
  classical
  let a : RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) :=
    ⟨(x,j),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  let b : RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) :=
    ⟨(x+1,j),by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  have hab : (tiltedReducedHost N M).Adj a b := by
    change PD.FK.squareLattice.Adj (x,j) (x+1,j)
    rw [PD.FK.squareLattice_adj_iff]; omega
  let e : (tiltedReducedHost N M).edgeSet := ⟨s(a,b),hab⟩
  have hnorm : rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2)) e = ⟨(x,j),.horizontal⟩ := by
    apply wholePlaneBondEdgeEquiv.injective
    have hp := wholePlaneBondEdgeEquiv.apply_symm_apply
      (rectanglePrimalEdgeToSquareEdge (-(M:ℤ),-((M+N+2:ℕ):ℤ))
        (2*M) (2*(M+N+2)) e)
    exact hp
  let d := rectangleDualEdgeEquiv (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) e
  have hpair : d.val = s(u,v) := by
    apply Sym2.map.injective Subtype.val_injective
    rw [host_dual_pair,hnorm]
    simp only [Sym2.map_mk,hu,hv,dualBondOfPrimal,LatticeBond.toSym2,
      LatticeBond.source,LatticeBond.target]
    congr 2; omega
  have hopen : d ∈ (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
      (tiltedReducedHostRemovedState N M t ht)).val := by
    by_cases hp : 0<t
    · apply tiltedReducedHost_below_dual_open N M hN t ht e b (by simp [e])
      dsimp [b,tiltedHeight]
      simp only [hp,ite_true] at hlower
      push_cast
      linarith
    · apply tiltedReducedHost_below_dual_open N M hN t ht e a (by simp [e])
      simpa only [a,tiltedHeight,hp,ite_false] using hlower
  rw [openGraph_adj]
  exact ⟨d,hopen,hpair⟩

/-- Every lower-corridor interior face reaches a bottom exterior port. -/
theorem tiltedReducedLowerCorridor_reachable_bottom
    (N M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (u : RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hu : u.val ∈ rectangleDualInterior (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2)))
    (hlower : tiltedHeight t u.val < if 0<t then t else 0) :
    ∃ v : RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)),
      v.val ∈ rectangleDualBoundary (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) ∧
      (openGraph (rectangleDualGraph (-(M:ℤ),-((M+N+2:ℕ):ℤ))
        (2*M) (2*(M+N+2)))
        (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
          (tiltedReducedHostRemovedState N M t ht)).val).Reachable u v := by
  classical
  have hb := (Finset.mem_filter.mp hu).2
  change -(M:ℤ) ≤ u.val.1 ∧ u.val.1 < -(M:ℤ)+(2*M:ℕ) ∧
    -((M+N+2:ℕ):ℤ) ≤ u.val.2 ∧
    u.val.2 < -((M+N+2:ℕ):ℤ)+(2*(M+N+2):ℕ) at hb
  let a : LatticeVertex := (u.val.1,-((M+N+2:ℕ):ℤ)-1)
  let d := (u.val.2-a.2).toNat
  have hd : (d:ℤ) = u.val.2-a.2 := Int.toNat_of_nonneg (by dsimp [a]; omega)
  have ha : a.2 = -((M+N+2:ℕ):ℤ)-1 := rfl
  have hsub (z : RectangleVertex a 0 d) : z.val ∈
      rectangleDualExpanded (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) := by
    have hz := (mem_latticeRectangle a z.val 0 d).mp z.property
    unfold rectangleDualExpanded
    rw [mem_latticeRectangle]
    dsimp [a] at hz
    constructor <;> constructor <;> omega
  let f : RectangleVertex a 0 d →
      RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) :=
    fun z => ⟨z.val,hsub z⟩
  have hlow (z : RectangleVertex a 0 d) :
      tiltedHeight t z.val < if 0<t then t else 0 := by
    have hz := (mem_latticeRectangle a z.val 0 d).mp z.property
    have hx : z.val.1 = u.val.1 := by dsimp [a] at hz; omega
    have hy : z.val.2 ≤ u.val.2 := by omega
    have hyR : (z.val.2:ℝ) ≤ u.val.2 := by exact_mod_cast hy
    dsimp [tiltedHeight] at hlower ⊢
    rw [hx]
    linarith
  let φ : rectangleGraph a 0 d →g
      openGraph (rectangleDualGraph (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
        (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
          (tiltedReducedHostRemovedState N M t ht)).val := by
    refine ⟨f,?_⟩
    intro z w hzw
    have hz := (mem_latticeRectangle a z.val 0 d).mp z.property
    have hw := (mem_latticeRectangle a w.val 0 d).mp w.property
    have hzx : z.val.1 = u.val.1 := by dsimp [a] at hz; omega
    have hwx : w.val.1 = u.val.1 := by dsimp [a] at hw; omega
    have hadj : PD.FK.squareLattice.Adj z.val w.val := hzw
    rw [PD.FK.squareLattice_adj_iff] at hadj
    have hstep : z.val.2+1 = w.val.2 ∨ w.val.2+1 = z.val.2 := by omega
    rcases hstep with hs | hs
    · apply tiltedReducedLowerCorridor_step N M hN t ht u.val.1 w.val.2
        (by constructor <;> omega) (by dsimp [a] at hz hw; constructor <;> omega)
        (by simpa only [tiltedHeight,hwx] using hlow w) (f z) (f w)
      · change z.val = (u.val.1,w.val.2-1)
        exact Prod.ext hzx (by omega)
      · change w.val = (u.val.1,w.val.2)
        exact Prod.ext hwx rfl
    · apply SimpleGraph.Adj.symm
      apply tiltedReducedLowerCorridor_step N M hN t ht u.val.1 z.val.2
        (by constructor <;> omega) (by dsimp [a] at hz hw; constructor <;> omega)
        (by simpa only [tiltedHeight,hzx] using hlow z) (f w) (f z)
      · change w.val = (u.val.1,z.val.2-1)
        exact Prod.ext hwx (by omega)
      · change z.val = (u.val.1,z.val.2)
        exact Prod.ext hzx rfl
  let top : RectangleVertex a 0 d := ⟨u.val,by
    rw [mem_latticeRectangle]; dsimp [a]; constructor <;> constructor <;> omega⟩
  let bottom : RectangleVertex a 0 d := ⟨a,by
    rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
  refine ⟨f bottom,?_,?_⟩
  · rw [rectangleDualBoundary,Finset.mem_filter]
    refine ⟨hsub bottom,?_⟩
    intro hin
    have hi := (Finset.mem_filter.mp hin).2
    have hiY := hi.2.2.1
    change -((M+N+2:ℕ):ℤ) ≤ a.2 at hiY
    omega
  · have hr := FKC.FiniteFK.rectangleGraph_reachable_all a 0 d top bottom
    rw [← rectangleGraph_eq_FKC] at hr
    exact hr.map φ

/-- The induced genuine dual boundary wires every intrinsic-top core vertex. -/
theorem tiltedReducedCore_top_partition_le
    (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hM : L+N+3 ≤ M) :
    (tiltedWindowBoundary N L t 0).partition ≤
      (isolatedExtensionPullbackBoundary (tiltedReducedCoreDualEmbedding N L M t hM)
        (tiltedReducedFiniteDualBoundary N M t ht)).partition := by
  intro x y hxy
  change x=y ∨ x ∈ tiltedWindowWiredVertices N L t 0 ∧
    y ∈ tiltedWindowWiredVertices N L t 0 at hxy
  rcases hxy with rfl | ⟨hx,hy⟩
  · exact (tiltedReducedFiniteDualBoundary N M t ht).partition.refl _
  have hxtop : tiltedTop N t x.val := by simpa [tiltedWindowWiredVertices] using hx
  have hytop : tiltedTop N t y.val := by simpa [tiltedWindowWiredVertices] using hy
  obtain ⟨u,hu,hxu⟩ := tiltedReducedLowerCorridor_reachable_bottom N M hN t ht
    (tiltedReducedCoreDualEmbedding N L M t hM x)
    (tiltedReducedCoreDualEmbedding_interior N L M t hM x)
    (tiltedReducedCore_top_below N L M t ht hM x hxtop)
  obtain ⟨v,hv,hyv⟩ := tiltedReducedLowerCorridor_reachable_bottom N M hN t ht
    (tiltedReducedCoreDualEmbedding N L M t hM y)
    (tiltedReducedCoreDualEmbedding_interior N L M t hM y)
    (tiltedReducedCore_top_below N L M t ht hM y hytop)
  change (componentSetoid _ (rectangleDualBoundaryCondition _ _ _) _).r _ _
  let S := (tiltedReducedFiniteDualBoundary N M t ht).partition
  exact S.trans (actualConnected_component _ _ _ hxu)
    (S.trans (boundary_component _ _ _ (Or.inr ⟨hu,hv⟩))
      (S.symm (actualConnected_component _ _ _ hyv)))

end
end PottsContinuity.RSW
