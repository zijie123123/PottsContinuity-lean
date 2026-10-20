module

public import PottsContinuity.Thm3.RSW.TiltedReducedCoreGraph

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt Thm3.Prop4
noncomputable section

private theorem reduced_dual_vertex_adj (N : ℕ) (t : ℝ) (u v : LatticeVertex)
    (huv : PD.FK.squareLattice.Adj u v) :
    PD.FK.squareLattice.Adj (tiltedStripReducedDualVertex N t u)
      (tiltedStripReducedDualVertex N t v) := by
  rw [PD.FK.squareLattice_adj_iff] at huv ⊢
  dsimp [tiltedStripReducedDualVertex]
  omega

/-- Away from intrinsic top and the artificial core sides, every sampled
finite dual neighbour is another genuine reduced core vertex and edge. -/
theorem tiltedReducedCoreDual_closedInterior (N L M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (x : (tiltedWindow N L t : Set (ℤ × ℤ)))
    (hx : x ∉ tiltedWindowWiredVertices N L t 1)
    (y : RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hxy : (rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)).Adj
      (tiltedReducedCoreDualEmbedding N L M t hM x) y) :
    ∃ z : (tiltedWindow N L t : Set (ℤ × ℤ)),
      tiltedReducedCoreDualEmbedding N L M t hM z = y ∧
        (tiltedWindowReducedGraph N L t).Adj x z := by
  classical
  let D := rectangleSubgraphDualGraph (tiltedReducedHost_map_le N M t)
  let f := tiltedReducedCoreDualEmbedding N L M t hM
  let d : D.edgeSet := ⟨s(f x,y),D.mem_edgeSet.mpr hxy⟩
  obtain ⟨e,he⟩ := tiltedReducedFiniteDualEdge_surjective N M t d
  have hystrip := tiltedReducedFiniteDualEdge_endpoints_mem N M t ht e y
    (by rw [he]; simp [d])
  have hhost := rectangleDualGraph_le_ambient
    (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) (edgeRestriction_le _ _ hxy)
  change PD.FK.squareLattice.Adj (f x).val y.val at hhost
  have hline := reduced_dual_vertex_adj N t _ _ hhost
  rw [tiltedReducedCoreDualEmbedding_replay] at hline
  have hxbox := ((mem_tiltedWindow N L t x.val).mp x.property).1
  have hxnotTop : ¬ tiltedTop N t x.val := fun h => hx (Or.inl h)
  have hybox : tiltedStripReducedDualVertex N t y.val ∈ box L := by
    by_contra hout
    apply hx
    right
    refine ⟨rfl,?_⟩
    rw [Foundations.vertexBoundary_eq_PD]
    exact ⟨hxbox,⟨_,hline,hout⟩⟩
  let z : (tiltedWindow N L t : Set (ℤ × ℤ)) :=
    ⟨tiltedStripReducedDualVertex N t y.val,(mem_tiltedWindow N L t _).mpr ⟨hybox,hystrip⟩⟩
  have hzeq : f z = y := by
    apply Subtype.ext
    change tiltedStripReducedDualVertex N t (tiltedStripReducedDualVertex N t y.val) = y.val
    apply Prod.ext <;> dsimp [tiltedStripReducedDualVertex] <;> omega
  refine ⟨z,hzeq,?_⟩
  let G := squareLattice.induce (tiltedWindow N L t : Set (ℤ × ℤ))
  have hadj : G.Adj x z := hline
  change s(x,z) ∈ (edgeRestriction G (tiltedWindowTopTopEdges N L t)).edgeSet
  rw [edgeRestriction_edgeSet]
  refine ⟨G.mem_edgeSet.mpr hadj,?_⟩
  intro hbad
  obtain ⟨g,hg,hpair⟩ := hbad
  have hxmem : x ∈ g.val := by rw [hpair]; simp
  have htop : ∀ u ∈ g.val, tiltedTop N t u.val := by
    simpa only [tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_coe] using hg
  exact hxnotTop (htop x hxmem)

end
end PottsContinuity.RSW
