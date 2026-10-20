module

public import PottsContinuity.Thm3.RSW.TiltedReducedFiniteReads

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- Every normalized finite source bond belongs to precisely the announced
reduced infinite-strip carrier, including its boundary bonds. -/
theorem tiltedReducedFiniteSourceBond_retained (N M : ℕ) (t : ℝ)
    (e : (tiltedWindowReducedGraph N M t).edgeSet) :
    (tiltedReducedFiniteSourceBond N M t e).source ∈ tiltedStripVertices N t ∧
    (tiltedReducedFiniteSourceBond N M t e).target ∈ tiltedStripVertices N t ∧
    ¬ (tiltedTop N t (tiltedReducedFiniteSourceBond N M t e).source ∧
       tiltedTop N t (tiltedReducedFiniteSourceBond N M t e).target) := by
  classical
  let b := tiltedReducedFiniteSourceBond N M t e
  have hp : b.toSym2 = Sym2.map (fun z => z.val) e.val :=
    tiltedReducedFiniteSourceBond_pair N M t e
  have hs (z : LatticeVertex) (hz : z ∈ b.toSym2) : z ∈ tiltedStripVertices N t := by
    rw [hp] at hz
    obtain ⟨u,hu,heq⟩ := Sym2.mem_map.mp hz
    rw [← heq]
    exact ((mem_tiltedWindow N M t u.val).mp u.property).2
  refine ⟨hs b.source (by simp [LatticeBond.toSym2]),
    hs b.target (by simp [LatticeBond.toSym2]),?_⟩
  rintro ⟨hbs,hbt⟩
  let G := squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ))
  let R := tiltedWindowTopTopEdges N M t
  let e0 := edgeRestrictionEdgeEquiv G R e
  apply e0.property
  simp only [R,tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  intro z hz
  have hz' : z.val ∈ b.toSym2 := by
    rw [hp]
    exact Sym2.mem_map.mpr ⟨z,hz,rfl⟩
  change z.val ∈ s(b.source,b.target) at hz'
  rcases (Sym2.mem_iff').mp hz' with hz' | hz'
  · exact hz' ▸ hbs
  · exact hz' ▸ hbt

/-- On actual finite dual edges the crossed endpoint map stays within the
original tilted strip; no exterior endpoint is clipped or filled. -/
theorem tiltedReducedFiniteDualEdge_endpoints_mem (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (e : (tiltedWindowReducedGraph N M t).edgeSet)
    (z : RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hz : z ∈ (tiltedReducedFiniteDualEdge N M t e).val) :
    tiltedStripReducedDualVertex N t z.val ∈ tiltedStripVertices N t := by
  have hb := tiltedReducedFiniteSourceBond_retained N M t e
  let b : tiltedStripReducedCarrier N t :=
    ⟨⟨tiltedReducedFiniteSourceBond N M t e,hb.1,hb.2.1⟩,hb.2.2⟩
  have hcross := tiltedStripReducedCrossedBond_mem N t ht b
  have hzmap : tiltedStripReducedDualVertex N t z.val ∈
      (tiltedStripReducedCrossedBond N t (tiltedReducedFiniteSourceBond N M t e)).toSym2 := by
    rw [← tiltedReducedFiniteDualEdge_crossed_pair]
    exact Sym2.mem_map.mpr ⟨z,hz,rfl⟩
  rcases (Sym2.mem_iff').mp hzmap with hzmap | hzmap
  · exact hzmap ▸ hcross.1
  · exact hzmap ▸ hcross.2.1

/-- Every retained dual edge is the actual crossed dual of a unique native
reduced source edge. -/
theorem tiltedReducedFiniteDualEdge_surjective (N M : ℕ) (t : ℝ) :
    Function.Surjective (tiltedReducedFiniteDualEdge N M t) :=
  (tiltedReducedFiniteEdgeEquiv N M t).surjective

end
end PottsContinuity.RSW
