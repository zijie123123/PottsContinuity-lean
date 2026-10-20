module

public import PottsContinuity.Thm3.RSW.TiltedReducedActiveLaw
public import PottsContinuity.Thm3.RSW.TiltedReducedCoreClosure

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt Thm3.Prop4
noncomputable section

/-- A host edge with a vertex below the strip is deleted and fixed closed. -/
theorem tiltedReducedHost_below_edge
    (N M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (e : (tiltedReducedHost N M).edgeSet)
    (z : RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hz : z ∈ e.val) (hbelow : tiltedHeight t z.val < 0) :
    e ∈ subgraphRemovedEdges ((tiltedWindowReducedGraph N M t).map
        (tiltedReducedHostEmbedding N M t)) (tiltedReducedHost N M) ∧
      e ∉ (tiltedReducedHostRemovedState N M t ht).val := by
  classical
  constructor
  · rw [mem_subgraphRemovedEdges]
    intro he
    rcases e with ⟨e,hehost⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨x,y,hxy,hxu,hyv⟩ := (SimpleGraph.map_adj _ _ _ _).mp he
      dsimp only at hxu hyv
      subst u
      subst v
      rcases (Sym2.mem_iff').mp hz with rfl | rfl
      · have hs := ((mem_tiltedWindow N M t x.val).mp x.property).2.1
        exact (not_lt_of_ge hs) hbelow
      · have hs := ((mem_tiltedWindow N M t y.val).mp y.property).2.1
        exact (not_lt_of_ge hs) hbelow
  · intro he
    have hh : ∀ u ∈ e.val, (N:ℝ) < tiltedHeight t u.val+1 := by
      simpa only [tiltedReducedHostRemovedState,tiltedUpperCorridorState,
        Finset.mem_filter,Finset.mem_univ,true_and] using he
    have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
    have := hh z hz
    linarith

/-- The genuine dual of every below-strip host edge is forced open. -/
theorem tiltedReducedHost_below_dual_open
    (N M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (e : (tiltedReducedHost N M).edgeSet)
    (z : RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hz : z ∈ e.val) (hbelow : tiltedHeight t z.val < 0) :
    rectangleDualEdgeEquiv (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) e ∈
      (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
        (tiltedReducedHostRemovedState N M t ht)).val := by
  classical
  have he := tiltedReducedHost_below_edge N M hN t ht e z hz hbelow
  simp only [rectangleSubgraphDualOpenRemovedState, Finset.mem_sdiff]
  constructor
  · exact Finset.mem_map.mpr ⟨e,he.1,rfl⟩
  · intro hb
    obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp hb
    have hfe' : f = e := (rectangleDualEdgeEquiv _ _ _).injective hfe
    exact he.2 (hfe' ▸ hf)

/-- The reflected image of an intrinsic top vertex lies below the
staircase level of the lower exterior dual corridor. -/
theorem tiltedReducedCore_top_below (N L M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (hM : L+N+3 ≤ M)
    (z : (tiltedWindow N L t : Set (ℤ × ℤ)))
    (hz : tiltedTop N t z.val) :
    tiltedHeight t (tiltedReducedCoreDualEmbedding N L M t hM z).val <
      (if 0 < t then t else 0) := by
  have hh := (tiltedTop_iff_height N ht z.val).mp hz
  change tiltedHeight t (tiltedStripReducedDualVertex N t z.val) < _
  dsimp [tiltedStripReducedDualVertex,tiltedHeight] at hh ⊢
  split_ifs <;> push_cast <;> nlinarith

end
end PottsContinuity.RSW
