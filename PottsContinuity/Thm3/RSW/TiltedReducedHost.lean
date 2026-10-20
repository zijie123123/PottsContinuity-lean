module

public import PottsContinuity.Thm3.RSW.TiltedUpperCorridor

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK Thm3.Prop4 DualityExt
noncomputable section

/-- Rectangular host with a full horizontal cap above the digital top. -/
abbrev tiltedReducedHost (N M : ℕ) :=
  rectangleGraph (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2))

/-- Physical inclusion of every original finite strip vertex in the taller host. -/
def tiltedReducedHostEmbedding (N M : ℕ) (t : ℝ) :
    (tiltedWindow N M t : Set (ℤ × ℤ)) ↪
      RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) where
  toFun z := ⟨z.val,by
    have hb := (Foundations.mem_box_iff_abs_le M z.val).mp
      ((mem_tiltedWindow N M t z.val).mp z.property).1
    have hx := abs_le.mp hb.1
    have hy := abs_le.mp hb.2
    rw [mem_latticeRectangle]
    push_cast
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2)) => z.val) h

/-- The reduced original graph embeds without adding or relabeling any bond. -/
theorem tiltedReducedHost_map_le (N M : ℕ) (t : ℝ) :
    (tiltedWindowReducedGraph N M t).map (tiltedReducedHostEmbedding N M t) ≤
      tiltedReducedHost N M := by
  intro u v huv
  obtain ⟨x,y,hxy,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  exact edgeRestriction_le (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))
    (tiltedWindowTopTopEdges N M t) hxy

/-- Every point of the host cap lies strictly in the open upper corridor. -/
theorem tiltedReducedHost_cap_upper (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (z : RectangleVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)))
    (hz : z.val.2 = -((M+N+2:ℕ):ℤ)+(2*(M+N+2):ℕ)) :
    (N : ℝ) < tiltedHeight t z.val+1 := by
  have hb := (mem_latticeRectangle _ z.val (2*M) (2*(M+N+2))).mp z.property
  have hxZ : |z.val.1| ≤ (M:ℤ) := by rw [abs_le]; push_cast at hb; omega
  have hx : |(z.val.1:ℝ)| ≤ (M:ℝ) := by exact_mod_cast hxZ
  have htx : t*(z.val.1:ℝ) ≤ (M:ℝ) :=
    (le_abs_self _).trans ((abs_mul t _).le.trans
      ((mul_le_mul_of_nonneg_right (abs_le.mpr ht) (abs_nonneg _)).trans (by simpa using hx)))
  have hy : (z.val.2:ℝ) = (M:ℝ)+N+2 := by
    have hZ : z.val.2 = ((M+N+2:ℕ):ℤ) := by omega
    exact_mod_cast hZ
  dsimp [tiltedHeight]
  linarith

/-- The open upper corridor never samples a retained strip bond. -/
theorem tiltedReducedHost_upperState_subset_removed (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    tiltedUpperCorridorState (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) N t ⊆
      subgraphRemovedEdges ((tiltedWindowReducedGraph N M t).map
        (tiltedReducedHostEmbedding N M t)) (tiltedReducedHost N M) := by
  classical
  intro e he
  rw [mem_subgraphRemovedEdges]
  intro hmap
  rcases e with ⟨e,hee⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨x,y,hxy,hxu,hyv⟩ := (SimpleGraph.map_adj _ _ _ _).mp
      (((tiltedWindowReducedGraph N M t).map _).mem_edgeSet.mp hmap)
    subst u
    subst v
    simp only [tiltedUpperCorridorState,Finset.mem_filter,Finset.mem_univ,true_and] at he
    have hx : tiltedTop N t x.val :=
      (tiltedTop_iff_height N ht x.val).mpr (he (tiltedReducedHostEmbedding N M t x) (by simp))
    have hy : tiltedTop N t y.val :=
      (tiltedTop_iff_height N ht y.val).mpr (he (tiltedReducedHostEmbedding N M t y) (by simp))
    have habsent := ((tiltedWindowReducedGraph N M t).mem_edgeSet.mpr hxy)
    change s(x,y) ∈ (edgeRestriction
      (squareLattice.induce (tiltedWindow N M t : Set (ℤ × ℤ)))
      (tiltedWindowTopTopEdges N M t)).edgeSet at habsent
    rw [edgeRestriction_edgeSet] at habsent
    apply habsent.2
    refine ⟨⟨s(x,y),habsent.1⟩,?_,rfl⟩
    simp only [Finset.mem_coe,tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    intro z hz
    rcases (Sym2.mem_iff').mp hz with rfl | rfl
    · exact hx
    · exact hy

/-- Literal host removed state: upper corridor open, every other omitted bond closed. -/
def tiltedReducedHostRemovedState (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    RemovedConfiguration (tiltedReducedHost N M)
      (subgraphRemovedEdges ((tiltedWindowReducedGraph N M t).map
        (tiltedReducedHostEmbedding N M t)) (tiltedReducedHost N M)) :=
  ⟨_,tiltedReducedHost_upperState_subset_removed N M t ht⟩

/-- The actual upper removed state realizes precisely the source's intrinsic
wired-top partition, without any finite source partition premise. -/
theorem tiltedReducedHost_source_partition (N M : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (tiltedWindowBoundary N M t 0).partition =
      (isolatedExtensionPullbackBoundary (tiltedReducedHostEmbedding N M t)
        (frozenBoundary (BoundaryCondition.free ∅)
          (tiltedReducedHostRemovedState N M t ht).val)).partition := by
  have hc := tiltedUpperCorridor_partition
    (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) N t
    (tiltedReducedHost_cap_upper N M t ht)
  change _ = Setoid.comap (tiltedReducedHostEmbedding N M t)
    (frozenBoundary (BoundaryCondition.free ∅)
      (tiltedUpperCorridorState _ _ _ N t)).partition
  rw [hc]
  apply Setoid.ext
  intro u v
  change (u=v ∨ u ∈ tiltedWindowWiredVertices N M t 0 ∧
    v ∈ tiltedWindowWiredVertices N M t 0) ↔
      tiltedReducedHostEmbedding N M t u = tiltedReducedHostEmbedding N M t v ∨
        ((N:ℝ)<tiltedHeight t u.val+1 ∧ (N:ℝ)<tiltedHeight t v.val+1)
  have heq : tiltedReducedHostEmbedding N M t u = tiltedReducedHostEmbedding N M t v ↔ u=v :=
    (tiltedReducedHostEmbedding N M t).injective.eq_iff
  rw [heq,← tiltedTop_iff_height N ht u.val,← tiltedTop_iff_height N ht v.val]
  simp [tiltedWindowWiredVertices]

end
end PottsContinuity.RSW
