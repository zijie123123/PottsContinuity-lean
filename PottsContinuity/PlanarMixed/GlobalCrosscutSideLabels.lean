module

public import PottsContinuity.PlanarMixed.SourceCrosscutComparison
public import PottsContinuity.PlanarMixed.SourceCrosscutShapes
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import PottsContinuity.Thm3.Push.WalkSupportStepPullback
public import PottsContinuity.PlanarTopology.HorizontalWalks

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 PlanarTopology
noncomputable section

/-- An actual horizontal row walk in the full square keeps its coordinate
interval, including at either boundary. -/
theorem originSquare_row_walk (N : ℕ) (u v : RectangleVertex (0,0) N N)
    (hy : u.val.2 = v.val.2) :
    ∃ p : (rectangleGraph (0,0) N N).Walk u v,
      ∀ z ∈ p.support,
        min u.val.1 v.val.1 ≤ z.val.1 ∧ z.val.1 ≤ max u.val.1 v.val.1 ∧ z.val.2 = u.val.2 := by
  obtain ⟨p,hp⟩ := horizontal_walk_between u.val.1 v.val.1 u.val.2
  let P : squareLattice.Walk u.val v.val := p.copy rfl (Prod.ext rfl hy)
  have hb : ∀ z ∈ P.support,
      min u.val.1 v.val.1 ≤ z.1 ∧ z.1 ≤ max u.val.1 v.val.1 ∧ z.2 = u.val.2 := by
    intro z hz
    exact hp z ((SimpleGraph.Walk.support_copy p _ _) ▸ hz)
  have hu := (mem_latticeRectangle (0,0) u.val N N).mp u.property
  have hv := (mem_latticeRectangle (0,0) v.val N N).mp v.property
  let i : RectangleVertex (0,0) N N ↪ LatticeVertex := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨q,hq⟩ := Push.exists_walk_pullback_support_steps i P u v rfl rfl
    (by
      intro z hz
      refine ⟨⟨z,?_⟩,rfl⟩
      rw [mem_latticeRectangle]
      have h := hb z hz
      dsimp at hu hv
      constructor
      · constructor <;> omega
      · constructor <;> omega)
    (by
      intro x y _ _ hxy
      exact (rectangleGraph_adj_iff (0,0) N N x y).mpr hxy)
  exact ⟨q,fun z hz => hb (i z) (hq z hz)⟩

namespace SquareCrosscutData
variable {N : ℕ} (D : SquareCrosscutData N)

/-- Points left of the ENTIRE first trace lie in the left closed region.
No restriction to a single cropped piece of that trace is made. -/
theorem rank_le_one_of_x_le_first (b : ℤ)
    (hfirst : ∀ z ∈ D.first.support, b ≤ z.val.1)
    (v : RectangleVertex (0,0) N N) (hv : v.val.1 ≤ b) : D.rank v ≤ 1 := by
  by_cases ha : v ∈ D.first.support
  · rw [(D.rank_first_iff v).mpr ha]
  have hb := (mem_latticeRectangle (0,0) v.val N N).mp v.property
  let l : RectangleVertex (0,0) N N := ⟨(0,v.val.2),by
    rw [mem_latticeRectangle]
    dsimp at hb ⊢
    exact ⟨⟨by omega,by omega⟩,hb.2⟩⟩
  obtain ⟨p,hp⟩ := originSquare_row_walk N l v rfl
  have hreach : v ∈ cutReachRegion (rectangleGraph (0,0) N N)
      {z | z ∈ D.first.support} (Square.squareLeftArc (0,0) N) := by
    refine ⟨l,rfl,p,?_⟩
    intro z hz hza
    have hr := hp z hz
    have hf := hfirst z hza
    have hv0 : 0 ≤ v.val.1 := by simpa using hb.1.1
    simp only [l,min_eq_left hv0,max_eq_right hv0] at hr
    have heq : z = v := Subtype.ext (Prod.ext (by omega) hr.2.2)
    exact ha (heq ▸ hza)
  change orderedCutRank _ _ _ _ _ D.orderedCuts v ≤ 1
  simp only [orderedCutRank,ite_eq_left hreach]
  omega

/-- Points right of the ENTIRE second trace lie in the right closed region. -/
theorem three_le_rank_of_second_x_le (b : ℤ)
    (hsecond : ∀ z ∈ D.second.support, z.val.1 ≤ b)
    (v : RectangleVertex (0,0) N N) (hv : b ≤ v.val.1) : 3 ≤ D.rank v := by
  by_cases hc : v ∈ D.second.support
  · rw [(D.rank_second_iff v).mpr hc]
  have hb := (mem_latticeRectangle (0,0) v.val N N).mp v.property
  let w : RectangleVertex (0,0) N N := ⟨((N:ℤ),v.val.2),by
    rw [mem_latticeRectangle]
    dsimp at hb ⊢
    exact ⟨⟨by omega,by omega⟩,hb.2⟩⟩
  obtain ⟨p,hp⟩ := originSquare_row_walk N w v rfl
  have hreach : v ∈ cutReachRegion (rectangleGraph (0,0) N N)
      {z | z ∈ D.second.support} (Square.squareRightArc (0,0) N) := by
    refine ⟨w,by change (N:ℤ)=0+(N:ℤ); omega,p,?_⟩
    intro z hz hzc
    have hr := hp z hz
    have hf := hsecond z hzc
    have hvN : v.val.1 ≤ (N:ℤ) := by simpa using hb.1.2
    simp only [w,min_eq_right hvN,max_eq_left hvN] at hr
    have heq : z = v := Subtype.ext (Prod.ext (by omega) hr.2.2)
    exact hc (heq ▸ hzc)
  have hnotL : v ∉ cutReachRegion (rectangleGraph (0,0) N N)
      {z | z ∈ D.first.support} (Square.squareLeftArc (0,0) N) := by
    intro hleft
    exact Set.disjoint_left.mp D.orderedCuts.regions_disjoint hleft hreach
  have hnotA := D.orderedCuts.rightRegion_avoids_first hreach
  change 3 ≤ orderedCutRank _ _ _ _ _ D.orderedCuts v
  simp only [orderedCutRank,ite_eq_right hnotL,ite_eq_right hnotA,ite_eq_left hreach]
  omega

end SquareCrosscutData
end
end PottsContinuity.PlanarMixed
