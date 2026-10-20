module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ComplementaryQueryStar
public import PottsContinuity.Thm3.Push.RectangleTopFrontier

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push
noncomputable section

/-- Exact top-port characterization, including the missing rightmost leaf. -/
theorem rectangleDualTopPorts_mem_iff_coordinates
    (a : LatticeVertex) (w h : ℕ) (v : RectangleDualVertex a w h) :
    v ∈ rectangleDualTopPorts a w h ↔
      a.1 ≤ v.val.1 ∧ v.val.1 < a.1+(w:ℤ) ∧ v.val.2=a.2+(h:ℤ) := by
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_range.mp hi
    simp only [rectangleDualTopPortVertex,Nat.min_eq_left (Nat.le_of_lt hi')]
    exact ⟨by omega,by omega,trivial⟩
  · rintro ⟨hlo,hhi,hy⟩
    let i := (v.val.1-a.1).toNat
    have hi : i < w := by dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_range.mpr hi,?_⟩
    apply Subtype.ext
    simp only [rectangleDualTopPortVertex,Nat.min_eq_left (Nat.le_of_lt hi)]
    apply Prod.ext <;> dsimp [i] <;> omega

/-- Exact bottom-port characterization with its true-dual minus-one shift. -/
theorem rectangleDualBottomPorts_mem_iff_coordinates
    (a : LatticeVertex) (w h : ℕ) (v : RectangleDualVertex a w h) :
    v ∈ rectangleDualBottomPorts a w h ↔
      a.1 ≤ v.val.1 ∧ v.val.1 < a.1+(w:ℤ) ∧ v.val.2=a.2-1 := by
  constructor
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_range.mp hi
    simp only [rectangleDualBottomPortVertex,Nat.min_eq_left (Nat.le_of_lt hi')]
    exact ⟨by omega,by omega,trivial⟩
  · rintro ⟨hlo,hhi,hy⟩
    let i := (v.val.1-a.1).toNat
    have hi : i < w := by dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_range.mpr hi,?_⟩
    apply Subtype.ext
    simp only [rectangleDualBottomPortVertex,Nat.min_eq_left (Nat.le_of_lt hi)]
    apply Prod.ext <;> dsimp [i] <;> omega


/-- Every endpoint of an OPEN queried original bond is a reached auxiliary
vertex after the literal double-dual coordinate translation. -/
theorem complementary_raw_open_query_endpoint_reached
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (seeds : Finset (RectangleDualVertex a w h))
    (b : (squareLattice.induce (V : Set LatticeVertex)).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A)))
    (u : (V : Set LatticeVertex)) (hub : u ∈ b.val) :
    ∃ v : RectangleDualVertex a w h, faceIndexMark v.val=u.val ∧
      v ∈ closedClusterReached (DualityExt.rectangleDualEdgeEquiv a w h) seeds
        (originalClosedDualRectangleRead V a w h A) := by
  obtain ⟨e,he,heb⟩ := (mem_complementaryRevealPullback _ _ _ _ b).mp hb
  have heclosed : e ∉ originalClosedDualRectangleRead V a w h A := by
    intro hm
    exact (mem_complementaryEdgeRead _ _ _ A e).mp hm b heb hbA
  have hub' : u.val ∈ Sym2.map Subtype.val b.val := Sym2.mem_map.mpr ⟨u,hub,rfl⟩
  rw [← rectangle_auxiliary_pair_of_original_edge V a w h e b heb] at hub'
  obtain ⟨v,hv,hvu⟩ := Sym2.mem_map.mp hub'
  exact ⟨v,hvu,closedClusterReveal_closed_edge_endpoints_reached _ _ _ e he heclosed v hv⟩

/-- A successful top exploration cannot attach an OPEN queried bond at the
opposite seed row. The original coordinate is one above the dual coordinate. -/
theorem top_raw_open_query_endpoint_above_bottom
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hA : originalClosedDualRectangleRead V a w h A ∈ rectangleHorizontalCrossingEvent a w h)
    (b : (squareLattice.induce (V : Set LatticeVertex)).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (rectangleTopReveal a w h (originalClosedDualRectangleRead V a w h A)))
    (u : (V : Set LatticeVertex)) (hub : u ∈ b.val)
    (hx : a.1+1 ≤ u.val.1 ∧ u.val.1 ≤ a.1+(w:ℤ)) : a.2 < u.val.2 := by
  obtain ⟨v,hvu,hreached⟩ := complementary_raw_open_query_endpoint_reached V a w h A
    (rectangleDualTopPorts a w h) b hbA hb u hub
  have hy := ((PD.FK.mem_latticeRectangle _ _ _ _).mp v.property).2.1
  have hxv := congrArg Prod.fst hvu
  have hyv := congrArg Prod.snd hvu
  simp only [faceIndexMark] at hxv hyv
  have hlow : a.2 ≤ u.val.2 := by
    change a.2-1 ≤ v.val.2 at hy
    omega
  by_contra hnot
  have heq : u.val.2=a.2 := by omega
  have hport : v ∈ rectangleDualBottomPorts a w h :=
    (rectangleDualBottomPorts_mem_iff_coordinates a w h v).mpr ⟨by omega,by omega,by omega⟩
  exact rectangleTopReached_avoids_bottom a w h _ hA hport hreached

/-- The bottom exploration also avoids every top port on a horizontal crossing. -/
theorem rectangleBottomReached_avoids_top
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h)
    {t : RectangleDualVertex a w h} (ht : t ∈ rectangleDualTopPorts a w h) :
    t ∉ closedClusterReached (DualityExt.rectangleDualEdgeEquiv a w h)
      (rectangleDualBottomPorts a w h) A := by
  rintro ⟨b,hb,hbt⟩
  rw [auxiliaryClosedConfiguration_rectangle_eq] at hbt
  exact rectanglePrimalDualCrossings_exclusive a w h A hA
    ⟨b,t,((rectangleDualBottomPorts_mem_iff_coordinates a w h b).mp hb).2.2,
      ((rectangleDualTopPorts_mem_iff_coordinates a w h t).mp ht).2.2,hbt⟩

/-- The lower open queried star cannot touch the opposite upper seed row. -/
theorem bottom_raw_open_query_endpoint_below_top
    (V : Finset LatticeVertex) (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hA : originalClosedDualRectangleRead V a w h A ∈ rectangleHorizontalCrossingEvent a w h)
    (b : (squareLattice.induce (V : Set LatticeVertex)).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ complementaryRevealPullback _ _ (rectangleDualOriginalEdge V a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h)
        (rectangleDualBottomPorts a w h) (originalClosedDualRectangleRead V a w h A)))
    (u : (V : Set LatticeVertex)) (hub : u ∈ b.val)
    (hx : a.1+1 ≤ u.val.1 ∧ u.val.1 ≤ a.1+(w:ℤ)) : u.val.2 ≤ a.2+(h:ℤ) := by
  obtain ⟨v,hvu,hreached⟩ := complementary_raw_open_query_endpoint_reached V a w h A
    (rectangleDualBottomPorts a w h) b hbA hb u hub
  have hy := ((PD.FK.mem_latticeRectangle _ _ _ _).mp v.property).2.2
  have hxv := congrArg Prod.fst hvu
  have hyv := congrArg Prod.snd hvu
  simp only [faceIndexMark] at hxv hyv
  have hhigh : u.val.2 ≤ a.2+(h:ℤ)+1 := by
    change v.val.2 ≤ (a.2-1)+((h+1:ℕ):ℤ) at hy
    norm_num only [Nat.cast_add,Nat.cast_one] at hy
    omega
  by_contra hnot
  have heq : u.val.2=a.2+(h:ℤ)+1 := by omega
  have hport : v ∈ rectangleDualTopPorts a w h :=
    (rectangleDualTopPorts_mem_iff_coordinates a w h v).mpr ⟨by omega,by omega,by omega⟩
  exact rectangleBottomReached_avoids_top a w h _ hA hport hreached

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
