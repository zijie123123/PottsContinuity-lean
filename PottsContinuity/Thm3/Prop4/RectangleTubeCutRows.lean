module

public import PottsContinuity.Thm3.Prop4.BoxRectangleTubeTransport
public import PottsContinuity.Thm3.Prop4.TubeCutEndpoints

/-!
# Genuine sampled rows of the transported central tube cut

Every row supplies an original horizontal rectangle bond. The consecutive
row interval and its endpoints come from the literal Euclidean tube.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance rectangleTubeCutEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- Every transported cut edge crosses exactly the prescribed column gap. -/
theorem rectangle_tube_cut_column (n : ℕ) (r : ℝ) (u v : LatticeVertex) (k : ℤ) :
    ∀ e ∈ configurationIso (boxTubeRectangleIso n) (radiusTubeCutEdges n r u v k),
      ∃ y : ℤ, Sym2.map Subtype.val e.val = s((k,y),(k+1,y)) := by
  intro e he
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp ((box_rectangle_tube_cut_mem n r u v k e).mp he)
  exact ⟨y,hy.symm⟩

/-- Every literal cut row is a genuine retained horizontal sampled bond,
and its original edge belongs to the transported surgery cut. -/
theorem rectangle_tube_cut_sampled_row (n : ℕ) (r : ℝ) (u v : LatticeVertex) (k y : ℤ)
    (hy : y ∈ radiusTubeCutRows n r u v k) :
    ∃ c : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n),
      c.val = ⟨(k,y),.horizontal⟩ ∧
      rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c ∈
        configurationIso (boxTubeRectangleIso n) (radiusTubeCutEdges n r u v k) := by
  classical
  have hends := (mem_radiusTubeCutRows_iff n r u v k y).mp hy
  have h0 : (k,y) ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    exact ((mem_radiusTube n r u v _).mp hends.1).1
  have h1 : (k+1,y) ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    exact ((mem_radiusTube n r u v _).mp hends.2).1
  let c : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) :=
    ⟨⟨(k,y),.horizontal⟩,h0,h1⟩
  let e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet :=
    rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c
  have he : e ∈ configurationIso (boxTubeRectangleIso n) (radiusTubeCutEdges n r u v k) := by
    apply (box_rectangle_tube_cut_mem n r u v k e).mpr
    change s((k,y),(k+1,y)) ∈ radiusTubeCut n r u v k
    exact Finset.mem_image.mpr ⟨y,hy,rfl⟩
  exact ⟨c,rfl,he⟩

/-- Positive-radius opposite-face tubes give the exact nonempty consecutive
row data required by the sampled central-cut estimate. -/
theorem rectangle_central_tube_cut_rows {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 2 ≤ r)
    (u v : LatticeVertex) (hu : u ∈ box n) (hv : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ radiusTubeCutRows n r u v 0 = Finset.Icc lo hi ∧
      ∀ y ∈ Finset.Icc lo hi,
        ∃ c : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n),
          c.val = ⟨(0,y),.horizontal⟩ ∧
          rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) c ∈
            configurationIso (boxTubeRectangleIso n) (radiusTubeCutEdges n r u v 0) := by
  obtain ⟨lo,hi,hlohi,hrows⟩ := radiusTubeCutRows_eq_interval n r u v 0
    (radiusTubeCutRows_zero_nonempty hn r hr u v hu hv huX hvX)
  refine ⟨lo,hi,hlohi,hrows,?_⟩
  intro y hy
  exact rectangle_tube_cut_sampled_row n r u v 0 y (by rwa [hrows])

end
end PottsContinuity.Thm3.Prop4
