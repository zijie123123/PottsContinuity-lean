module

public import PottsContinuity.PlanarMixed.FiniteSlit.Prewiring
public import PottsContinuity.FKC.FiniteFK.RectangleConnectivity

/-! Actual auxiliary paths along finite wired arcs. The rectangle-to-path
argument follows SlitReflectedArcConnectivity; the balanced carrier and outer
arc geometry here are the finite route's own definitions. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section
local instance finiteSlitArcConnectivityEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

private theorem rectangle_internal_connected
    {V : Type*} [Finite V] (G : SimpleGraph V) (S : Set V)
    (a : LatticeVertex) (w h : ℕ) (f : RectangleVertex a w h → V)
    (hf : ∀ u v, (rectangleGraph a w h).Adj u v → G.Adj (f u) (f v))
    (hS : ∀ u, f u ∈ S) (u v : RectangleVertex a w h) :
    ActualConnected G (internalBonds G S) (f u) (f v) := by
  let φ : rectangleGraph a w h →g openGraph G (internalBonds G S) :=
    { toFun := f
      map_rel' := by
        intro z t hzt
        have hG := hf z t hzt
        exact (openGraph_adj G _ _ _).mpr
          ⟨⟨s(f z,f t),G.mem_edgeSet.mpr hG⟩,
            (mem_internalBonds_pair G S _ _ hG).mpr ⟨hS z,hS t⟩,rfl⟩ }
  let ψ : FKC.rectangleGraph a w h →g rectangleGraph a w h :=
    { toFun := id
      map_rel' := by
        intro z t hzt
        exact (PD.FK.squareLattice_adj_iff _ _).mpr hzt }
  exact ((FKC.FiniteFK.rectangleGraph_reachable_all a w h u v).map ψ).map φ

/-- Any rectangular piece of one wired arc has actual auxiliary open paths.
The hypotheses check the physical carrier and retained bonds, not wiring links. -/
theorem internalEdges_connected_of_rectangle (M : ℕ) (x y : ℤ)
    (a : LatticeVertex) (w h : ℕ)
    (hsub : PD.FK.latticeRectangle a w h ⊆
      PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (hret : ∀ u v : RectangleVertex a w h, (rectangleGraph a w h).Adj u v →
      ¬ (y < u.val.2 ∧ y < v.val.2 ∧
        ((u.val.1 = x-1 ∧ v.val.1 = x) ∨ (v.val.1 = x-1 ∧ u.val.1 = x))))
    (harc : (∀ z : RectangleVertex a w h, (⟨z.val,hsub z.property⟩ : Vertex M x) ∈ alpha M x) ∨
      (∀ z : RectangleVertex a w h, (⟨z.val,hsub z.property⟩ : Vertex M x) ∈ beta M x y))
    (u v : RectangleVertex a w h) :
    ActualConnected (graph M x y) (internalEdges M x y)
      ⟨u.val,hsub u.property⟩ ⟨v.val,hsub v.property⟩ := by
  let f : RectangleVertex a w h → Vertex M x := fun z => ⟨z.val,hsub z.property⟩
  have hf : ∀ u v, (rectangleGraph a w h).Adj u v → (graph M x y).Adj (f u) (f v) :=
    fun u v huv => ⟨huv,hret u v huv⟩
  rcases harc with ha | hb
  · exact actualConnected_mono Finset.subset_union_left
      (rectangle_internal_connected (graph M x y) (alpha M x) a w h f hf ha u v)
  · exact actualConnected_mono Finset.subset_union_right
      (rectangle_internal_connected (graph M x y) (beta M x y) a w h f hf hb u v)

/-- The whole left outer side is an actual auxiliary open path, for every
sample and truncation size. Its fixed horizontal coordinate avoids the slit. -/
theorem leftSide_internal_connected (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u v : Vertex M x) (hu : u.val.1 = x-(M : ℤ)) (hv : v.val.1 = x-(M : ℤ)) :
    ActualConnected (graph M x y) (internalEdges M x y) u v := by
  let a : LatticeVertex := (x-(M : ℤ),0)
  have hs : PD.FK.latticeRectangle a 0 M ⊆
      PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
    intro z hz
    rw [PD.FK.mem_latticeRectangle] at hz
    apply (mem_rectangle_iff M x (by omega) z).mpr
    dsimp [a] at hz
    simp only [zero_add,add_zero] at hz
    omega
  have hmem (z : Vertex M x) (hz : z.val.1 = x-(M : ℤ)) :
      z.val ∈ PD.FK.latticeRectangle a 0 M := by
    have hb := (mem_rectangle_iff M x (by omega) z.val).mp z.property
    rw [PD.FK.mem_latticeRectangle]
    dsimp [a]
    simp only [zero_add,add_zero]
    omega
  have hcol (z : RectangleVertex a 0 M) : z.val.1 = x-(M : ℤ) := by
    have hz := (PD.FK.mem_latticeRectangle _ _ _ _).mp z.property
    dsimp [a] at hz
    simp only [zero_add,add_zero] at hz
    omega
  exact internalEdges_connected_of_rectangle M x y a 0 M hs
    (by intro z t _; have := hcol z; have := hcol t; omega)
    (Or.inl (fun z => Or.inr (Or.inl (hcol z))))
    ⟨u.val,hmem u hu⟩ ⟨v.val,hmem v hv⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
