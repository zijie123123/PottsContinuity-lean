/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollar.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.Duality.Rectangle
public import PottsContinuity.PD.FK.SubgraphComparison
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK

noncomputable section

abbrev rectangleDoubleCollarInnerGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleGraph a w h

abbrev rectangleDoubleCollarOuterGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleGraph (a.1, a.2 - 1) w (h + 2)

abbrev rectangleDoubleCollarInnerVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleVertex a w h

abbrev rectangleDoubleCollarOuterVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleVertex (a.1, a.2 - 1) w (h + 2)

theorem rectangleDoubleCollar_vertex_inclusion (a : LatticeVertex) (w h : ℕ) :
    latticeRectangle a w h ⊆ latticeRectangle (a.1, a.2 - 1) w (h + 2) := by
  intro z hz
  rw [mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
  exact ⟨⟨hxlo, hxhi⟩, ⟨by omega, by omega⟩⟩

def rectangleDoubleCollarEmbedding (a : LatticeVertex) (w h : ℕ) :
    rectangleDoubleCollarInnerVertex a w h ↪ rectangleDoubleCollarOuterVertex a w h :=
  rectangleVertexEmbedding (rectangleDoubleCollar_vertex_inclusion a w h)

@[simp] theorem rectangleDoubleCollarEmbedding_val (a : LatticeVertex) (w h : ℕ)
    (v : rectangleDoubleCollarInnerVertex a w h) :
    (rectangleDoubleCollarEmbedding a w h v).val = v.val := rfl

theorem rectangleDoubleCollar_map_le (a : LatticeVertex) (w h : ℕ) :
    (rectangleDoubleCollarInnerGraph a w h).map (rectangleDoubleCollarEmbedding a w h) ≤
      rectangleDoubleCollarOuterGraph a w h :=
  rectangleGraph_map_rectangleVertexEmbedding (rectangleDoubleCollar_vertex_inclusion a w h)

local instance rectangleDoubleCollarOuterEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarOuterGraph a w h).edgeSet := Classical.decEq _

def rectangleDoubleCollarRemoved (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleDoubleCollarOuterGraph a w h) :=
  subgraphRemovedEdges
    ((rectangleDoubleCollarInnerGraph a w h).map (rectangleDoubleCollarEmbedding a w h))
    (rectangleDoubleCollarOuterGraph a w h)

def rectangleDoubleCollarState (a : LatticeVertex) (w h : ℕ) :
    RemovedConfiguration (rectangleDoubleCollarOuterGraph a w h)
      (rectangleDoubleCollarRemoved a w h) :=
  ⟨rectangleDoubleCollarRemoved a w h, Finset.Subset.rfl⟩

@[simp] theorem rectangleDoubleCollarRemoved_mem_iff (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleDoubleCollarOuterGraph a w h).edgeSet) :
    e ∈ rectangleDoubleCollarRemoved a w h ↔
      e.val ∉ ((rectangleDoubleCollarInnerGraph a w h).map
        (rectangleDoubleCollarEmbedding a w h)).edgeSet := by
  simp [rectangleDoubleCollarRemoved]

private theorem rectangleDoubleCollar_outside_endpoint_band
    (a : LatticeVertex) (w h : ℕ) (_hh : 1 ≤ h)
    (x y : rectangleDoubleCollarOuterVertex a w h)
    (hxy : squareLattice.Adj x.val y.val)
    (hnotInner : ¬ (a.2 ≤ x.val.2 ∧ x.val.2 ≤ a.2 + (h : ℤ))) :
    (((x.val.2 = a.2 - 1 ∨ x.val.2 = a.2) ∧
        (y.val.2 = a.2 - 1 ∨ y.val.2 = a.2) ∧
        (x.val.2 = a.2 - 1 ∨ y.val.2 = a.2 - 1)) ∨
      ((x.val.2 = a.2 + (h : ℤ) ∨ x.val.2 = a.2 + (h : ℤ) + 1) ∧
        (y.val.2 = a.2 + (h : ℤ) ∨ y.val.2 = a.2 + (h : ℤ) + 1) ∧
        (x.val.2 = a.2 + (h : ℤ) + 1 ∨ y.val.2 = a.2 + (h : ℤ) + 1))) := by
  have hxbox := x.property
  have hybox := y.property
  rw [mem_latticeRectangle] at hxbox hybox
  rcases hxbox with ⟨⟨_, _⟩, ⟨hxlo, hxhi⟩⟩
  rcases hybox with ⟨⟨_, _⟩, ⟨hylo, hyhi⟩⟩
  have hxoutside : x.val.2 = a.2 - 1 ∨ x.val.2 = a.2 + (h : ℤ) + 1 := by omega
  rcases (squareLattice_adj_iff x.val y.val).mp hxy with hhor | hver
  · rcases hhor with ⟨hstep, hyEq⟩
    have hyEq' : y.val.2 = x.val.2 := hyEq.symm
    rcases hxoutside with hx | hx
    · left; refine ⟨?_, ?_, ?_⟩ <;> omega
    · right; refine ⟨?_, ?_, ?_⟩ <;> omega
  · rcases hver with ⟨hxEq, hstep⟩
    rcases hxoutside with hx | hx
    · left; refine ⟨?_, ?_, ?_⟩ <;> omega
    · right; refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Every edge in the full removed collar is in one of the two disjoint
vertical bands, and its corresponding outer boundary row is one endpoint. -/
theorem rectangleDoubleCollar_removed_edge_endpoints
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    {e : (rectangleDoubleCollarOuterGraph a w h).edgeSet}
    (he : e ∈ (rectangleDoubleCollarState a w h).val) :
    ∃ u v : rectangleDoubleCollarOuterVertex a w h,
      e.val = s(u,v) ∧
      (((u.val.2 = a.2 - 1 ∨ u.val.2 = a.2) ∧
          (v.val.2 = a.2 - 1 ∨ v.val.2 = a.2) ∧
          (u.val.2 = a.2 - 1 ∨ v.val.2 = a.2 - 1)) ∨
        ((u.val.2 = a.2 + (h : ℤ) ∨ u.val.2 = a.2 + (h : ℤ) + 1) ∧
          (v.val.2 = a.2 + (h : ℤ) ∨ v.val.2 = a.2 + (h : ℤ) + 1) ∧
          (u.val.2 = a.2 + (h : ℤ) + 1 ∨ v.val.2 = a.2 + (h : ℤ) + 1))) := by
  classical
  have henot := (rectangleDoubleCollarRemoved_mem_iff a w h e).mp
    (by simpa [rectangleDoubleCollarState] using he)
  obtain ⟨p, hp⟩ := Sym2.mk_surjective e.val
  rcases p with ⟨u, v⟩
  have heval : e.val = s(u,v) := hp.symm
  let x : rectangleDoubleCollarOuterVertex a w h := u
  let y : rectangleDoubleCollarOuterVertex a w h := v
  have hadj : (rectangleDoubleCollarOuterGraph a w h).Adj x y := by
    apply (rectangleDoubleCollarOuterGraph a w h).mem_edgeSet.mp
    simpa [x, y, heval] using e.property
  have hAdj : squareLattice.Adj x.val y.val :=
    (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
  have hnotboth : ¬ (a.2 ≤ x.val.2 ∧ x.val.2 ≤ a.2 + (h : ℤ) ∧
      a.2 ≤ y.val.2 ∧ y.val.2 ≤ a.2 + (h : ℤ)) := by
    intro hb
    let ux : rectangleDoubleCollarInnerVertex a w h := ⟨x.val, by
      have hx := x.property
      rw [mem_latticeRectangle] at hx ⊢
      exact ⟨hx.1, ⟨hb.1, hb.2.1⟩⟩
    ⟩
    let vy : rectangleDoubleCollarInnerVertex a w h := ⟨y.val, by
      have hy := y.property
      rw [mem_latticeRectangle] at hy ⊢
      exact ⟨hy.1, ⟨hb.2.2.1, hb.2.2.2⟩⟩
    ⟩
    have hinner : (rectangleDoubleCollarInnerGraph a w h).Adj ux vy :=
      (rectangleGraph_adj_iff _ _ _ _ _).2 hAdj
    have hmap : ((rectangleDoubleCollarInnerGraph a w h).map
        (rectangleDoubleCollarEmbedding a w h)).Adj x y := by
      rw [SimpleGraph.map_adj]
      refine ⟨ux, vy, hinner, ?_, ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        rfl
    have hmapEdge : s(x,y) ∈ ((rectangleDoubleCollarInnerGraph a w h).map
        (rectangleDoubleCollarEmbedding a w h)).edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr hmap
    apply henot
    rw [heval]
    simpa [x, y] using hmapEdge
  by_cases hxInner : a.2 ≤ x.val.2 ∧ x.val.2 ≤ a.2 + (h : ℤ)
  · have hyOutside : ¬ (a.2 ≤ y.val.2 ∧ y.val.2 ≤ a.2 + (h : ℤ)) := by
      intro hyInner
      exact hnotboth ⟨hxInner.1, hxInner.2, hyInner.1, hyInner.2⟩
    have hband := rectangleDoubleCollar_outside_endpoint_band
      a w h hh y x hAdj.symm hyOutside
    refine ⟨x, y, heval, ?_⟩
    rcases hband with hbot | htop
    · exact Or.inl ⟨hbot.2.1, hbot.1, hbot.2.2.symm⟩
    · exact Or.inr ⟨htop.2.1, htop.1, htop.2.2.symm⟩
  · have hband := rectangleDoubleCollar_outside_endpoint_band
      a w h hh x y hAdj hxInner
    exact ⟨x, y, heval, hband⟩

end
end PottsContinuity.PlanarMixed.Square
