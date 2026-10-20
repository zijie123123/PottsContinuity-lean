module

public import PottsContinuity.PlanarMixed.Square.RectangleCrossingSymmetry
public import PottsContinuity.PD.Duality.FiniteDuality
public import PottsContinuity.PD.Duality.RectangleFlowDimension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Actual primal/dual coordinate swap on squares

Adapted from the edge-labelled reflection proof in
FKconvergence/FiniteFK/RectangleDualVerticalReflection.lean. The coordinate
swap exchanges the two bond axes without reversing the normalized endpoints.
Every vertex, including the expanded dual boundary vertices, is retained.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial
noncomputable section

def swapBond (b : LatticeBond) : LatticeBond :=
  match b.axis with
  | .horizontal => ⟨latticeCoordinateSwap b.base, .vertical⟩
  | .vertical => ⟨latticeCoordinateSwap b.base, .horizontal⟩

 theorem swapBond_mem (z : ℤ) (N : ℕ) (b : RectanglePrimalBond (z,z) N N) :
    (swapBond b.val).source ∈ latticeRectangle (z,z) N N ∧
      (swapBond b.val).target ∈ latticeRectangle (z,z) N N := by
  rcases b with ⟨⟨⟨x,y⟩, ax⟩, hm⟩
  cases ax <;>
    simp only [swapBond, latticeCoordinateSwap, LatticeBond.source, LatticeBond.target] <;>
    simp only [LatticeBond.source, LatticeBond.target, mem_latticeRectangle] at hm <;>
    constructor <;> rw [mem_latticeRectangle] <;> constructor <;> omega

private theorem swapBond_toSym2 (b : LatticeBond) :
    (swapBond b).toSym2 = Sym2.map latticeCoordinateSwap b.toSym2 := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> rfl

private theorem dualBond_swap (b : LatticeBond) :
    dualBondOfPrimal (swapBond b) = swapBond (dualBondOfPrimal b) := by
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;> rfl

 theorem dualSwap_mem (z : ℤ) (N : ℕ) (v : RectangleDualVertex (z,z) N N) :
    latticeCoordinateSwap v.val ∈ rectangleDualExpanded (z,z) N N := by
  have hv : v.val ∈ latticeRectangle (z-1,z-1) (N+1) (N+1) := v.property
  change latticeCoordinateSwap v.val ∈ latticeRectangle (z-1,z-1) (N+1) (N+1)
  rw [mem_latticeRectangle] at hv ⊢
  exact ⟨hv.2, hv.1⟩

/-- The literal coordinate swap of the expanded dual square. -/
def squareDualSwapVertexEquiv (z : ℤ) (N : ℕ) :
    RectangleDualVertex (z,z) N N ≃ RectangleDualVertex (z,z) N N where
  toFun v := ⟨latticeCoordinateSwap v.val, dualSwap_mem z N v⟩
  invFun v := ⟨latticeCoordinateSwap v.val, dualSwap_mem z N v⟩
  left_inv v := Subtype.ext (latticeCoordinateSwap_swap v.val)
  right_inv v := Subtype.ext (latticeCoordinateSwap_swap v.val)

@[simp] theorem squareDualSwapVertexEquiv_val (z : ℤ) (N : ℕ)
    (v : RectangleDualVertex (z,z) N N) :
    (squareDualSwapVertexEquiv z N v).val = latticeCoordinateSwap v.val := rfl

/-- The primal coordinate swap with its source and target explicitly the same square. -/
def squarePrimalGraphSwapIso (z : ℤ) (N : ℕ) :
    rectangleGraph (z,z) N N ≃g rectangleGraph (z,z) N N where
  toEquiv := rectangleVertexCoordinateSwapEquiv (z,z) N N
  map_rel_iff' := by
    intro u v
    exact squareLattice_adj_coordinateSwap_iff u.val v.val

@[simp] theorem squarePrimalGraphSwapIso_val (z : ℤ) (N : ℕ)
    (v : RectangleVertex (z,z) N N) :
    (squarePrimalGraphSwapIso z N v).val = latticeCoordinateSwap v.val := rfl

def swapPrimalEdge (z : ℤ) (N : ℕ) (e : rectanglePrimalEdgeCarrier (z,z) N N) :
    rectanglePrimalEdgeCarrier (z,z) N N :=
  (rectanglePrimalEdgeBondEquiv (z,z) N N).symm
    ⟨swapBond (rectanglePrimalEdgeBond (z,z) N N e),
      swapBond_mem z N ⟨_, rectanglePrimalEdgeBond_endpoints_mem_public (z,z) N N e⟩⟩

private theorem swapPrimalEdge_bond (z : ℤ) (N : ℕ)
    (e : rectanglePrimalEdgeCarrier (z,z) N N) :
    rectanglePrimalEdgeBond (z,z) N N (swapPrimalEdge z N e) =
      swapBond (rectanglePrimalEdgeBond (z,z) N N e) := by
  exact congrArg Subtype.val ((rectanglePrimalEdgeBondEquiv (z,z) N N).apply_symm_apply
    ⟨swapBond (rectanglePrimalEdgeBond (z,z) N N e),
      swapBond_mem z N ⟨_, rectanglePrimalEdgeBond_endpoints_mem_public (z,z) N N e⟩⟩)

def swapDualEdge (z : ℤ) (N : ℕ) (e : RectangleDualEdgeCarrier (z,z) N N) :
    RectangleDualEdgeCarrier (z,z) N N :=
  rectanglePrimalDualEdgeEquiv (z,z) N N (swapPrimalEdge z N e.primalEdge)

private theorem swapPrimalEdge_eq_iso (z : ℤ) (N : ℕ)
    (e : (rectangleGraph (z,z) N N).edgeSet) :
    swapPrimalEdge z N e =
      configurationIsoEdgeEquiv (squarePrimalGraphSwapIso z N) e := by
  let ec : rectanglePrimalEdgeCarrier (z,z) N N := e
  let em : rectanglePrimalEdgeCarrier (z,z) N N :=
    configurationIsoEdgeEquiv (squarePrimalGraphSwapIso z N) e
  apply (rectanglePrimalEdgeBondEquiv (z,z) N N).injective
  apply Subtype.ext
  apply LatticeBond.toSym2_injective
  change (rectanglePrimalEdgeBond (z,z) N N (swapPrimalEdge z N ec)).toSym2 =
    (rectanglePrimalEdgeBond (z,z) N N em).toSym2
  rw [swapPrimalEdge_bond, swapBond_toSym2,
    rectanglePrimalEdgeBond_toSym2_public, rectanglePrimalEdgeBond_toSym2_public]
  dsimp [em, configurationIsoEdgeEquiv, SimpleGraph.Iso.mapEdgeSet,
    SimpleGraph.Hom.mapEdgeSet]
  rw [Sym2.map_map]
  change Sym2.map (latticeCoordinateSwap ∘ (fun v : RectangleVertex (z,z) N N => v.val)) e.val =
    Sym2.map (fun v : RectangleVertex (z,z) N N => v.val)
      (Sym2.map (rectangleVertexCoordinateSwapEquiv (z,z) N N) e.val)
  exact Sym2.inductionOn e.val (fun u v => rfl)

private theorem swapDualEdge_crossing (z : ℤ) (N : ℕ)
    (e : RectangleDualEdgeCarrier (z,z) N N) :
    (swapDualEdge z N e).crossingBond = swapBond e.crossingBond := by
  change dualBondOfPrimal (rectanglePrimalEdgeBond (z,z) N N (swapPrimalEdge z N e.primalEdge)) = _
  rw [swapPrimalEdge_bond, dualBond_swap, e.crossingBond_eq]
  rfl

private theorem swapDualEdge_pair (z : ℤ) (N : ℕ)
    (e : RectangleDualEdgeCarrier (z,z) N N) :
    s(squareDualSwapVertexEquiv z N (rectangleDualEdgeSource (z,z) N N e),
      squareDualSwapVertexEquiv z N (rectangleDualEdgeTarget (z,z) N N e)) =
      rectangleDualCarrierPair (z,z) N N (swapDualEdge z N e) := by
  apply Sym2.eq_iff.mpr
  rcases e with ⟨pe, ⟨⟨x,y⟩, ax⟩, hc⟩
  cases ax <;> left <;> constructor <;> apply Subtype.ext <;>
    simp [squareDualSwapVertexEquiv_val, rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val, swapDualEdge_crossing, swapBond,
      latticeCoordinateSwap, LatticeBond.source, LatticeBond.target]

/-- Coordinate swap preserves the actual labelled dual-square graph. -/
def squareDualGraphSwapIso (z : ℤ) (N : ℕ) :
    rectangleDualGraph (z,z) N N ≃g rectangleDualGraph (z,z) N N where
  toEquiv := squareDualSwapVertexEquiv z N
  map_rel_iff' := by
    intro u v
    rw [rectangleDualGraph_adj_iff, rectangleDualGraph_adj_iff]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨swapDualEdge z N e, ?_⟩
      have hm := congrArg (Sym2.map (squareDualSwapVertexEquiv z N)) he
      simp only [rectangleDualCarrierPair, Sym2.map_mk] at hm
      rw [swapDualEdge_pair] at hm
      have hu : squareDualSwapVertexEquiv z N (squareDualSwapVertexEquiv z N u) = u :=
        (squareDualSwapVertexEquiv z N).left_inv u
      have hv : squareDualSwapVertexEquiv z N (squareDualSwapVertexEquiv z N v) = v :=
        (squareDualSwapVertexEquiv z N).left_inv v
      rw [hu, hv] at hm
      exact hm
    · rintro ⟨e, he⟩
      refine ⟨swapDualEdge z N e, ?_⟩
      have hm := congrArg (Sym2.map (squareDualSwapVertexEquiv z N)) he
      simp only [rectangleDualCarrierPair, Sym2.map_mk] at hm
      rw [swapDualEdge_pair] at hm
      exact hm

private theorem dualGraphEdge_swap (z : ℤ) (N : ℕ)
    (e : RectangleDualEdgeCarrier (z,z) N N) :
    rectangleDualGraphEdgeEquiv (z,z) N N (swapDualEdge z N e) =
      configurationIsoEdgeEquiv (squareDualGraphSwapIso z N)
        (rectangleDualGraphEdgeEquiv (z,z) N N e) := by
  apply Subtype.ext
  change rectangleDualCarrierPair (z,z) N N (swapDualEdge z N e) =
    Sym2.map (squareDualSwapVertexEquiv z N) (rectangleDualCarrierPair (z,z) N N e)
  rw [← swapDualEdge_pair]
  simp [rectangleDualCarrierPair]

/- The following finite-set reindexing proof is adapted from
FKconvergence/FiniteFK/RectangleDualVerticalReflection.lean. -/
theorem squarePrimalDualConfiguration_swap_commute
    (z : ℤ) (N : ℕ) (A : Configuration (rectangleGraph (z,z) N N)) :
    configurationIso (squareDualGraphSwapIso z N)
        (rectanglePrimalDualConfigurationEquiv (z,z) N N A) =
      rectanglePrimalDualConfigurationEquiv (z,z) N N
        (configurationIso (squarePrimalGraphSwapIso z N) A) := by
  classical
  let A₀ : Finset (rectanglePrimalEdgeCarrier (z,z) N N) := by
    exact A
  let A₁ : Finset (rectanglePrimalEdgeCarrier (z,z) N N) := by
    exact configurationIso (squarePrimalGraphSwapIso z N) A
  apply Finset.ext
  intro d
  let E := (rectangleDualGraphEdgeEquiv (z,z) N N).trans
    (configurationIsoEdgeEquiv (squareDualGraphSwapIso z N))
  obtain ⟨e, rfl⟩ := E.surjective d
  rw [rectanglePrimalDualConfigurationEquiv_apply,
    rectanglePrimalDualConfigurationEquiv_apply]
  change configurationIsoEdgeEquiv
      (squareDualGraphSwapIso z N)
        (rectangleDualGraphEdgeEquiv (z,z) N N e) ∈
      Finset.map (configurationIsoEdgeEquiv
        (squareDualGraphSwapIso z N)).toEmbedding
        (rectangleDualConfiguration (z,z) N N A₀) ↔
    configurationIsoEdgeEquiv
      (squareDualGraphSwapIso z N)
        (rectangleDualGraphEdgeEquiv (z,z) N N e) ∈
      rectangleDualConfiguration (z,z) N N A₁
  have hmap : swapPrimalEdge z N e.primalEdge ∈ A₁ ↔
    e.primalEdge ∈ A₀ := by
    rw [swapPrimalEdge_eq_iso z N e.primalEdge]
    change (configurationIsoEdgeEquiv (squarePrimalGraphSwapIso z N)
        e.primalEdge) ∈ Finset.map
          (configurationIsoEdgeEquiv (squarePrimalGraphSwapIso z N)).toEmbedding A₀ ↔
      e.primalEdge ∈ A₀
    rw [Finset.mem_map]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      have hx' : x = e.primalEdge :=
        (configurationIsoEdgeEquiv
          (squarePrimalGraphSwapIso z N)).injective hxeq
      subst x
      exact hx
    · intro hx
      exact ⟨e.primalEdge, hx, rfl⟩
  have hleft : configurationIsoEdgeEquiv
      (squareDualGraphSwapIso z N)
        (rectangleDualGraphEdgeEquiv (z,z) N N e) ∈
      Finset.map (configurationIsoEdgeEquiv
        (squareDualGraphSwapIso z N)).toEmbedding
        (rectangleDualConfiguration (z,z) N N A₀) ↔
    rectangleDualGraphEdgeEquiv (z,z) N N e ∈ rectangleDualConfiguration (z,z) N N A₀ := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨x, hx, hxeq⟩
      have hx' : x = rectangleDualGraphEdgeEquiv (z,z) N N e :=
        (configurationIsoEdgeEquiv
          (squareDualGraphSwapIso z N)).injective hxeq
      simpa [hx'] using hx
    · intro hx
      exact ⟨rectangleDualGraphEdgeEquiv (z,z) N N e, hx, rfl⟩
  rw [hleft, ← dualGraphEdge_swap,
    mem_rectangleDualConfiguration, mem_rectangleDualConfiguration]
  exact (not_congr hmap).symm

end
end PottsContinuity.PlanarMixed.Square
