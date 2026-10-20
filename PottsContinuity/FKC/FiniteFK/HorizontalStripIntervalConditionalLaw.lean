-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripIntervalConditionalLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.FrozenBoundaryOutsideRegion
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalTopBoundary
public import PottsContinuity.FKC.FiniteFK.HorizontalStripConditionalBoundary
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutRectangle
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopBoundary
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
noncomputable section

local instance intervalCondInnerEdgeFintype (a : ℤ) (w n : ℕ) :
    Fintype (rectangleGraph (a, 0) w (2 * n)).edgeSet := Fintype.ofFinite _
local instance intervalCondInnerEdgeDecidableEq (a : ℤ) (w n : ℕ) :
    DecidableEq (rectangleGraph (a, 0) w (2 * n)).edgeSet := Classical.decEq _
local instance intervalCondOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance intervalCondOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

private theorem intervalTopSides_outsideOrTop
    {a : ℤ} {w N n : ℕ} (hleft : -(N : ℤ) < a)
    (hright : a + (w : ℤ) < N)
    (f : RectangleVertex (a, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (hfval : ∀ u, (f u).val = u.val) :
    horizontalStripTopSidesSet N n ⊆
      {v | v ∉ Set.range f} ∪ horizontalStripTopWiredSet N n := by
  intro v hv
  simp only [horizontalStripTopSidesSet, Set.mem_ofPred_eq] at hv
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  rcases hv with htop | hleftSide | hrightSide
  · exact Or.inr (by simpa [horizontalStripTopWiredSet] using htop)
  · left
    intro hvRange
    obtain ⟨u, hu⟩ := hvRange
    have hcoord := congrArg (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val.1) hu
    rw [hfval] at hcoord
    have huBounds := u.property
    rw [mem_latticeRectangle] at huBounds
    have hside : v.val.1 = -(N : ℤ) := by simpa using hleftSide
    rw [hside] at hcoord
    rcases huBounds with ⟨⟨huLo, huHi⟩, _⟩
    omega
  · left
    intro hvRange
    obtain ⟨u, hu⟩ := hvRange
    have hcoord := congrArg (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val.1) hu
    rw [hfval] at hcoord
    have huBounds := u.property
    rw [mem_latticeRectangle] at huBounds
    have hside : v.val.1 = (N : ℤ) := by simpa using hrightSide
    rw [hside] at hcoord
    rcases huBounds with ⟨⟨huLo, huHi⟩, _⟩
    omega

 theorem intervalLeftWeak {a : ℤ} {N : ℕ}
    (hleft : -(N : ℤ) < a) : -(N : ℤ) ≤ a := by omega

 theorem intervalRightWeak {a : ℤ} {w N : ℕ}
    (hright : a + (w : ℤ) < N) : a + (w : ℤ) ≤ N := by omega

/-- With an admissible outer boundary and a genuine frozen state whose open
removed edges have both endpoints outside the inner interval, the mapped
conditional law is exactly the actual top-only inner FK law. -/
theorem law_filter_frozen_map_horizontalStripInterval_eq_topOnly
    (a : ℤ) (w n N : ℕ)
    (hleft : -(N : ℤ) < a) (hright : a + (w : ℤ) < N)
    (q : ClusterWeight)
    (ξ : BoundaryCondition (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (K : RemovedConfiguration (horizontalStripCutRectangle N n)
      (subgraphRemovedEdges
        ((rectangleGraph (a, 0) w (2 * n)).map
          (horizontalStripIntervalEmbedding (n := n)
            (intervalLeftWeak (a := a) (N := N) hleft) (intervalRightWeak (a := a) (w := w) (N := N) hright)))
        (horizontalStripCutRectangle N n)))
    (hK : ∀ ⦃e : (horizontalStripCutRectangle N n).edgeSet⦄,
      e ∈ K.val → ∀ ⦃v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)⦄,
        v ∈ e.val → v ∉ Set.range (horizontalStripIntervalEmbedding (n := n)
          (intervalLeftWeak (a := a) (N := N) hleft) (intervalRightWeak (a := a) (w := w) (N := N) hright))) :
    let f := horizontalStripIntervalEmbedding (n := n) (intervalLeftWeak (a := a) (N := N) hleft) (intervalRightWeak (a := a) (w := w) (N := N) hright)
    let hGH : (rectangleGraph (a, 0) w (2 * n)).map f ≤ horizontalStripCutRectangle N n :=
      horizontalStripInterval_map_le (n := n) (intervalLeftWeak (a := a) (N := N) hleft) (intervalRightWeak (a := a) (w := w) (N := N) hright)
    ((law (horizontalStripCutRectangle N n) q ξ).filter
      (frozenStateEvent (subgraphRemovedEdges ((rectangleGraph (a, 0) w (2 * n)).map f)
        (horizontalStripCutRectangle N n)) K)
      (frozenStateEvent_support q ξ _ K)).map
        (embeddedConfigurationRestriction (rectangleGraph (a, 0) w (2 * n))
          (horizontalStripCutRectangle N n) f hGH) =
      law (rectangleGraph (a, 0) w (2 * n)) q
        (horizontalStripIntervalTopWiredBoundary a w n) := by
  dsimp
  let G := rectangleGraph (a, 0) w (2 * n)
  let H := horizontalStripCutRectangle N n
  let f : RectangleVertex (a, 0) w (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripIntervalEmbedding (n := n) (intervalLeftWeak (a := a) (N := N) hleft) (intervalRightWeak (a := a) (w := w) (N := N) hright)
  have hGH : G.map f ≤ H := horizontalStripInterval_map_le (n := n) (intervalLeftWeak (a := a) (N := N) hleft) (intervalRightWeak (a := a) (w := w) (N := N) hright)
  have hboundary :
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition =
        (horizontalStripIntervalTopWiredBoundary a w n).partition := by
    have hf : ∀ u, f u ∉ {v | v ∉ Set.range f} := by
      intro u hu
      exact hu ⟨u, rfl⟩
    have hξ' : ξ.boundary ⊆ {v | v ∉ Set.range f} ∪ horizontalStripTopWiredSet N n := by
      intro v hv
      exact intervalTopSides_outsideOrTop hleft hright f (fun u => rfl) (hξ hv)
    have hpart := isolatedExtensionPullback_frozenBoundary_partition_eq_wired_away
      f {v | v ∉ Set.range f} (horizontalStripTopWiredSet N n) ξ K.val hξ' hTop hK hf
    have hpre : f ⁻¹' horizontalStripTopWiredSet N n =
        horizontalStripIntervalTopWiredSet a w n := by
      ext u
      simp [horizontalStripTopWiredSet, horizontalStripIntervalTopWiredSet, f]
    rw [hpre] at hpart
    exact hpart
  rw [law_filter_frozen_map_embeddedRestriction G H f hGH q ξ K]
  exact law_eq_of_boundary_partition_eq q _ _ hboundary

end
end PottsContinuity.FKC.FiniteFK
