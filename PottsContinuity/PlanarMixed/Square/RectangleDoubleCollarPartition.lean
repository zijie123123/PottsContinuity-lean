/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarPartition.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarPartitionUpper
public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarRowConnectivity
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

noncomputable section

/-- The actual removed-open collar merges each inner terminal row, and no
other inner identifications. Thus its pulled-back frozen partition is exactly
the two-block boundary with bottom and top wired separately. -/
theorem rectangleDoubleCollar_frozen_pullback_partition_eq_twoBlocks
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) :
    (isolatedExtensionPullbackBoundary
      (rectangleDoubleCollarEmbedding a w h)
      (frozenBoundary
        (BoundaryCondition.free
          (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
        (rectangleDoubleCollarState a w h).val)).partition =
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
        (rectangleDoubleCollarInnerTop a w h)
        (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh)).partition := by
  apply Setoid.ext
  intro u v
  constructor
  · intro huv
    exact rectangleDoubleCollar_frozen_pullback_partition_le_twoBlocks a w h hh huv
  · intro hrel
    rw [twoBlockBoundary_partition_rel] at hrel
    rcases hrel with heq | hbottom | htop
    · subst v
      exact (Setoid.comap_rel (rectangleDoubleCollarEmbedding a w h)
        (frozenBoundary
          (BoundaryCondition.free
            (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
          (rectangleDoubleCollarState a w h).val).partition u u).mpr
        (Setoid.refl' (frozenBoundary
          (BoundaryCondition.free
            (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
          (rectangleDoubleCollarState a w h).val).partition _)
    · have huMember : u ∈ rectangleDoubleCollarInnerBottom a w h := hbottom.1
      change u.val.2 = a.2 at huMember
      have hvMember : v ∈ rectangleDoubleCollarInnerBottom a w h := hbottom.2
      change v.val.2 = a.2 at hvMember
      have hu := huMember
      have hv := hvMember
      have hconn := rectangleDoubleCollar_bottom_row_connected a w h u v hu hv
      exact (Setoid.comap_rel (rectangleDoubleCollarEmbedding a w h)
        (frozenBoundary
          (BoundaryCondition.free
            (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
          (rectangleDoubleCollarState a w h).val).partition u v).mpr
        (actualConnected_component (rectangleDoubleCollarOuterGraph a w h)
          (BoundaryCondition.free
            (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
          (rectangleDoubleCollarState a w h).val hconn)
    · have huMember : u ∈ rectangleDoubleCollarInnerTop a w h := htop.1
      change u.val.2 = a.2 + (h : ℤ) at huMember
      have hvMember : v ∈ rectangleDoubleCollarInnerTop a w h := htop.2
      change v.val.2 = a.2 + (h : ℤ) at hvMember
      have hu := huMember
      have hv := hvMember
      have hconn := rectangleDoubleCollar_top_row_connected a w h u v hu hv
      exact (Setoid.comap_rel (rectangleDoubleCollarEmbedding a w h)
        (frozenBoundary
          (BoundaryCondition.free
            (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
          (rectangleDoubleCollarState a w h).val).partition u v).mpr
        (actualConnected_component (rectangleDoubleCollarOuterGraph a w h)
          (BoundaryCondition.free
            (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
          (rectangleDoubleCollarState a w h).val hconn)

end
end PottsContinuity.PlanarMixed.Square
