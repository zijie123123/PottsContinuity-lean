/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarPartitionUpper.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollar
public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import PottsContinuity.PD.FK.DomainMarkov
public import PottsContinuity.PD.FK.Wiring
public import PottsContinuity.PD.FK.IsolatedBoundaryComponents
public import Mathlib.Tactic
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

noncomputable section

def rectangleDoubleCollarInnerBottom (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleDoubleCollarInnerVertex a w h) :=
  {v | v.val.2 = a.2}

def rectangleDoubleCollarInnerTop (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleDoubleCollarInnerVertex a w h) :=
  {v | v.val.2 = a.2 + (h : ℤ)}

def rectangleDoubleCollarOuterLowerBand (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleDoubleCollarOuterVertex a w h) :=
  {v | v.val.2 = a.2 - 1 ∨ v.val.2 = a.2}

def rectangleDoubleCollarOuterUpperBand (a : LatticeVertex) (w h : ℕ) :
    Set (rectangleDoubleCollarOuterVertex a w h) :=
  {v | v.val.2 = a.2 + (h : ℤ) ∨ v.val.2 = a.2 + (h : ℤ) + 1}

theorem rectangleDoubleCollarInnerBottom_disjoint_top
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) :
    Disjoint (rectangleDoubleCollarInnerBottom a w h)
      (rectangleDoubleCollarInnerTop a w h) := by
  apply Set.disjoint_left.mpr
  intro v hvB hvT
  change v.val.2 = a.2 at hvB
  change v.val.2 = a.2 + (h : ℤ) at hvT
  omega

private theorem rectangleDoubleCollarOuterBands_disjoint
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) :
    Disjoint (rectangleDoubleCollarOuterLowerBand a w h)
      (rectangleDoubleCollarOuterUpperBand a w h) := by
  apply Set.disjoint_left.mpr
  intro v hvL hvU
  change v.val.2 = a.2 - 1 ∨ v.val.2 = a.2 at hvL
  change v.val.2 = a.2 + (h : ℤ) ∨
    v.val.2 = a.2 + (h : ℤ) + 1 at hvU
  omega

private theorem rectangleDoubleCollar_componentSetoid_le_twoBands
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) :
    componentSetoid (rectangleDoubleCollarOuterGraph a w h)
      (BoundaryCondition.free (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
      (rectangleDoubleCollarState a w h).val ≤
      twoBlockSetoid (rectangleDoubleCollarOuterLowerBand a w h)
        (rectangleDoubleCollarOuterUpperBand a w h)
        (rectangleDoubleCollarOuterBands_disjoint a w h hh) := by
  apply componentSetoid_le
  · intro x y hconn
    apply reachableSetoid_le_of_adj (openGraph _ (rectangleDoubleCollarState a w h).val)
      _ ?_ hconn
    intro x y hxy
    rw [openGraph_adj] at hxy
    change s(x, y) ∈ Subtype.val ''
      (↑(rectangleDoubleCollarState a w h).val : Set
        (rectangleDoubleCollarOuterGraph a w h).edgeSet) at hxy
    rcases hxy with ⟨e, he, hxyE⟩
    have heState : e ∈ (rectangleDoubleCollarState a w h).val := he
    obtain ⟨u, v, huv, hband⟩ :=
      rectangleDoubleCollar_removed_edge_endpoints a w h hh heState
    have hxyUV : s(x, y) = s(u, v) := hxyE.symm.trans huv
    rcases Sym2.eq_iff.mp hxyUV with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · change x = y ∨
        (x ∈ rectangleDoubleCollarOuterLowerBand a w h ∧
          y ∈ rectangleDoubleCollarOuterLowerBand a w h) ∨
        (x ∈ rectangleDoubleCollarOuterUpperBand a w h ∧
          y ∈ rectangleDoubleCollarOuterUpperBand a w h)
      rw [hxu, hyv]
      change u = v ∨
        (u ∈ rectangleDoubleCollarOuterLowerBand a w h ∧
          v ∈ rectangleDoubleCollarOuterLowerBand a w h) ∨
        (u ∈ rectangleDoubleCollarOuterUpperBand a w h ∧
          v ∈ rectangleDoubleCollarOuterUpperBand a w h)
      rcases hband with hbot | htop
      · exact Or.inr (Or.inl ⟨by change u.val.2 = a.2 - 1 ∨ u.val.2 = a.2; omega,
          by change v.val.2 = a.2 - 1 ∨ v.val.2 = a.2; omega⟩)
      · exact Or.inr (Or.inr ⟨by change u.val.2 = a.2 + (h : ℤ) ∨
            u.val.2 = a.2 + (h : ℤ) + 1; omega,
          by change v.val.2 = a.2 + (h : ℤ) ∨
            v.val.2 = a.2 + (h : ℤ) + 1; omega⟩)
    · apply (twoBlockSetoid _ _ _).symm
      rw [hxv, hyu]
      change u = v ∨
        (u ∈ rectangleDoubleCollarOuterLowerBand a w h ∧
          v ∈ rectangleDoubleCollarOuterLowerBand a w h) ∨
        (u ∈ rectangleDoubleCollarOuterUpperBand a w h ∧
          v ∈ rectangleDoubleCollarOuterUpperBand a w h)
      rcases hband with hbot | htop
      · exact Or.inr (Or.inl ⟨by change u.val.2 = a.2 - 1 ∨ u.val.2 = a.2; omega,
          by change v.val.2 = a.2 - 1 ∨ v.val.2 = a.2; omega⟩)
      · exact Or.inr (Or.inr ⟨by change u.val.2 = a.2 + (h : ℤ) ∨
            u.val.2 = a.2 + (h : ℤ) + 1; omega,
          by change v.val.2 = a.2 + (h : ℤ) ∨
            v.val.2 = a.2 + (h : ℤ) + 1; omega⟩)
  · intro x y hxy
    change x = y at hxy
    subst y
    exact (twoBlockSetoid _ _ _).refl x

/-- The pullback of the outer free boundary frozen by every removed-open
collar edge is bounded by the inner bottom/top rows wired separately. -/
theorem rectangleDoubleCollar_frozen_pullback_partition_le_twoBlocks
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h) :
    (isolatedExtensionPullbackBoundary
      (rectangleDoubleCollarEmbedding a w h)
      (frozenBoundary
        (BoundaryCondition.free
          (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
        (rectangleDoubleCollarState a w h).val)).partition ≤
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom a w h)
        (rectangleDoubleCollarInnerTop a w h)
        (rectangleDoubleCollarInnerBottom_disjoint_top a w h hh)).partition := by
  let f := rectangleDoubleCollarEmbedding a w h
  let B := rectangleDoubleCollarInnerBottom a w h
  let T := rectangleDoubleCollarInnerTop a w h
  let LB := rectangleDoubleCollarOuterLowerBand a w h
  let UB := rectangleDoubleCollarOuterUpperBand a w h
  have hcomp := rectangleDoubleCollar_componentSetoid_le_twoBands a w h hh
  intro x y hxy
  change (componentSetoid (rectangleDoubleCollarOuterGraph a w h)
    (BoundaryCondition.free (∅ : Set (rectangleDoubleCollarOuterVertex a w h)))
    (rectangleDoubleCollarState a w h).val).r (f x) (f y) at hxy
  have hband := hcomp hxy
  change f x = f y ∨ (f x ∈ LB ∧ f y ∈ LB) ∨ (f x ∈ UB ∧ f y ∈ UB) at hband
  rw [twoBlockBoundary_partition_rel]
  rcases hband with heq | hLB | hUB
  · exact Or.inl (f.injective heq)
  · have hxB : x ∈ B := by
      have hxBand := hLB.1
      change (f x).val.2 = a.2 - 1 ∨ (f x).val.2 = a.2 at hxBand
      rw [rectangleDoubleCollarEmbedding_val] at hxBand
      have hbox := x.property
      rw [mem_latticeRectangle] at hbox
      change x.val.2 = a.2
      rcases hxBand with houter | hbottom
      · omega
      · exact hbottom
    have hyB : y ∈ B := by
      have hyBand := hLB.2
      change (f y).val.2 = a.2 - 1 ∨ (f y).val.2 = a.2 at hyBand
      rw [rectangleDoubleCollarEmbedding_val] at hyBand
      have hbox := y.property
      rw [mem_latticeRectangle] at hbox
      change y.val.2 = a.2
      rcases hyBand with houter | hbottom
      · omega
      · exact hbottom
    exact Or.inr (Or.inl ⟨hxB, hyB⟩)
  · have hxT : x ∈ T := by
      have hxBand := hUB.1
      change (f x).val.2 = a.2 + (h : ℤ) ∨
        (f x).val.2 = a.2 + (h : ℤ) + 1 at hxBand
      rw [rectangleDoubleCollarEmbedding_val] at hxBand
      have hbox := x.property
      rw [mem_latticeRectangle] at hbox
      change x.val.2 = a.2 + (h : ℤ)
      rcases hxBand with htop | houter
      · exact htop
      · omega
    have hyT : y ∈ T := by
      have hyBand := hUB.2
      change (f y).val.2 = a.2 + (h : ℤ) ∨
        (f y).val.2 = a.2 + (h : ℤ) + 1 at hyBand
      rw [rectangleDoubleCollarEmbedding_val] at hyBand
      have hbox := y.property
      rw [mem_latticeRectangle] at hbox
      change y.val.2 = a.2 + (h : ℤ)
      rcases hyBand with htop | houter
      · exact htop
      · omega
    exact Or.inr (Or.inr ⟨hxT, hyT⟩)

end
end PottsContinuity.PlanarMixed.Square
