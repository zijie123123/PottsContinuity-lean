/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDualHorizontalCore.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDualTopLeaves
public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarDualBoundary
public import PottsContinuity.PlanarMixed.Square.FrozenBoundaryRetraction
public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial
noncomputable section

abbrev rectangleDualHorizontalCoreVertex (a : LatticeVertex) (w h : ℕ) :=
  {v : RectangleDualVertex a w h // a.2 ≤ v.1.2 ∧ v.1.2 ≤ a.2 + (h : ℤ) - 1}

def rectangleDualHorizontalCoreGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (rectangleDualHorizontalCoreVertex a w h) :=
  (rectangleDualGraph a w h).induce
    {v : RectangleDualVertex a w h |
      a.2 ≤ v.1.2 ∧ v.1.2 ≤ a.2 + (h : ℤ) - 1}

def rectangleDualHorizontalCoreInclusion (a : LatticeVertex) (w h : ℕ) :
    rectangleDualHorizontalCoreVertex a w h ↪ RectangleDualVertex a w h :=
  ⟨Subtype.val, Subtype.val_injective⟩

def rectangleDualHorizontalCoreRetraction (a : LatticeVertex) (w h : ℕ)
    (hh : 1 ≤ h) (v : RectangleDualVertex a w h) :
    rectangleDualHorizontalCoreVertex a w h := by
  let y := min (max v.1.2 a.2) (a.2 + (h : ℤ) - 1)
  have hlo : a.2 ≤ y := by
    dsimp [y]
    have ha : a.2 ≤ a.2 + (h : ℤ) - 1 := by omega
    exact le_min (le_max_right _ _) ha
  have hhi : y ≤ a.2 + (h : ℤ) - 1 := by
    dsimp [y]
    exact min_le_right _ _
  have hexp : (v.1.1, y) ∈ rectangleDualExpanded a w h := by
    have hv := v.2
    change v.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hv
    rw [mem_latticeRectangle] at hv
    rcases hv with ⟨hx, hy⟩
    have hytop : v.1.2 ≤ a.2 + (h : ℤ) := by omega
    change (v.1.1, y) ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1)
    rw [mem_latticeRectangle]
    refine ⟨hx, ?_⟩
    constructor
    · omega
    · have hmax : max v.1.2 a.2 ≤ a.2 + (h : ℤ) :=
        max_le_iff.mpr ⟨hytop, by omega⟩
      dsimp [y]
      omega
  exact ⟨⟨(v.1.1, y), hexp⟩, hlo, hhi⟩

@[simp] theorem rectangleDualHorizontalCoreRetraction_val
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    (v : RectangleDualVertex a w h) :
    (rectangleDualHorizontalCoreRetraction a w h hh v).1.1 =
      (v.1.1, min (max v.1.2 a.2) (a.2 + (h : ℤ) - 1)) := rfl

@[simp] theorem rectangleDualHorizontalCoreRetraction_inclusion
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    (u : rectangleDualHorizontalCoreVertex a w h) :
    rectangleDualHorizontalCoreRetraction a w h hh
      (rectangleDualHorizontalCoreInclusion a w h u) = u := by
  apply Subtype.ext
  apply Subtype.ext
  simp [rectangleDualHorizontalCoreRetraction,
    rectangleDualHorizontalCoreInclusion, u.2]

private theorem rectangleDualHorizontalCoreRetraction_side
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    (v : RectangleDualVertex a w h)
    (hv : v ∈ rectangleDoubleCollarDualInnerVerticalSides a w h) :
    rectangleDualHorizontalCoreRetraction a w h hh v ∈
      {u : rectangleDualHorizontalCoreVertex a w h |
        rectangleDualHorizontalCoreInclusion a w h u ∈
          rectangleDoubleCollarDualInnerVerticalSides a w h} := by
  simp only [rectangleDoubleCollarDualInnerVerticalSides, Set.mem_ofPred_eq] at hv ⊢
  simp only [rectangleDualHorizontalCoreInclusion,
    ]
  exact hv

private theorem rectangleDualHorizontalCoreRetraction_openEdge
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    (K : RemovedConfiguration (rectangleDualGraph a w h)
      (subgraphRemovedEdges
        ((rectangleDualHorizontalCoreGraph a w h).map
          (rectangleDualHorizontalCoreInclusion a w h))
        (rectangleDualGraph a w h)))
    {u v : RectangleDualVertex a w h}
    (hopen : (openGraph (rectangleDualGraph a w h) K.val).Adj u v) :
    (BoundaryCondition.wired
      {x : rectangleDualHorizontalCoreVertex a w h |
        rectangleDualHorizontalCoreInclusion a w h x ∈
          rectangleDoubleCollarDualInnerVerticalSides a w h}).partition.r
      (rectangleDualHorizontalCoreRetraction a w h hh u)
      (rectangleDualHorizontalCoreRetraction a w h hh v) := by
  classical
  have hAdj : (rectangleDualGraph a w h).Adj u v :=
    (openGraph_le (rectangleDualGraph a w h) K.val) hopen
  rw [openGraph_adj] at hopen
  rcases hopen with ⟨e, heK, heuv⟩
  have hremoved := K.property heK
  have hnotmap : e.1 ∉
      ((rectangleDualHorizontalCoreGraph a w h).map
        (rectangleDualHorizontalCoreInclusion a w h)).edgeSet :=
    (mem_subgraphRemovedEdges e).mp hremoved
  by_cases huBot : u.1.2 = a.2 - 1
  · obtain ⟨hvu, _, _⟩ :=
      generalRectangleDualBottomRow_adj_neighbor a w h u.1.1 u v
        (by exact congrArg (fun y : ℤ => (u.1.1, y)) huBot)
        hAdj
    apply (BoundaryCondition.wired_rel _ _ _).2
    left
    apply Subtype.ext
    apply Subtype.ext
    simp [rectangleDualHorizontalCoreRetraction_val, hvu, huBot]
  · by_cases hvBot : v.1.2 = a.2 - 1
    · obtain ⟨huv', _, _⟩ :=
        generalRectangleDualBottomRow_adj_neighbor a w h v.1.1 v u
          (by exact congrArg (fun y : ℤ => (v.1.1, y)) hvBot)
          hAdj.symm
      apply (BoundaryCondition.wired_rel _ _ _).2
      left
      apply Subtype.ext
      apply Subtype.ext
      simp [rectangleDualHorizontalCoreRetraction_val, huv', hvBot]
    · by_cases huTop : u.1.2 = a.2 + (h : ℤ)
      · obtain ⟨hvu, _, _⟩ :=
          rectangleDualTopRow_adj_neighbor a w h u.1.1 u v
            (by exact congrArg (fun y : ℤ => (u.1.1, y)) huTop)
            hAdj
        apply (BoundaryCondition.wired_rel _ _ _).2
        left
        apply Subtype.ext
        apply Subtype.ext
        simp [rectangleDualHorizontalCoreRetraction_val, hvu, huTop]
      · by_cases hvTop : v.1.2 = a.2 + (h : ℤ)
        · obtain ⟨huv', _, _⟩ :=
            rectangleDualTopRow_adj_neighbor a w h v.1.1 v u
              (by exact congrArg (fun y : ℤ => (v.1.1, y)) hvTop)
              hAdj.symm
          apply (BoundaryCondition.wired_rel _ _ _).2
          left
          apply Subtype.ext
          apply Subtype.ext
          simp [rectangleDualHorizontalCoreRetraction_val, huv', hvTop]
        · have huCore : a.2 ≤ u.1.2 ∧ u.1.2 ≤ a.2 + (h : ℤ) - 1 := by
            have hv := u.2
            change u.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hv
            rw [mem_latticeRectangle] at hv
            rcases hv with ⟨_, ⟨hlo, hhi⟩⟩
            constructor <;> omega
          have hvCore : a.2 ≤ v.1.2 ∧ v.1.2 ≤ a.2 + (h : ℤ) - 1 := by
            have hv := v.2
            change v.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hv
            rw [mem_latticeRectangle] at hv
            rcases hv with ⟨_, ⟨hlo, hhi⟩⟩
            constructor <;> omega
          let cu : rectangleDualHorizontalCoreVertex a w h := ⟨u, huCore⟩
          let cv : rectangleDualHorizontalCoreVertex a w h := ⟨v, hvCore⟩
          have hG : (rectangleDualHorizontalCoreGraph a w h).Adj cu cv := by
            change (rectangleDualGraph a w h).Adj u v
            exact hAdj
          have hmap : (rectangleDualHorizontalCoreGraph a w h).map
              (rectangleDualHorizontalCoreInclusion a w h) |>.Adj
              (rectangleDualHorizontalCoreInclusion a w h cu)
              (rectangleDualHorizontalCoreInclusion a w h cv) :=
            (SimpleGraph.map_adj _ _ _ _).2 ⟨cu, cv, hG, rfl, rfl⟩
          have hmem : s((rectangleDualHorizontalCoreInclusion a w h cu),
              (rectangleDualHorizontalCoreInclusion a w h cv)) ∈
              ((rectangleDualHorizontalCoreGraph a w h).map
                (rectangleDualHorizontalCoreInclusion a w h)).edgeSet :=
            ((rectangleDualHorizontalCoreGraph a w h).map
              (rectangleDualHorizontalCoreInclusion a w h)).mem_edgeSet.mpr hmap
          have hpair : s((rectangleDualHorizontalCoreInclusion a w h cu),
              (rectangleDualHorizontalCoreInclusion a w h cv)) = e.1 := by
            simpa [rectangleDualHorizontalCoreInclusion, cu, cv] using heuv.symm
          exact False.elim (hnotmap (hpair ▸ hmem))

theorem rectangleDualHorizontalCore_boundary_retraction
    (a : LatticeVertex) (w h : ℕ) (hh : 1 ≤ h)
    (K : RemovedConfiguration (rectangleDualGraph a w h)
      (subgraphRemovedEdges
        ((rectangleDualHorizontalCoreGraph a w h).map
          (rectangleDualHorizontalCoreInclusion a w h))
        (rectangleDualGraph a w h))) :
    (isolatedExtensionPullbackBoundary
      (rectangleDualHorizontalCoreInclusion a w h)
      (frozenBoundary
        (BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h))
        K.val)).partition =
      (BoundaryCondition.wired
        {u : rectangleDualHorizontalCoreVertex a w h |
          rectangleDualHorizontalCoreInclusion a w h u ∈
            rectangleDoubleCollarDualInnerVerticalSides a w h}).partition := by
  classical
  let f := rectangleDualHorizontalCoreInclusion a w h
  let r := rectangleDualHorizontalCoreRetraction a w h hh
  let ξ := BoundaryCondition.wired (rectangleDoubleCollarDualInnerVerticalSides a w h)
  let η := BoundaryCondition.wired {u : rectangleDualHorizontalCoreVertex a w h |
    f u ∈ rectangleDoubleCollarDualInnerVerticalSides a w h}
  have hξ : ∀ x y, ξ.partition.r x y → η.partition.r (r x) (r y) := by
    intro x y hxy
    rw [BoundaryCondition.wired_rel] at hxy
    rcases hxy with heq | ⟨hx, hy⟩
    · apply (BoundaryCondition.wired_rel _ _ _).2
      exact Or.inl (congrArg r heq)
    · apply (BoundaryCondition.wired_rel _ _ _).2
      exact Or.inr ⟨rectangleDualHorizontalCoreRetraction_side a w h hh x hx,
        rectangleDualHorizontalCoreRetraction_side a w h hh y hy⟩
  have hopen : ∀ x y, (openGraph (rectangleDualGraph a w h) K.val).Adj x y →
      η.partition.r (r x) (r y) := by
    intro x y hxy
    exact rectangleDualHorizontalCoreRetraction_openEdge a w h hh K hxy
  have hlower : η.partition ≤ Setoid.comap f ξ.partition := by
    intro u v huv
    change (BoundaryCondition.wired
      {u : rectangleDualHorizontalCoreVertex a w h |
        f u ∈ rectangleDoubleCollarDualInnerVerticalSides a w h}).partition.r u v at huv
    rw [BoundaryCondition.wired_rel] at huv
    change (BoundaryCondition.wired
      (rectangleDoubleCollarDualInnerVerticalSides a w h)).partition.r (f u) (f v)
    rw [BoundaryCondition.wired_rel]
    rcases huv with heq | ⟨hu, hv⟩
    · exact Or.inl (congrArg f heq)
    · exact Or.inr ⟨hu, hv⟩
  exact isolatedExtensionPullback_frozenBoundary_partition_eq_of_retraction
    f r (by intro u; exact rectangleDualHorizontalCoreRetraction_inclusion a w h hh u)
    ξ K.val η.partition hξ hopen hlower

end
end PottsContinuity.PlanarMixed.Square
