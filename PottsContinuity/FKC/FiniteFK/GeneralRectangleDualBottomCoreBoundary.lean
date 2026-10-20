-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomCoreBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomLeaves
public import PottsContinuity.FKC.FiniteFK.FrozenBoundaryRetraction

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- The literal inclusion of the retained core vertices into the inner dual
vertex carrier. -/
def generalRectangleDualBottomCoreInclusion (a : LatticeVertex) (w h : ℕ) :
    generalRectangleDualBottomCoreVertex a w h ↪ RectangleDualVertex a w h :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Clamp the removed bottom face-base row to its unique parent in the core. -/
def generalRectangleDualBottomCoreRetraction (a : LatticeVertex) (w h : ℕ)
    (v : RectangleDualVertex a w h) : generalRectangleDualBottomCoreVertex a w h := by
  let z : LatticeVertex := (v.1.1, max v.1.2 a.2)
  have hz : z ∈ rectangleDualExpanded a w h := by
    change z ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1)
    rw [mem_latticeRectangle]
    have hv := v.2
    change v.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hv
    rw [mem_latticeRectangle] at hv
    rcases hv with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    refine ⟨⟨hx₁, hx₂⟩, ?_⟩
    exact ⟨le_trans hy₁ (le_max_left _ _),
      max_le_iff.mpr ⟨hy₂, by omega⟩⟩
  exact ⟨⟨z, hz⟩, le_max_right _ _⟩

@[simp] theorem generalRectangleDualBottomCoreRetraction_val
    (a : LatticeVertex) (w h : ℕ) (v : RectangleDualVertex a w h) :
    (generalRectangleDualBottomCoreRetraction a w h v).1.1 =
      (v.1.1, max v.1.2 a.2) := rfl

@[simp] theorem generalRectangleDualBottomCoreRetraction_inclusion
    (a : LatticeVertex) (w h : ℕ)
    (u : generalRectangleDualBottomCoreVertex a w h) :
    generalRectangleDualBottomCoreRetraction a w h
      (generalRectangleDualBottomCoreInclusion a w h u) = u := by
  apply Subtype.ext
  apply Subtype.ext
  simp [generalRectangleDualBottomCoreInclusion,
    generalRectangleDualBottomCoreRetraction, max_eq_left u.2]

private theorem coreRetraction_boundary_mem
    (a : LatticeVertex) (w h : ℕ) (v : RectangleDualVertex a w h)
    (hv : v ∈ generalRectangleDualBottomCollarInnerThreeSides a w h) :
    generalRectangleDualBottomCoreRetraction a w h v ∈
      {u : generalRectangleDualBottomCoreVertex a w h |
        (generalRectangleDualBottomCoreInclusion a w h u) ∈
          generalRectangleDualBottomCollarInnerThreeSides a w h} := by
  simp only [generalRectangleDualBottomCollarInnerThreeSides, Set.mem_ofPred_eq] at hv ⊢
  simp only [generalRectangleDualBottomCoreInclusion,
    ]
  rcases hv with hleft | hright | htop
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hright)
  · exact Or.inr (Or.inr (by
      change max v.1.2 a.2 = a.2 + (h : ℤ)
      rw [max_eq_left (by omega)]
      exact htop))

private theorem coreRetraction_openEdge_preserves_boundary
    (a : LatticeVertex) (w h : ℕ)
    (K : RemovedConfiguration (rectangleDualGraph a w h)
      (subgraphRemovedEdges
        ((generalRectangleDualBottomCoreGraph a w h).map
          (generalRectangleDualBottomCoreInclusion a w h))
        (rectangleDualGraph a w h)))
    {u v : RectangleDualVertex a w h}
    (hopen : (openGraph (rectangleDualGraph a w h) K.val).Adj u v) :
    (BoundaryCondition.wired
      {x : generalRectangleDualBottomCoreVertex a w h |
        (generalRectangleDualBottomCoreInclusion a w h x) ∈
          generalRectangleDualBottomCollarInnerThreeSides a w h}).partition.r
      (generalRectangleDualBottomCoreRetraction a w h u)
      (generalRectangleDualBottomCoreRetraction a w h v) := by
  classical
  have hAdj : (rectangleDualGraph a w h).Adj u v :=
    (openGraph_le (rectangleDualGraph a w h) K.val) hopen
  rw [openGraph_adj] at hopen
  rcases hopen with ⟨e, heK, heuv⟩
  have hremoved := K.property heK
  have hnotmap : e.1 ∉
      ((generalRectangleDualBottomCoreGraph a w h).map
        (generalRectangleDualBottomCoreInclusion a w h)).edgeSet :=
    (mem_subgraphRemovedEdges e).mp hremoved
  by_cases hurow : u.1.2 = a.2 - 1
  · obtain ⟨hvu, _, _⟩ :=
      generalRectangleDualBottomRow_adj_neighbor a w h u.1.1 u v
        (by
          exact congrArg (fun y : ℤ => (u.1.1, y)) hurow) hAdj
    have hcoords : v.1 = (u.1.1, a.2) := hvu
    apply (BoundaryCondition.wired_rel _ _ _).2
    left
    apply Subtype.ext
    apply Subtype.ext
    simp [generalRectangleDualBottomCoreRetraction_val, hcoords, hurow]
  · by_cases hvrow : v.1.2 = a.2 - 1
    · obtain ⟨huv, _, _⟩ :=
        generalRectangleDualBottomRow_adj_neighbor a w h v.1.1 v u
          (by
            exact congrArg (fun y : ℤ => (v.1.1, y)) hvrow) hAdj.symm
      have hcoords : u.1 = (v.1.1, a.2) := huv
      apply (BoundaryCondition.wired_rel _ _ _).2
      left
      apply Subtype.ext
      apply Subtype.ext
      simp [generalRectangleDualBottomCoreRetraction_val, hcoords, hvrow]
    · have huCore : a.2 ≤ u.1.2 := by
        have hlo := u.2
        change u.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hlo
        rw [mem_latticeRectangle] at hlo
        rcases hlo with ⟨_, ⟨hlo, _⟩⟩
        omega
      have hvCore : a.2 ≤ v.1.2 := by
        have hlo := v.2
        change v.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hlo
        rw [mem_latticeRectangle] at hlo
        rcases hlo with ⟨_, ⟨hlo, _⟩⟩
        omega
      let cu : generalRectangleDualBottomCoreVertex a w h := ⟨u, huCore⟩
      let cv : generalRectangleDualBottomCoreVertex a w h := ⟨v, hvCore⟩
      have hG : (generalRectangleDualBottomCoreGraph a w h).Adj cu cv := by
        change (rectangleDualGraph a w h).Adj u v
        exact hAdj
      have hmap : (((generalRectangleDualBottomCoreGraph a w h).map
          (generalRectangleDualBottomCoreInclusion a w h))).Adj
          (generalRectangleDualBottomCoreInclusion a w h cu)
          (generalRectangleDualBottomCoreInclusion a w h cv) :=
        (SimpleGraph.map_adj _ _ _ _).2 ⟨cu, cv, hG, rfl, rfl⟩
      have hmem : s((generalRectangleDualBottomCoreInclusion a w h cu),
          (generalRectangleDualBottomCoreInclusion a w h cv)) ∈
          ((generalRectangleDualBottomCoreGraph a w h).map
            (generalRectangleDualBottomCoreInclusion a w h)).edgeSet :=
        ((generalRectangleDualBottomCoreGraph a w h).map
          (generalRectangleDualBottomCoreInclusion a w h)).mem_edgeSet.mpr hmap
      have hpair : s((generalRectangleDualBottomCoreInclusion a w h cu),
          (generalRectangleDualBottomCoreInclusion a w h cv)) = e.1 := by
        simpa [generalRectangleDualBottomCoreInclusion, cu, cv] using heuv.symm
      exact False.elim (hnotmap (hpair ▸ hmem))

/-- For every actual removed-edge state, clamping the free bottom leaves
pulls the frozen boundary back to exactly the wired top and side partition on
the retained true-dual core. -/
theorem generalRectangleDualBottomCoreBoundary_retraction
    (a : LatticeVertex) (w h : ℕ)
    (K : RemovedConfiguration (rectangleDualGraph a w h)
      (subgraphRemovedEdges
        ((generalRectangleDualBottomCoreGraph a w h).map
          (generalRectangleDualBottomCoreInclusion a w h))
        (rectangleDualGraph a w h))) :
    (isolatedExtensionPullbackBoundary
      (generalRectangleDualBottomCoreInclusion a w h)
      (frozenBoundary
        (BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h))
        K.val)).partition =
      (BoundaryCondition.wired
        {u : generalRectangleDualBottomCoreVertex a w h |
          (generalRectangleDualBottomCoreInclusion a w h u) ∈
            generalRectangleDualBottomCollarInnerThreeSides a w h}).partition := by
  classical
  let f := generalRectangleDualBottomCoreInclusion a w h
  let r := generalRectangleDualBottomCoreRetraction a w h
  let ξ := BoundaryCondition.wired (generalRectangleDualBottomCollarInnerThreeSides a w h)
  let η := BoundaryCondition.wired
    {u : generalRectangleDualBottomCoreVertex a w h |
      f u ∈ generalRectangleDualBottomCollarInnerThreeSides a w h}
  have hξ : ∀ x y, ξ.partition.r x y → η.partition.r (r x) (r y) := by
    intro x y hxy
    rw [BoundaryCondition.wired_rel] at hxy
    rcases hxy with heq | ⟨hx, hy⟩
    · apply (BoundaryCondition.wired_rel _ _ _).2
      exact Or.inl (congrArg r heq)
    · apply (BoundaryCondition.wired_rel _ _ _).2
      exact Or.inr ⟨coreRetraction_boundary_mem a w h x hx,
        coreRetraction_boundary_mem a w h y hy⟩
  have hopen : ∀ x y, (openGraph (rectangleDualGraph a w h) K.val).Adj x y →
      η.partition.r (r x) (r y) := by
    intro x y hxy
    exact coreRetraction_openEdge_preserves_boundary a w h K hxy
  have hlower : η.partition ≤ Setoid.comap f ξ.partition := by
    intro u v huv
    change (BoundaryCondition.wired
      {u : generalRectangleDualBottomCoreVertex a w h |
        f u ∈ generalRectangleDualBottomCollarInnerThreeSides a w h}).partition.r u v at huv
    rw [BoundaryCondition.wired_rel] at huv
    change (BoundaryCondition.wired
      (generalRectangleDualBottomCollarInnerThreeSides a w h)).partition.r (f u) (f v)
    rw [BoundaryCondition.wired_rel]
    rcases huv with heq | ⟨hu, hv⟩
    · exact Or.inl (congrArg f heq)
    · exact Or.inr ⟨hu, hv⟩
  exact isolatedExtensionPullback_frozenBoundary_partition_eq_of_retraction
    f r (by intro u; exact generalRectangleDualBottomCoreRetraction_inclusion a w h u)
    ξ K.val η.partition hξ hopen hlower

end
end PottsContinuity.FKC.FiniteFK
