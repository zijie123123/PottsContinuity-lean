-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleBottomCollarLaw.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleBottomCollar

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

local instance rectangleArbitraryBottomCollarInnerEdgeFintype (a : LatticeVertex)
    (w h : ℕ) : Fintype (rectangleArbitraryBottomCollarInnerGraph a w h).edgeSet :=
  Fintype.ofFinite _
local instance rectangleArbitraryBottomCollarOuterEdgeFintype (a : LatticeVertex)
    (w h : ℕ) : Fintype (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet :=
  Fintype.ofFinite _
local instance rectangleArbitraryBottomCollarOuterFinite (a : LatticeVertex)
    (w h : ℕ) : Finite (rectangleArbitraryBottomCollarOuterVertex a w h) :=
  Finite.of_fintype _
local instance rectangleArbitraryBottomCollarLawOuterEdgeDecidableEq (a : LatticeVertex)
    (w h : ℕ) : DecidableEq (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet :=
  Classical.decEq _

 theorem rectangleArbitraryBottomCollar_map_le (a : LatticeVertex) (w h : ℕ) :
    (rectangleArbitraryBottomCollarInnerGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h) ≤
      rectangleArbitraryBottomCollarOuterGraph a w h := by
  exact rectangleGraph_map_rectangleVertexEmbedding
    (rectangleArbitraryBottomCollar_subset a w h)

private theorem rectangleArbitraryBottomCollar_adj_edge_removed (a : LatticeVertex)
    (w h : ℕ) {u v : rectangleArbitraryBottomCollarOuterVertex a w h}
    (hu : u ∉ Set.range (rectangleArbitraryBottomCollarEmbedding a w h))
    (hadj : (rectangleArbitraryBottomCollarOuterGraph a w h).Adj u v) :
    (⟨s(u,v), (rectangleArbitraryBottomCollarOuterGraph a w h).mem_edgeSet.mpr hadj⟩ :
      (rectangleArbitraryBottomCollarOuterGraph a w h).edgeSet) ∈
      rectangleArbitraryBottomCollarRemoved a w h := by
  rw [rectangleArbitraryBottomCollarRemoved, mem_subgraphRemovedEdges]
  intro hmem
  have hmap : ((rectangleArbitraryBottomCollarInnerGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h)).Adj u v :=
    ((rectangleArbitraryBottomCollarInnerGraph a w h).map
      (rectangleArbitraryBottomCollarEmbedding a w h)).mem_edgeSet.mp hmem
  obtain ⟨x,y,hxy,hxu,hyv⟩ :=
    (SimpleGraph.map_adj (rectangleArbitraryBottomCollarEmbedding a w h)
      (rectangleArbitraryBottomCollarInnerGraph a w h) u v).mp hmap
  exact hu ⟨x,hxu⟩

def rectangleArbitraryBottomCollarRowVertex (a : LatticeVertex) (w h i : ℕ)
    (hi : i ≤ w) : rectangleArbitraryBottomCollarOuterVertex a w h :=
  ⟨(a.1 + (i : ℤ), a.2 - 1), by
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · constructor <;> omega⟩

@[simp] theorem rectangleArbitraryBottomCollarRowVertex_val (a : LatticeVertex)
    (w h i : ℕ) (hi : i ≤ w) :
    (rectangleArbitraryBottomCollarRowVertex a w h i hi).val =
      (a.1 + (i : ℤ), a.2 - 1) := rfl

private theorem rectangleArbitraryBottomCollar_row_adj (a : LatticeVertex) (w h i : ℕ)
    (hi : i < w) :
    (rectangleArbitraryBottomCollarOuterGraph a w h).Adj
      (rectangleArbitraryBottomCollarRowVertex a w h i (by omega))
      (rectangleArbitraryBottomCollarRowVertex a w h (i + 1) (by omega)) := by
  rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
  left
  constructor
  · simp only [rectangleArbitraryBottomCollarRowVertex, Subtype.coe_mk,
      Nat.cast_add, Nat.cast_one]
    omega
  · simp [rectangleArbitraryBottomCollarRowVertex]

private theorem rectangleArbitraryBottomCollar_row_step_connected
    (a : LatticeVertex) (w h i : ℕ) (hi : i < w) :
    ActualConnected (rectangleArbitraryBottomCollarOuterGraph a w h)
      (rectangleArbitraryBottomCollarState a w h).val
      (rectangleArbitraryBottomCollarRowVertex a w h i (by omega))
      (rectangleArbitraryBottomCollarRowVertex a w h (i + 1) (by omega)) := by
  apply actualConnected_of_adj
  rw [openGraph_adj]
  refine ⟨⟨s(_, _), ?_⟩, ?_, rfl⟩
  · exact (rectangleArbitraryBottomCollarOuterGraph a w h).mem_edgeSet.mpr
      (rectangleArbitraryBottomCollar_row_adj a w h i hi)
  · apply rectangleArbitraryBottomCollar_adj_edge_removed a w h
    · intro hrange
      obtain ⟨v,hv⟩ := hrange
      have hvy := congrArg
        (fun z : rectangleArbitraryBottomCollarOuterVertex a w h => z.val.2) hv
      change (rectangleArbitraryBottomCollarEmbedding a w h v).val.2 = a.2 - 1 at hvy
      rw [rectangleArbitraryBottomCollarEmbedding_val] at hvy
      have hpos := ((mem_latticeRectangle _ _ _ _).mp v.property).2.1
      omega
    · exact rectangleArbitraryBottomCollar_row_adj a w h i hi

private theorem rectangleArbitraryBottomCollar_row_reachable_zero
    (a : LatticeVertex) (w h : ℕ) :
    ∀ i (hi : i ≤ w),
      ActualConnected (rectangleArbitraryBottomCollarOuterGraph a w h)
        (rectangleArbitraryBottomCollarState a w h).val
        (rectangleArbitraryBottomCollarRowVertex a w h 0 (by omega))
        (rectangleArbitraryBottomCollarRowVertex a w h i hi) := by
  intro i
  induction i with
  | zero => intro hi; exact SimpleGraph.Reachable.refl _
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep := rectangleArbitraryBottomCollar_row_step_connected a w h i (by omega)
      exact hprev.trans hstep

def rectangleArbitraryBottomCollarOffset (a : LatticeVertex) (w h : ℕ)
    (v : rectangleArbitraryBottomCollarInnerVertex a w h) : ℕ :=
  (v.val.1 - a.1).toNat

lemma rectangleArbitraryBottomCollarOffset_le (a : LatticeVertex) (w h : ℕ)
    (v : rectangleArbitraryBottomCollarInnerVertex a w h) :
    rectangleArbitraryBottomCollarOffset a w h v ≤ w := by
  have hv := (mem_latticeRectangle _ _ _ _).mp v.property
  have hn : 0 ≤ v.val.1 - a.1 := by omega
  have hbound : v.val.1 - a.1 ≤ (w : ℤ) := by omega
  exact Int.toNat_le.mpr hbound

lemma rectangleArbitraryBottomCollarOffset_cast (a : LatticeVertex) (w h : ℕ)
    (v : rectangleArbitraryBottomCollarInnerVertex a w h) :
    ((rectangleArbitraryBottomCollarOffset a w h v : ℕ) : ℤ) = v.val.1 - a.1 := by
  exact Int.toNat_of_nonneg (by
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    omega)

private theorem rectangleArbitraryBottomCollar_inner_to_row (a : LatticeVertex)
    (w h : ℕ) (v : rectangleArbitraryBottomCollarInnerVertex a w h)
    (hv : v.val.2 = a.2) :
    ActualConnected (rectangleArbitraryBottomCollarOuterGraph a w h)
      (rectangleArbitraryBottomCollarState a w h).val
      ((rectangleArbitraryBottomCollarEmbedding a w h) v)
      (rectangleArbitraryBottomCollarRowVertex a w h
        (rectangleArbitraryBottomCollarOffset a w h v)
        (rectangleArbitraryBottomCollarOffset_le a w h v)) := by
  have hadj : (rectangleArbitraryBottomCollarOuterGraph a w h).Adj
      ((rectangleArbitraryBottomCollarEmbedding a w h) v)
      (rectangleArbitraryBottomCollarRowVertex a w h
        (rectangleArbitraryBottomCollarOffset a w h v)
        (rectangleArbitraryBottomCollarOffset_le a w h v)) := by
    rw [rectangleGraph_adj_iff]
    rw [rectangleArbitraryBottomCollarEmbedding_val, squareLattice_adj_iff]
    right
    constructor
    · have hx : a.1 + (rectangleArbitraryBottomCollarOffset a w h v : ℤ) = v.val.1 := by
        rw [rectangleArbitraryBottomCollarOffset_cast]
        omega
      simp only [rectangleArbitraryBottomCollarRowVertex, Subtype.coe_mk]
      exact hx.symm
    · right
      simp only [rectangleArbitraryBottomCollarRowVertex, Subtype.coe_mk]
      omega
  have hadj' := hadj.symm
  apply SimpleGraph.Reachable.symm
  apply actualConnected_of_adj
  rw [openGraph_adj]
  refine ⟨⟨s(_, _), (rectangleArbitraryBottomCollarOuterGraph a w h).mem_edgeSet.mpr hadj'⟩,
    ?_, rfl⟩
  apply rectangleArbitraryBottomCollar_adj_edge_removed a w h
  · intro hrange
    obtain ⟨u,hu⟩ := hrange
    have hcoord := congrArg
      (fun z : rectangleArbitraryBottomCollarOuterVertex a w h => z.val.2) hu
    change (rectangleArbitraryBottomCollarEmbedding a w h u).val.2 = a.2 - 1 at hcoord
    rw [rectangleArbitraryBottomCollarEmbedding_val] at hcoord
    have huinner := (mem_latticeRectangle _ _ _ _).mp u.property
    omega
  · exact hadj'

theorem rectangleArbitraryBottomCollar_bottom_connected (a : LatticeVertex)
    (w h : ℕ) (u v : rectangleArbitraryBottomCollarInnerVertex a w h)
    (hu : u.val.2 = a.2) (hv : v.val.2 = a.2) :
    ActualConnected (rectangleArbitraryBottomCollarOuterGraph a w h)
      (rectangleArbitraryBottomCollarState a w h).val
      ((rectangleArbitraryBottomCollarEmbedding a w h) u)
      ((rectangleArbitraryBottomCollarEmbedding a w h) v) := by
  have hurow := rectangleArbitraryBottomCollar_inner_to_row a w h u hu
  have hvrow := rectangleArbitraryBottomCollar_inner_to_row a w h v hv
  have hrootu := rectangleArbitraryBottomCollar_row_reachable_zero a w h
    (rectangleArbitraryBottomCollarOffset a w h u)
    (rectangleArbitraryBottomCollarOffset_le a w h u)
  have hrootv := rectangleArbitraryBottomCollar_row_reachable_zero a w h
    (rectangleArbitraryBottomCollarOffset a w h v)
    (rectangleArbitraryBottomCollarOffset_le a w h v)
  have hrows : ActualConnected (rectangleArbitraryBottomCollarOuterGraph a w h)
      (rectangleArbitraryBottomCollarState a w h).val
      (rectangleArbitraryBottomCollarRowVertex a w h
        (rectangleArbitraryBottomCollarOffset a w h u)
        (rectangleArbitraryBottomCollarOffset_le a w h u))
      (rectangleArbitraryBottomCollarRowVertex a w h
        (rectangleArbitraryBottomCollarOffset a w h v)
        (rectangleArbitraryBottomCollarOffset_le a w h v)) := hrootu.symm.trans hrootv
  exact hurow.trans (hrows.trans hvrow.symm)

private theorem rectangleArbitraryBottomCollar_mem_exteriorOrBottom_iff
    (a : LatticeVertex) (w h : ℕ)
    (v : rectangleArbitraryBottomCollarInnerVertex a w h) :
    rectangleArbitraryBottomCollarEmbedding a w h v ∈
      rectangleArbitraryBottomCollarExteriorOrBottom a w h ↔
        v ∈ rectangleArbitraryBottomCollarBottom a w h := by
  change (rectangleArbitraryBottomCollarEmbedding a w h v ∉
        Set.range (rectangleArbitraryBottomCollarEmbedding a w h) ∨
      ∃ u, u ∈ rectangleArbitraryBottomCollarBottom a w h ∧
        rectangleArbitraryBottomCollarEmbedding a w h u =
          rectangleArbitraryBottomCollarEmbedding a w h v) ↔ _
  constructor
  · rintro (h | ⟨u, hu, huv⟩)
    · exact False.elim (h ⟨v, rfl⟩)
    · have huv' : u = v := (rectangleArbitraryBottomCollarEmbedding a w h).injective huv
      simpa [huv'] using hu
  · intro hv
    exact Or.inr ⟨v, hv, rfl⟩

theorem rectangleArbitraryBottomCollar_frozen_partition_eq (a : LatticeVertex)
    (w h : ℕ) :
    (isolatedExtensionPullbackBoundary (rectangleArbitraryBottomCollarEmbedding a w h)
      (frozenBoundary
        (BoundaryCondition.free (∅ : Set (rectangleArbitraryBottomCollarOuterVertex a w h)))
        (rectangleArbitraryBottomCollarState a w h).val)).partition =
      (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h)).partition := by
  let ξ := BoundaryCondition.free (∅ : Set (rectangleArbitraryBottomCollarOuterVertex a w h))
  let D := rectangleArbitraryBottomCollarExteriorOrBottom a w h
  have hwhole : componentSetoid (rectangleArbitraryBottomCollarOuterGraph a w h) ξ
      (rectangleArbitraryBottomCollarState a w h).val ≤ (BoundaryCondition.wired D).partition := by
    simpa [ξ, D, rectangleArbitraryBottomCollarExteriorOrBottom, BoundaryCondition.free,
      Set.empty_union] using
      (componentSetoid_le_wired_union_of_edge_endpoints ξ D
        (rectangleArbitraryBottomCollarState a w h).val
        (rectangleArbitraryBottomCollar_removed_edge_endpoints a w h))
  ext u v
  change (componentSetoid (rectangleArbitraryBottomCollarOuterGraph a w h) ξ
      (rectangleArbitraryBottomCollarState a w h).val).r
        ((rectangleArbitraryBottomCollarEmbedding a w h) u)
        ((rectangleArbitraryBottomCollarEmbedding a w h) v) ↔
    (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h)).partition.r u v
  constructor
  · intro huv
    have hD := hwhole huv
    rw [BoundaryCondition.wired_rel] at hD
    rcases hD with heq | ⟨huD,hvD⟩
    · exact (BoundaryCondition.wired_rel _ _ _).mpr
        (Or.inl ((rectangleArbitraryBottomCollarEmbedding a w h).injective heq))
    · exact (BoundaryCondition.wired_rel _ _ _).mpr
        (Or.inr ⟨(rectangleArbitraryBottomCollar_mem_exteriorOrBottom_iff a w h u).mp huD,
          (rectangleArbitraryBottomCollar_mem_exteriorOrBottom_iff a w h v).mp hvD⟩)
  · intro huv
    rw [BoundaryCondition.wired_rel] at huv
    rcases huv with heq | ⟨hu,hv⟩
    · subst v
      exact (componentSetoid (rectangleArbitraryBottomCollarOuterGraph a w h) ξ
        (rectangleArbitraryBottomCollarState a w h).val).refl _
    · exact actualConnected_component
        (rectangleArbitraryBottomCollarOuterGraph a w h) ξ
        (rectangleArbitraryBottomCollarState a w h).val
        (rectangleArbitraryBottomCollar_bottom_connected a w h u v hu hv)

theorem rectangleArbitraryBottomCollar_conditional_law_map
    (a : LatticeVertex) (w h : ℕ) (q : ClusterWeight) :
    (((law (rectangleArbitraryBottomCollarOuterGraph a w h) q
        (BoundaryCondition.free
          (∅ : Set (rectangleArbitraryBottomCollarOuterVertex a w h)))).filter
      (frozenStateEvent (rectangleArbitraryBottomCollarRemoved a w h)
        (rectangleArbitraryBottomCollarState a w h))
      (frozenStateEvent_support q
        (BoundaryCondition.free
          (∅ : Set (rectangleArbitraryBottomCollarOuterVertex a w h)))
        (rectangleArbitraryBottomCollarRemoved a w h)
        (rectangleArbitraryBottomCollarState a w h))).map
      (embeddedConfigurationRestriction
        (rectangleArbitraryBottomCollarInnerGraph a w h)
        (rectangleArbitraryBottomCollarOuterGraph a w h)
        (rectangleArbitraryBottomCollarEmbedding a w h)
        (rectangleArbitraryBottomCollar_map_le a w h))) =
      law (rectangleArbitraryBottomCollarInnerGraph a w h) q
        (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h)) := by
  let G := rectangleArbitraryBottomCollarInnerGraph a w h
  let H := rectangleArbitraryBottomCollarOuterGraph a w h
  let f := rectangleArbitraryBottomCollarEmbedding a w h
  have hGH : G.map f ≤ H := rectangleArbitraryBottomCollar_map_le a w h
  change (((law H q (BoundaryCondition.free ∅)).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H)
        (rectangleArbitraryBottomCollarState a w h))
      (frozenStateEvent_support q (BoundaryCondition.free ∅)
        (subgraphRemovedEdges (G.map f) H)
        (rectangleArbitraryBottomCollarState a w h))).map
      (embeddedConfigurationRestriction G H f hGH)) =
    law G q (BoundaryCondition.wired (rectangleArbitraryBottomCollarBottom a w h))
  rw [law_filter_frozen_map_embeddedRestriction G H f hGH q
    (BoundaryCondition.free ∅) (rectangleArbitraryBottomCollarState a w h)]
  exact law_eq_of_boundary_partition_eq q _ _
    (rectangleArbitraryBottomCollar_frozen_partition_eq a w h)

end
end PottsContinuity.FKC.FiniteFK
