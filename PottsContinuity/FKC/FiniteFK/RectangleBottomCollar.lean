-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleBottomCollar.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.Rectangle

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

abbrev rectangleBottomCollarInnerGraph (n : ℕ) :=
  rectangleGraph (-(n : ℤ), 0) (2 * n) n

abbrev rectangleBottomCollarOuterGraph (n : ℕ) :=
  rectangleGraph (-(n : ℤ), -1) (2 * n) (n + 1)

abbrev rectangleBottomCollarInnerVertex (n : ℕ) :=
  RectangleVertex (-(n : ℤ), 0) (2 * n) n

abbrev rectangleBottomCollarOuterVertex (n : ℕ) :=
  RectangleVertex (-(n : ℤ), -1) (2 * n) (n + 1)

def rectangleBottomCollarBottom (n : ℕ) : Set (rectangleBottomCollarInnerVertex n) :=
  {v | v.1.2 = 0}

lemma rectangleBottomCollar_subset (n : ℕ) :
    latticeRectangle (-(n : ℤ), 0) (2 * n) n ⊆
      latticeRectangle (-(n : ℤ), -1) (2 * n) (n + 1) := by
  intro z hz
  rw [mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hx1,hx2⟩,⟨hy1,hy2⟩⟩
  exact ⟨⟨hx1,hx2⟩,⟨by omega, by omega⟩⟩

def rectangleBottomCollarEmbedding (n : ℕ) :
    rectangleBottomCollarInnerVertex n ↪ rectangleBottomCollarOuterVertex n :=
  rectangleVertexEmbedding (rectangleBottomCollar_subset n)

lemma rectangleBottomCollarEmbedding_val (n : ℕ)
    (v : rectangleBottomCollarInnerVertex n) :
    (rectangleBottomCollarEmbedding n v).val = v.val := rfl

local instance rectangleBottomCollarInnerFintype (n : ℕ) :
    Fintype (rectangleBottomCollarInnerGraph n).edgeSet := Fintype.ofFinite _
local instance rectangleBottomCollarInnerFinite (n : ℕ) :
    Finite (rectangleBottomCollarInnerVertex n) := Finite.of_fintype _
local instance rectangleBottomCollarInnerDecidableEq (n : ℕ) :
    DecidableEq (rectangleBottomCollarInnerGraph n).edgeSet := Classical.decEq _
local instance rectangleBottomCollarOuterFintype (n : ℕ) :
    Fintype (rectangleBottomCollarOuterGraph n).edgeSet := Fintype.ofFinite _
local instance rectangleBottomCollarOuterFinite (n : ℕ) :
    Finite (rectangleBottomCollarOuterVertex n) := Finite.of_fintype _
local instance rectangleBottomCollarOuterDecidableEq (n : ℕ) :
    DecidableEq (rectangleBottomCollarOuterGraph n).edgeSet := Classical.decEq _

def rectangleBottomCollarRemoved (n : ℕ) : Configuration (rectangleBottomCollarOuterGraph n) :=
  subgraphRemovedEdges
    ((rectangleBottomCollarInnerGraph n).map (rectangleBottomCollarEmbedding n))
    (rectangleBottomCollarOuterGraph n)

def rectangleBottomCollarState (n : ℕ) :
    RemovedConfiguration (rectangleBottomCollarOuterGraph n)
      (rectangleBottomCollarRemoved n) :=
  ⟨rectangleBottomCollarRemoved n, Finset.Subset.rfl⟩

def rectangleBottomCollarExteriorOrBottom (n : ℕ) :
    Set (rectangleBottomCollarOuterVertex n) :=
  (Set.range (rectangleBottomCollarEmbedding n))ᶜ ∪
    (rectangleBottomCollarEmbedding n) '' rectangleBottomCollarBottom n

theorem rectangleBottomCollar_removed_edge_endpoints (n : ℕ) :
    ∀ ⦃e : (rectangleBottomCollarOuterGraph n).edgeSet⦄,
      e ∈ (rectangleBottomCollarState n).val →
      ∀ ⦃x : rectangleBottomCollarOuterVertex n⦄, x ∈ e.1 →
        x ∈ rectangleBottomCollarExteriorOrBottom n := by
  classical
  intro e he x hx
  have heR : e ∈ subgraphRemovedEdges
      ((rectangleBottomCollarInnerGraph n).map (rectangleBottomCollarEmbedding n))
      (rectangleBottomCollarOuterGraph n) := by
    simpa [rectangleBottomCollarState, rectangleBottomCollarRemoved] using he
  have henot : e.val ∉
      ((rectangleBottomCollarInnerGraph n).map (rectangleBottomCollarEmbedding n)).edgeSet :=
    (mem_subgraphRemovedEdges _).mp heR
  obtain ⟨ab,hab⟩ := Sym2.mk_surjective e.val
  rcases ab with ⟨a,b⟩
  have heval : e.val = s(a,b) := hab.symm
  have habAdj : (rectangleBottomCollarOuterGraph n).Adj a b := by
    apply (rectangleBottomCollarOuterGraph n).mem_edgeSet.mp
    rw [← heval]
    exact e.property
  have hxAB : x = a ∨ x = b := by
    rw [heval] at hx
    exact (Sym2.mem_iff').mp hx
  have hnotboth : ¬ (a ∈ Set.range (rectangleBottomCollarEmbedding n) ∧
      b ∈ Set.range (rectangleBottomCollarEmbedding n)) := by
    rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    have hadj : (rectangleBottomCollarOuterGraph n).Adj
        ((rectangleBottomCollarEmbedding n) u) ((rectangleBottomCollarEmbedding n) v) := by
      simpa [hu,hv] using habAdj
    have hsq : squareLattice.Adj u.val v.val := by
      change squareLattice.Adj ((rectangleBottomCollarEmbedding n u).val)
        ((rectangleBottomCollarEmbedding n v).val)
      exact (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
    have hinner : (rectangleBottomCollarInnerGraph n).Adj u v :=
      (rectangleGraph_adj_iff _ _ _ _ _).2 hsq
    have hmap : ((rectangleBottomCollarInnerGraph n).map
        (rectangleBottomCollarEmbedding n)).Adj a b :=
      (SimpleGraph.map_adj _ _ _ _).2 ⟨u,v,hinner,hu,hv⟩
    have hmem : s(a,b) ∈
        ((rectangleBottomCollarInnerGraph n).map
          (rectangleBottomCollarEmbedding n)).edgeSet :=
      (SimpleGraph.mem_edgeSet _).2 hmap
    exact henot (heval ▸ hmem)
  have hinside_endpoint (u : rectangleBottomCollarInnerVertex n)
      (z y : rectangleBottomCollarOuterVertex n)
      (hzu : (rectangleBottomCollarEmbedding n) u = z)
      (hynot : y ∉ Set.range (rectangleBottomCollarEmbedding n))
      (hadj : (rectangleBottomCollarOuterGraph n).Adj z y) :
      u ∈ rectangleBottomCollarBottom n := by
    have hsquare : squareLattice.Adj z.val y.val :=
      (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
    have hzmem := u.property
    rw [mem_latticeRectangle] at hzmem
    have hxmem := y.property
    rw [mem_latticeRectangle] at hxmem
    have hxinner : (0 ≤ y.val.2 ∧ y.val.2 ≤ n) →
        y ∈ Set.range (rectangleBottomCollarEmbedding n) := by
      intro hy
      refine ⟨⟨y.val, ?_⟩, ?_⟩
      · rw [mem_latticeRectangle]
        exact ⟨⟨hxmem.1.1,hxmem.1.2⟩, by simpa using hy⟩
      · apply Subtype.ext
        rfl
    have hy_not : ¬ (0 ≤ y.val.2 ∧ y.val.2 ≤ n) := fun hy => hynot (hxinner hy)
    have hval : z.val = u.val := by
      have hh := congrArg (fun t : rectangleBottomCollarOuterVertex n => t.val) hzu
      change u.val = z.val at hh
      exact hh.symm
    rw [hval] at hsquare
    rw [squareLattice_adj_iff] at hsquare
    rcases hsquare with ⟨_, hxy⟩ | ⟨_, hxy | hxy⟩
    · exact False.elim (hy_not (by omega))
    · exact False.elim (hy_not (by omega))
    · change u.val.2 = 0
      omega
  rcases hxAB with hxa | hxb
  · rw [hxa]
    by_cases ha : a ∈ Set.range (rectangleBottomCollarEmbedding n)
    · obtain ⟨u,hu⟩ := ha
      have hb : b ∉ Set.range (rectangleBottomCollarEmbedding n) := fun hb =>
        hnotboth ⟨⟨u,hu⟩,hb⟩
      right
      refine ⟨u, hinside_endpoint u a b hu hb ?_, hu⟩
      simpa [hu] using habAdj
    · exact Or.inl ha
  · rw [hxb]
    by_cases hb : b ∈ Set.range (rectangleBottomCollarEmbedding n)
    · obtain ⟨u,hu⟩ := hb
      have ha : a ∉ Set.range (rectangleBottomCollarEmbedding n) := fun ha =>
        hnotboth ⟨ha,⟨u,hu⟩⟩
      right
      refine ⟨u, hinside_endpoint u b a hu ha ?_, hu⟩
      simpa [hu] using habAdj.symm
    · exact Or.inl hb

def rectangleBottomCollarRowVertex (n i : ℕ) (hi : i ≤ 2 * n) :
    rectangleBottomCollarOuterVertex n :=
  ⟨(-(n : ℤ) + (i : ℤ), -1), by
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩

lemma rectangleBottomCollar_row_adj (n i : ℕ) (hi : i < 2 * n) :
    (rectangleBottomCollarOuterGraph n).Adj
      (rectangleBottomCollarRowVertex n i (by omega))
      (rectangleBottomCollarRowVertex n (i + 1) (by omega)) := by
  rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
  left
  constructor
  · left
    simp only [rectangleBottomCollarRowVertex, Subtype.coe_mk, Nat.cast_add, Nat.cast_one]
    ring
  · simp [rectangleBottomCollarRowVertex]

private theorem rectangleBottomCollar_adj_edge_removed (n : ℕ)
    {u v : rectangleBottomCollarOuterVertex n}
    (hu : u ∉ Set.range (rectangleBottomCollarEmbedding n))
    (hadj : (rectangleBottomCollarOuterGraph n).Adj u v) :
    (⟨s(u,v), (rectangleBottomCollarOuterGraph n).mem_edgeSet.mpr hadj⟩ :
      (rectangleBottomCollarOuterGraph n).edgeSet) ∈ rectangleBottomCollarRemoved n := by
  rw [rectangleBottomCollarRemoved, mem_subgraphRemovedEdges]
  intro hmem
  have hmap : ((rectangleBottomCollarInnerGraph n).map
      (rectangleBottomCollarEmbedding n)).Adj u v :=
    ((rectangleBottomCollarInnerGraph n).map
      (rectangleBottomCollarEmbedding n)).mem_edgeSet.mp hmem
  obtain ⟨x,y,hxy,hxu,hyv⟩ :=
    (SimpleGraph.map_adj (rectangleBottomCollarEmbedding n)
      (rectangleBottomCollarInnerGraph n) u v).mp hmap
  exact hu ⟨x,hxu⟩

private theorem rectangleBottomCollar_row_step_connected (n i : ℕ) (hi : i < 2*n) :
    ActualConnected (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarState n).val
      (rectangleBottomCollarRowVertex n i (by omega))
      (rectangleBottomCollarRowVertex n (i+1) (by omega)) := by
  apply actualConnected_of_adj
  rw [openGraph_adj]
  refine ⟨⟨s(_, _), ?_⟩, ?_, rfl⟩
  · exact (rectangleBottomCollarOuterGraph n).mem_edgeSet.mpr
      (rectangleBottomCollar_row_adj n i hi)
  · exact rectangleBottomCollar_adj_edge_removed n
      (by
        intro h
        obtain ⟨v,hv⟩ := h
        have hvy := congrArg (fun z : rectangleBottomCollarOuterVertex n => z.val.2) hv
        change v.val.2 = -1 at hvy
        have hpos := ((mem_latticeRectangle _ _ _ _).mp v.property).2.1
        omega)
      (rectangleBottomCollar_row_adj n i hi)

private theorem rectangleBottomCollar_row_reachable_zero (n : ℕ) :
    ∀ i (hi : i ≤ 2*n),
      ActualConnected (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarState n).val
        (rectangleBottomCollarRowVertex n 0 (by omega))
        (rectangleBottomCollarRowVertex n i hi) := by
  intro i
  induction i with
  | zero => intro hi; exact SimpleGraph.Reachable.refl _
  | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep := rectangleBottomCollar_row_step_connected n i (by omega)
      exact hprev.trans hstep

def rectangleBottomCollarOffset (n : ℕ) (v : rectangleBottomCollarInnerVertex n) : ℕ :=
  (v.val.1 + (n : ℤ)).toNat

lemma rectangleBottomCollarOffset_le (n : ℕ)
    (v : rectangleBottomCollarInnerVertex n) : rectangleBottomCollarOffset n v ≤ 2*n := by
  have hv := (mem_latticeRectangle _ _ _ _).mp v.property
  have hn : 0 ≤ v.val.1 + (n : ℤ) := by omega
  have hbound : v.val.1 + (n : ℤ) ≤ (2*n : ℤ) := by omega
  exact Int.toNat_le.mpr hbound

lemma rectangleBottomCollarOffset_cast (n : ℕ)
    (v : rectangleBottomCollarInnerVertex n) :
    ((rectangleBottomCollarOffset n v : ℕ) : ℤ) = v.val.1 + (n : ℤ) := by
  exact Int.toNat_of_nonneg (by
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    omega)

private theorem rectangleBottomCollar_inner_to_row (n : ℕ)
    (v : rectangleBottomCollarInnerVertex n) (hv : v.val.2 = 0) :
    ActualConnected (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarState n).val
      ((rectangleBottomCollarEmbedding n) v)
      (rectangleBottomCollarRowVertex n (rectangleBottomCollarOffset n v)
        (rectangleBottomCollarOffset_le n v)) := by
  have hadj : (rectangleBottomCollarOuterGraph n).Adj
      ((rectangleBottomCollarEmbedding n) v)
      (rectangleBottomCollarRowVertex n (rectangleBottomCollarOffset n v)
        (rectangleBottomCollarOffset_le n v)) := by
    rw [rectangleGraph_adj_iff]
    rw [rectangleBottomCollarEmbedding_val, squareLattice_adj_iff]
    right
    constructor
    · have hx : -(n : ℤ) + (rectangleBottomCollarOffset n v : ℤ) = v.val.1 := by
        rw [rectangleBottomCollarOffset_cast]
        omega
      simp only [rectangleBottomCollarRowVertex, Subtype.coe_mk]
      exact hx.symm
    · right
      simp only [rectangleBottomCollarRowVertex, Subtype.coe_mk]
      omega
  have hadj' := hadj.symm
  apply SimpleGraph.Reachable.symm
  apply actualConnected_of_adj
  rw [openGraph_adj]
  refine ⟨⟨s(_, _), (rectangleBottomCollarOuterGraph n).mem_edgeSet.mpr hadj'⟩, ?_, rfl⟩
  apply rectangleBottomCollar_adj_edge_removed n
  · intro hrange
    obtain ⟨u, hu⟩ := hrange
    have hcoord := congrArg (fun z : rectangleBottomCollarOuterVertex n => z.val.2) hu
    change (rectangleBottomCollarEmbedding n u).val.2 = -1 at hcoord
    rw [rectangleBottomCollarEmbedding_val] at hcoord
    have huinner := (mem_latticeRectangle _ _ _ _).mp u.property
    omega
  · exact hadj'

private theorem rectangleBottomCollar_bottom_connected (n : ℕ)
    (u v : rectangleBottomCollarInnerVertex n)
    (hu : u.val.2 = 0) (hv : v.val.2 = 0) :
    ActualConnected (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarState n).val
      ((rectangleBottomCollarEmbedding n) u) ((rectangleBottomCollarEmbedding n) v) := by
  have hurow := rectangleBottomCollar_inner_to_row n u hu
  have hvrow := rectangleBottomCollar_inner_to_row n v hv
  have hrootu := rectangleBottomCollar_row_reachable_zero n
    (rectangleBottomCollarOffset n u) (rectangleBottomCollarOffset_le n u)
  have hrootv := rectangleBottomCollar_row_reachable_zero n
    (rectangleBottomCollarOffset n v) (rectangleBottomCollarOffset_le n v)
  have hrows : ActualConnected (rectangleBottomCollarOuterGraph n)
      (rectangleBottomCollarState n).val
      (rectangleBottomCollarRowVertex n (rectangleBottomCollarOffset n u)
        (rectangleBottomCollarOffset_le n u))
      (rectangleBottomCollarRowVertex n (rectangleBottomCollarOffset n v)
        (rectangleBottomCollarOffset_le n v)) := hrootu.symm.trans hrootv
  exact hurow.trans (hrows.trans hvrow.symm)

lemma rectangleBottomCollar_mem_exteriorOrBottom_iff (n : ℕ)
    (v : rectangleBottomCollarInnerVertex n) :
    rectangleBottomCollarEmbedding n v ∈ rectangleBottomCollarExteriorOrBottom n ↔
      v ∈ rectangleBottomCollarBottom n := by
  change (rectangleBottomCollarEmbedding n v ∉
        Set.range (rectangleBottomCollarEmbedding n) ∨
      ∃ u, u ∈ rectangleBottomCollarBottom n ∧
        rectangleBottomCollarEmbedding n u = rectangleBottomCollarEmbedding n v) ↔ _
  constructor
  · rintro (h | ⟨u, hu, huv⟩)
    · exact False.elim (h ⟨v, rfl⟩)
    · have : u = v := (rectangleBottomCollarEmbedding n).injective huv
      simpa [this] using hu
  · intro hv
    exact Or.inr ⟨v, hv, rfl⟩

theorem rectangleBottomCollar_frozen_partition_eq (n : ℕ) :
    (isolatedExtensionPullbackBoundary (rectangleBottomCollarEmbedding n)
      (frozenBoundary (BoundaryCondition.free (∅ : Set (rectangleBottomCollarOuterVertex n)))
        (rectangleBottomCollarState n).val)).partition =
      (BoundaryCondition.wired (rectangleBottomCollarBottom n)).partition := by
  let ξ := BoundaryCondition.free (∅ : Set (rectangleBottomCollarOuterVertex n))
  let D := rectangleBottomCollarExteriorOrBottom n
  have hwhole : componentSetoid (rectangleBottomCollarOuterGraph n) ξ
      (rectangleBottomCollarState n).val ≤
      (BoundaryCondition.wired D).partition := by
    simpa [ξ, D, rectangleBottomCollarExteriorOrBottom, BoundaryCondition.free,
      Set.empty_union] using
      (componentSetoid_le_wired_union_of_edge_endpoints ξ D
        (rectangleBottomCollarState n).val
        (rectangleBottomCollar_removed_edge_endpoints n))
  ext u v
  change (componentSetoid (rectangleBottomCollarOuterGraph n) ξ
      (rectangleBottomCollarState n).val).r
        ((rectangleBottomCollarEmbedding n) u) ((rectangleBottomCollarEmbedding n) v) ↔
    (BoundaryCondition.wired (rectangleBottomCollarBottom n)).partition.r u v
  constructor
  · intro huv
    have hD := hwhole huv
    rw [BoundaryCondition.wired_rel] at hD
    rcases hD with heq | ⟨huD,hvD⟩
    · exact (BoundaryCondition.wired_rel _ _ _).mpr
        (Or.inl ((rectangleBottomCollarEmbedding n).injective heq))
    · exact (BoundaryCondition.wired_rel _ _ _).mpr
        (Or.inr ⟨(rectangleBottomCollar_mem_exteriorOrBottom_iff n u).mp huD,
          (rectangleBottomCollar_mem_exteriorOrBottom_iff n v).mp hvD⟩)
  · intro huv
    rw [BoundaryCondition.wired_rel] at huv
    rcases huv with heq | ⟨hu,hv⟩
    · subst v
      exact (componentSetoid (rectangleBottomCollarOuterGraph n) ξ
        (rectangleBottomCollarState n).val).refl _
    · exact actualConnected_component (rectangleBottomCollarOuterGraph n) ξ
        (rectangleBottomCollarState n).val
        (rectangleBottomCollar_bottom_connected n u v hu hv)

theorem law_eq_of_boundary_partition_eq {V : Type*} [Finite V]
    {G : SimpleGraph V} (q : ClusterWeight) (ξ η : BoundaryCondition V)
    (hξη : ξ.partition = η.partition) : law G q ξ = law G q η := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : DecidableEq G.edgeSet := Classical.decEq _
  have hcount (A : Configuration G) :
      componentCount G ξ A = componentCount G η A := by
    simp only [componentCount, componentSetoid]
    rw [hξη]
  have hw (A : Configuration G) : weight G q ξ A = weight G q η A := by
    simp only [weight, hcount A]
  have hpartition : partitionFunction G q ξ = partitionFunction G q η := by
    unfold partitionFunction FiniteProbability.partition
    congr 1
    funext A
    exact hw A
  ext A
  rw [law_apply, law_apply, configurationProbability, configurationProbability,
    hw A, hpartition]

theorem rectangleBottomCollar_conditional_law_map (n : ℕ) (q : ClusterWeight) :
    (((law (rectangleBottomCollarOuterGraph n) q
        (BoundaryCondition.free (∅ : Set (rectangleBottomCollarOuterVertex n)))).filter
      (frozenStateEvent (rectangleBottomCollarRemoved n) (rectangleBottomCollarState n))
      (frozenStateEvent_support q
        (BoundaryCondition.free (∅ : Set (rectangleBottomCollarOuterVertex n)))
        (rectangleBottomCollarRemoved n) (rectangleBottomCollarState n))).map
      (embeddedConfigurationRestriction (rectangleBottomCollarInnerGraph n)
        (rectangleBottomCollarOuterGraph n) (rectangleBottomCollarEmbedding n)
        (rectangleGraph_map_rectangleVertexEmbedding (rectangleBottomCollar_subset n)))) =
      law (rectangleBottomCollarInnerGraph n) q
        (BoundaryCondition.wired (rectangleBottomCollarBottom n)) := by
  let G := rectangleBottomCollarInnerGraph n
  let H := rectangleBottomCollarOuterGraph n
  let f := rectangleBottomCollarEmbedding n
  have hGH : G.map f ≤ H :=
    rectangleGraph_map_rectangleVertexEmbedding (rectangleBottomCollar_subset n)
  change (((law H q (BoundaryCondition.free ∅)).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) (rectangleBottomCollarState n))
      (frozenStateEvent_support q (BoundaryCondition.free ∅)
        (subgraphRemovedEdges (G.map f) H) (rectangleBottomCollarState n))).map
      (embeddedConfigurationRestriction G H f hGH)) = law G q
        (BoundaryCondition.wired (rectangleBottomCollarBottom n))
  rw [law_filter_frozen_map_embeddedRestriction G H f hGH q
    (BoundaryCondition.free ∅) (rectangleBottomCollarState n)]
  exact law_eq_of_boundary_partition_eq q _ _ (rectangleBottomCollar_frozen_partition_eq n)


end
end PottsContinuity.FKC.FiniteFK
