-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingClusterBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterComplement
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance wiredAvoidingBoundaryEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance wiredAvoidingBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Every endpoint of an open edge recorded by the masked-cluster reveal is
in that cluster or in the forbidden set. -/
theorem wiredAvoidingRecord_openEdge_endpoint_mem
    (W : Set V) (S : Finset V) (A₀ : Configuration G)
    {e : G.edgeSet} (he : e ∈
      (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀).val)
    {u : V} (hu : u ∈ e.1) :
    u ∈ wiredAvoidingClusterSet G W S A₀ ∪ W := by
  classical
  have heA : e ∈ A₀ := (Finset.mem_inter.mp he).1
  have heReveal : e ∈ wiredAvoidingClusterReveal G W S A₀ :=
    (Finset.mem_inter.mp he).2
  rcases (wiredAvoidingClusterReveal_mem_iff W S A₀ e).mp heReveal with
    ⟨v, hv, hvC⟩
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.1
  have heq : e.1 = s(a,b) := by simpa using hab.symm
  have hAdj : G.Adj a b := by
    apply G.mem_edgeSet.mp
    rw [← heq]
    exact e.2
  have eab : (⟨s(a,b), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈ A₀ := by
    have heab : (⟨s(a,b), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      exact heq.symm
    simpa [heab] using heA
  have hOpen : (openGraph G A₀).Adj a b := by
    rw [openGraph_adj]
    exact ⟨⟨s(a,b), G.mem_edgeSet.mpr hAdj⟩, eab, rfl⟩
  have hv' : v = a ∨ v = b := by
    rw [← hab] at hv
    exact (Sym2.mem_iff').mp hv
  have hu' : u = a ∨ u = b := by
    rw [← hab] at hu
    exact (Sym2.mem_iff').mp hu
  have ha_or_b : a ∈ wiredAvoidingClusterSet G W S A₀ ∪ W ∧
      b ∈ wiredAvoidingClusterSet G W S A₀ ∪ W := by
    rcases hv' with rfl | rfl
    · constructor
      · exact Set.mem_union_left _ hvC
      · by_cases hbW : b ∈ W
        · exact Set.mem_union_right _ hbW
        · exact Set.mem_union_left _
            (wiredAvoidingClusterSet_openEdge_closed W S A₀ hvC hbW hOpen)
    · constructor
      · by_cases haW : a ∈ W
        · exact Set.mem_union_right _ haW
        · exact Set.mem_union_left _
            (wiredAvoidingClusterSet_openEdge_closed W S A₀ hvC haW hOpen.symm)
      · exact Set.mem_union_left _ hvC
  rcases hu' with rfl | rfl
  · exact ha_or_b.1
  · exact ha_or_b.2

/-- The frozen boundary after recording the masked cluster is supported by
original wiring together with the cluster and forbidden vertices. -/
theorem frozenWiredAvoidingClusterBoundary_le_wired_union
    (ξ : BoundaryCondition V) (W : Set V) (S : Finset V) (A₀ : Configuration G) :
    (frozenBoundary ξ
      (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀).val).partition ≤
      (BoundaryCondition.wired
        (ξ.boundary ∪ (wiredAvoidingClusterSet G W S A₀ ∪ W))).partition := by
  change componentSetoid G ξ
      (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀).val ≤ _
  exact componentSetoid_le_wired_union_of_edge_endpoints ξ _ _
    (fun {e} he {u} hu => wiredAvoidingRecord_openEdge_endpoint_mem W S A₀ he hu)

/-- On the induced complement, the frozen partition is dominated by wiring the
pulled-back original boundary and forbidden set. -/
theorem isolatedPullback_frozenWiredAvoidingClusterBoundary_le_wired_union
    (ξ : BoundaryCondition V) (W : Set V) (S : Finset V) (A₀ : Configuration G) :
    (isolatedExtensionPullbackBoundary
      (wiredAvoidingComplementEmbedding G W S A₀)
      (frozenBoundary ξ
        (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀).val)).partition ≤
      (BoundaryCondition.wired
        ((wiredAvoidingComplementEmbedding G W S A₀) ⁻¹' (ξ.boundary ∪ W))).partition := by
  intro u v huv
  have hcomap := (Setoid.comap_rel _ _ _ _).mp huv
  have hbound := frozenWiredAvoidingClusterBoundary_le_wired_union ξ W S A₀ hcomap
  rcases (BoundaryCondition.wired_rel _ _ _).mp hbound with heq | ⟨huD, hvD⟩
  · exact (BoundaryCondition.wired_rel _ _ _).mpr
      (Or.inl ((wiredAvoidingComplementEmbedding G W S A₀).injective heq))
  · have huOut : u.val ∉ wiredAvoidingClusterSet G W S A₀ := u.property
    have hvOut : v.val ∉ wiredAvoidingClusterSet G W S A₀ := v.property
    have huB : u ∈ (wiredAvoidingComplementEmbedding G W S A₀) ⁻¹' (ξ.boundary ∪ W) := by
      change (wiredAvoidingComplementEmbedding G W S A₀) u ∈ ξ.boundary ∪ W
      rcases ((Set.mem_union _ _ _).mp huD) with huξ | huCW
      · exact Set.mem_union_left _ huξ
      · rcases ((Set.mem_union _ _ _).mp huCW) with huC | huW
        · exact (huOut huC).elim
        · exact Set.mem_union_right _ huW
    have hvB : v ∈ (wiredAvoidingComplementEmbedding G W S A₀) ⁻¹' (ξ.boundary ∪ W) := by
      change (wiredAvoidingComplementEmbedding G W S A₀) v ∈ ξ.boundary ∪ W
      rcases ((Set.mem_union _ _ _).mp hvD) with hvξ | hvCW
      · exact Set.mem_union_left _ hvξ
      · rcases ((Set.mem_union _ _ _).mp hvCW) with hvC | hvW
        · exact (hvOut hvC).elim
        · exact Set.mem_union_right _ hvW
    exact (BoundaryCondition.wired_rel _ _ _).mpr (Or.inr ⟨huB, hvB⟩)

/-- If the original boundary already lies in the cluster or forbidden set, the
pulled-back frozen boundary is dominated by wiring only the forbidden set. -/
theorem isolatedPullback_frozenWiredAvoidingClusterBoundary_le_wired
    (ξ : BoundaryCondition V) (W : Set V) (S : Finset V) (A₀ : Configuration G)
    (hξ : ξ.boundary ⊆ wiredAvoidingClusterSet G W S A₀ ∪ W) :
    (isolatedExtensionPullbackBoundary
      (wiredAvoidingComplementEmbedding G W S A₀)
      (frozenBoundary ξ
        (revealRecordConfiguration G (wiredAvoidingClusterReveal G W S) A₀).val)).partition ≤
      (BoundaryCondition.wired
        ((wiredAvoidingComplementEmbedding G W S A₀) ⁻¹' W)).partition := by
  have hsets : (wiredAvoidingComplementEmbedding G W S A₀) ⁻¹'
      (ξ.boundary ∪ W) = (wiredAvoidingComplementEmbedding G W S A₀) ⁻¹' W := by
    ext u
    constructor
    · intro hu
      change (wiredAvoidingComplementEmbedding G W S A₀) u ∈ ξ.boundary ∪ W at hu
      rcases ((Set.mem_union _ _ _).mp hu) with huξ | huW
      · rcases ((Set.mem_union _ _ _).mp (hξ huξ)) with huC | huW'
        · exact (u.property huC).elim
        · exact huW'
      · exact huW
    · intro hu
      change (wiredAvoidingComplementEmbedding G W S A₀) u ∈ W at hu
      exact Set.mem_union_right _ hu
  rw [← hsets]
  exact isolatedPullback_frozenWiredAvoidingClusterBoundary_le_wired_union ξ W S A₀

end
end PottsContinuity.FKC.FiniteFK
