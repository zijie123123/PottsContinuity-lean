-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredAvoidingRegionComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredAvoidingClusterBoundary
public import PottsContinuity.FKC.FiniteFK.EmbeddedBoundaryComparison
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance wiredAvoidingRegionVertexFintype : Fintype V := Fintype.ofFinite _

local instance wiredAvoidingRegionBigEdgeFintype (H : Set V) :
    Fintype (G.induce H).edgeSet := Fintype.ofFinite _
local instance wiredAvoidingRegionBigEdgeDecidableEq (H : Set V) :
    DecidableEq (G.induce H).edgeSet := Classical.decEq _

/-- All original vertices outside a finite region are the seeds for the
masked exploration used to compare its complement with that region. -/
def wiredAvoidingRegionSeeds (H : Set V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ H)

theorem wiredAvoidingRegionSeeds_mem (H : Set V) (v : V) :
    v ∈ wiredAvoidingRegionSeeds H ↔ v ∉ H := by
  classical
  simp [wiredAvoidingRegionSeeds]

theorem wiredAvoidingClusterSet_contains_outsideRegion
    (H W : Set V) (hWH : W ⊆ H) (A : Configuration G) (v : V) (hv : v ∉ H) :
    v ∈ wiredAvoidingClusterSet G W (wiredAvoidingRegionSeeds H) A := by
  exact wiredAvoidingClusterSet_seed_subset W (wiredAvoidingRegionSeeds H) A
    (by
      intro s hs hsW
      have hsH : s ∈ H := hWH hsW
      exact ((wiredAvoidingRegionSeeds_mem H s).mp hs) hsH)
    v ((wiredAvoidingRegionSeeds_mem H v).2 hv)

theorem wiredAvoidingComplementSet_subset_region
    (H W : Set V) (hWH : W ⊆ H) (A : Configuration G) :
    wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A ⊆ H := by
  intro v hv
  by_contra hvH
  exact hv (wiredAvoidingClusterSet_contains_outsideRegion H W hWH A v hvH)

def wiredAvoidingRegionEmbedding
    (H W : Set V) (hWH : W ⊆ H) (A : Configuration G) :
    wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A ↪ {v : V // v ∈ H} :=
  ⟨fun v => ⟨v.val, wiredAvoidingComplementSet_subset_region H W hWH A v.property⟩,
    by
      intro u v huv
      apply Subtype.ext
      exact congrArg (fun z : {v : V // v ∈ H} => z.val) huv⟩

theorem wiredAvoidingRegionGraph_map_le
    (H W : Set V) (hWH : W ⊆ H) (A : Configuration G) :
    (G.induce (wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A)).map
      (wiredAvoidingRegionEmbedding H W hWH A) ≤ G.induce H := by
  intro u v huv
  rcases (SimpleGraph.map_adj (wiredAvoidingRegionEmbedding H W hWH A)
      (G.induce (wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A)) u v).mp huv with
    ⟨u', v', hadj, rfl, rfl⟩
  exact SimpleGraph.induce_adj.mpr (SimpleGraph.induce_adj.mp hadj)

theorem wiredAvoidingComplement_wiredBoundary_le_regionWired
    (ξ : BoundaryCondition V) (H W : Set V) (hWH : W ⊆ H)
    (hξ : ξ.boundary ⊆ Hᶜ ∪ W) (A₀ : Configuration G) :
    (isolatedExtensionPullbackBoundary
      (wiredAvoidingComplementEmbedding G W (wiredAvoidingRegionSeeds H) A₀)
      (frozenBoundary ξ (revealRecordConfiguration G
        (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H)) A₀).val)).partition ≤
    (isolatedExtensionPullbackBoundary
      (wiredAvoidingRegionEmbedding H W hWH A₀)
      (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})).partition := by
  have houtside : ∀ v, v ∉ H → v ∈ wiredAvoidingClusterSet G W
      (wiredAvoidingRegionSeeds H) A₀ := by
    intro v hv
    exact wiredAvoidingClusterSet_contains_outsideRegion H W hWH A₀ v hv
  have hxi : ξ.boundary ⊆
      wiredAvoidingClusterSet G W (wiredAvoidingRegionSeeds H) A₀ ∪ W := by
    intro v hv
    rcases (Set.mem_union _ _ _).mp (hξ hv) with hvout | hvW
    · exact Set.mem_union_left _ (houtside v hvout)
    · exact Set.mem_union_right _ hvW
  have hsmall := isolatedPullback_frozenWiredAvoidingClusterBoundary_le_wired
    ξ W (wiredAvoidingRegionSeeds H) A₀ hxi
  intro u v huv
  have hw := hsmall ((Setoid.comap_rel _ _ _ _).mp huv)
  rcases (BoundaryCondition.wired_rel _ _ _).mp hw with heq | ⟨huW, hvW⟩
  · exact (BoundaryCondition.wired_rel _ _ _).mpr
      (Or.inl (congrArg (wiredAvoidingRegionEmbedding H W hWH A₀) heq))
  · have huW' : (wiredAvoidingRegionEmbedding H W hWH A₀) u ∈
        {v : {v : V // v ∈ H} | v.val ∈ W} := by
      change u.val ∈ W
      exact huW
    have hvW' : (wiredAvoidingRegionEmbedding H W hWH A₀) v ∈
        {v : {v : V // v ∈ H} | v.val ∈ W} := by
      change v.val ∈ W
      exact hvW
    exact (BoundaryCondition.wired_rel _ _ _).mpr (Or.inr ⟨huW', hvW'⟩)

theorem wiredAvoidingComplement_conditioned_event_probability_le_regionWired
    (q : ClusterWeight) (ξ : BoundaryCondition V) (H W : Set V)
    (hWH : W ⊆ H) (hξ : ξ.boundary ⊆ Hᶜ ∪ W) (A₀ : Configuration G)
    (E : Set (Configuration
      (G.induce (wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A₀))))
    (hE : IsUpperSet E) :
    (let C := wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A₀
     let f₀ := wiredAvoidingComplementEmbedding G W (wiredAvoidingRegionSeeds H) A₀
     let G₀ := G.induce C
     let K := revealRecordConfiguration G
       (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H)) A₀
     let filtered := ((law G q ξ).filter
       (revealRecordEvent G (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H)) A₀)
       (by
         rw [revealRecordEvent_eq_frozenStateEvent G
           (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H))
           (fun A B hAB => wiredAvoidingClusterReveal_consistent W
             (wiredAvoidingRegionSeeds H) A B hAB) A₀]
         exact frozenStateEvent_support q ξ
           (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H) A₀) K)).map
       (embeddedConfigurationRestriction G₀ G f₀
         (wiredAvoidingComplementGraph_le (G := G) W (wiredAvoidingRegionSeeds H) A₀));
     (filtered.toMeasure E).toReal ≤
       (measure (G.induce H) q (BoundaryCondition.wired
         {v : {v : V // v ∈ H} | v.val ∈ W})
         {B | embeddedConfigurationRestriction G₀ (G.induce H)
           (wiredAvoidingRegionEmbedding H W hWH A₀)
           (wiredAvoidingRegionGraph_map_le H W hWH A₀) B ∈ E}).toReal) := by
  classical
  let C := wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A₀
  let f₀ := wiredAvoidingComplementEmbedding G W (wiredAvoidingRegionSeeds H) A₀
  let G₀ := G.induce C
  let K := revealRecordConfiguration G
    (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H)) A₀
  let filtered := ((law G q ξ).filter
    (revealRecordEvent G (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H)) A₀)
    (by
      rw [revealRecordEvent_eq_frozenStateEvent G
        (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H))
        (fun A B hAB => wiredAvoidingClusterReveal_consistent W
          (wiredAvoidingRegionSeeds H) A B hAB) A₀]
      exact frozenStateEvent_support q ξ
        (wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H) A₀) K)).map
    (embeddedConfigurationRestriction G₀ G f₀
      (wiredAvoidingComplementGraph_le (G := G) W (wiredAvoidingRegionSeeds H) A₀))
  have hrecord := law_filter_wiredAvoidingClusterRecord_map_complement
    (G := G) q ξ W (wiredAvoidingRegionSeeds H) A₀
  have hfilteredLaw : filtered = law G₀ q
      (isolatedExtensionPullbackBoundary f₀ (frozenBoundary ξ K.val)) := by
    dsimp [filtered, K, f₀, G₀]
    exact hrecord
  change (filtered.toMeasure E).toReal ≤ _
  rw [hfilteredLaw]
  let f := wiredAvoidingRegionEmbedding H W hWH A₀
  let η : BoundaryCondition ( {v : V // v ∈ H} ) :=
    BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W}
  have hmap : G₀.map f ≤ G.induce H := wiredAvoidingRegionGraph_map_le H W hWH A₀
  have hpartition :
      (isolatedExtensionPullbackBoundary f₀ (frozenBoundary ξ K.val)).partition ≤
        (isolatedExtensionPullbackBoundary f η).partition :=
    wiredAvoidingComplement_wiredBoundary_le_regionWired ξ H W hWH hξ A₀
  have hboundary := measure_boundary_comparison q
    (isolatedExtensionPullbackBoundary f₀ (frozenBoundary ξ K.val))
    (isolatedExtensionPullbackBoundary f η) hpartition E hE
  have houter := embedded_boundary_probability_le G₀ (G.induce H) f hmap q η E hE
  calc
    ((law G₀ q (isolatedExtensionPullbackBoundary f₀ (frozenBoundary ξ K.val))).toMeasure E).toReal =
        (measure G₀ q (isolatedExtensionPullbackBoundary f₀ (frozenBoundary ξ K.val)) E).toReal := by
      simp [measure]
    _ ≤ (measure G₀ q (isolatedExtensionPullbackBoundary f η) E).toReal := hboundary
    _ ≤ (measure (G.induce H) q η
          {B | embeddedConfigurationRestriction G₀ (G.induce H) f hmap B ∈ E}).toReal := houter

end
end PottsContinuity.FKC.FiniteFK
