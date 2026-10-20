module

public import PottsContinuity.PlanarMixed.FiniteSlit.HostAugmentation

/-! The augmented source sample has the exact frozen exterior record. Its
dual is the canonical reflected sample plus the fixed OPEN slit chain. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality BD12 DualityExt
noncomputable section
local instance finiteSlitClampedDualSampleEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- A retained source edge outside the active carrier is an internal arc bond. -/
theorem source_removed_host_edge_mem_arcBonds (M : ℕ) (x y : ℤ)
    (e : (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).edgeSet)
    (heG : e.val ∈ (graph M x y).edgeSet)
    (heR : e ∈ subgraphRemovedEdges (activeGraph M x y)
      (rectangleGraph (x-(M : ℤ),0) (2*M-1) M)) : e ∈ rectangleArcBonds M x y := by
  obtain ⟨s,he⟩ := e
  induction s using Sym2.inductionOn with
  | _ u v =>
    have hg := (graph M x y).mem_edgeSet.mp heG
    have hn : (⟨s(u,v),(graph M x y).mem_edgeSet.mpr hg⟩ : (graph M x y).edgeSet) ∈
        internalEdges M x y := by
      by_contra hn
      have ha := (edgeRestriction_adj_exists_not_mem (graph M x y) (internalEdges M x y) u v).mpr ⟨hg,hn⟩
      exact (mem_subgraphRemovedEdges _).mp heR ((activeGraph M x y).mem_edgeSet.mpr ha)
    rw [internalEdges,Finset.mem_union,mem_internalBonds_pair _ _ u v hg,
      mem_internalBonds_pair _ _ u v hg] at hn
    have hh := (rectangleGraph (x-(M : ℤ),0) (2*M-1) M).mem_edgeSet.mp he
    rw [rectangleArcBonds,Finset.mem_union,mem_internalBonds_pair _ _ u v hh,
      mem_internalBonds_pair _ _ u v hh]
    exact hn

/-- All removed primal states are the specified OPEN arc / CLOSED slit record. -/
theorem hostAugmentation_frozen_record (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y)) :
    hostAugmentation M x y C ∈ frozenStateEvent _ (exteriorState M x y) := by
  change hostAugmentation M x y C ∩ _ = rectangleArcBonds M x y
  ext e
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨he,hr⟩
    rcases Finset.mem_union.mp he with he | he
    · have hg : e.val ∈ (graph M x y).edgeSet := by
        obtain ⟨a,_,ha⟩ := Finset.mem_map.mp he
        rw [← ha]
        exact a.property
      exact source_removed_host_edge_mem_arcBonds M x y e hg hr
    · exact he
  · intro he
    exact ⟨Finset.mem_union_right _ he,rectangleArcBonds_subset_removed M x y he⟩

/-- Augmentation leaves every active source edge at its original sampled state. -/
theorem hostRestriction_hostAugmentation (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y)) :
    hostRestriction M x y (hostAugmentation M x y C) = activeRestriction M x y C := by
  ext e
  rw [activeRestriction_mem]
  let a : (graph M x y).edgeSet :=
    edgeRestrictionEdgeEmbedding (graph M x y) (internalEdges M x y) e
  change e ∈ subgraphConfigurationRestriction _ _ ↔ a ∈ C
  rw [mem_subgraphConfigurationRestriction]
  have he : subgraphEdgeEmbedding (activeGraph_le_rectangle M x y) e =
      subgraphEdgeEmbedding (graph_le_rectangle M x y) a := Subtype.ext rfl
  have hn : subgraphEdgeEmbedding (activeGraph_le_rectangle M x y) e ∉ rectangleArcBonds M x y := by
    intro ha
    have hr := rectangleArcBonds_subset_removed M x y ha
    exact (mem_subgraphRemovedEdges _).mp hr e.property
  change _ ∈ subgraphConfigurationEmbedding _ C ∪ rectangleArcBonds M x y ↔ _
  simp only [Finset.mem_union,hn,or_false]
  rw [he]
  exact Finset.mem_map' (subgraphEdgeEmbedding (graph_le_rectangle M x y))

/-- The reflected active part of the augmented dual is the canonical full-source complement. -/
theorem dualHostRestriction_augmented_dual (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) (C : Configuration (graph M x y)) :
    dualHostRestriction M x y hM
      (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M (hostAugmentation M x y C)) =
      dualConfiguration M x y C := by
  rw [hostRestriction_dual_transport M x y hM hy hyM,hostRestriction_hostAugmentation,
    dualConfiguration_factor M x y hM hy hyM]

/-- The complementary augmented sample has exactly the fixed dual exterior state. -/
theorem augmented_dual_frozen_record (M : ℕ) (x y : ℤ) (C : Configuration (graph M x y)) :
    positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M (hostAugmentation M x y C) ∈
      frozenStateEvent _ (dualExteriorState M x y) := by
  exact (complementary_frozen_intersection_iff
    (rectangleDualEdgeEquiv (x-(M : ℤ),0) (2*M-1) M)
    (positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M)
    (fun A e => rectangleDualEdgeEquiv_mem_dualConfiguration A e) _ _
    (hostAugmentation M x y C) (exteriorState M x y).property).mp
      (hostAugmentation_frozen_record M x y C)

/-- Reconstruct any exact dual record from its actual embedded sampled part
and the fixed exterior state, retaining every artificial host vertex. -/
theorem dual_sample_reconstruction (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (B : Configuration (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M))
    (hB : B ∈ frozenStateEvent _ (dualExteriorState M x y)) :
    B = embeddedConfigurationEmbedding (dualGraph M x y)
      (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (cellEmbedding M x hM)
      (dualGraph_map_le_rectangleDual M x y hM) (dualHostRestriction M x y hM B) ∪
        (dualExteriorState M x y).val := by
  let D := dualGraph M x y
  let f := cellEmbedding M x hM
  let H := rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M
  have hrec : B ∩ dualRemovedEdges M x y = (dualExteriorState M x y).val := hB
  ext e
  constructor
  · intro he
    by_cases hr : e ∈ dualRemovedEdges M x y
    · exact Finset.mem_union_right _ (hrec ▸ Finset.mem_inter.mpr ⟨he,hr⟩)
    · apply Finset.mem_union_left
      rw [embeddedConfigurationEmbedding_eq_map]
      have hm : e.val ∈ (D.map f).edgeSet := by
        have hn : e ∉ subgraphRemovedEdges (D.map f) H := by
          rw [dualRemovedEdges_eq_mapped_complement M x y hM hy hyM]
          exact hr
        simpa only [mem_subgraphRemovedEdges,not_not] using hn
      let a := (isolatedExtensionEdgeEquiv D f).symm ⟨e.val,hm⟩
      have hval : Sym2.map f a.val = e.val :=
        congrArg (fun z : (D.map f).edgeSet => z.val)
          ((isolatedExtensionEdgeEquiv D f).apply_symm_apply ⟨e.val,hm⟩)
      have ha : embeddedEdgeEmbedding D H f (dualGraph_map_le_rectangleDual M x y hM) a = e :=
        Subtype.ext hval
      apply Finset.mem_map.mpr
      refine ⟨a,?_,ha⟩
      exact (mem_embeddedConfigurationRestriction _ _ _ _ B a).mpr (ha.symm ▸ he)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · exact embeddedConfigurationEmbedding_restriction_subset _ _ _ _ B he
    · exact (Finset.mem_inter.mp (hrec.symm ▸ he)).1

/-- Exact decomposition used to remove the static forced slit chain. -/
theorem augmented_dual_decomposition (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ)) (C : Configuration (graph M x y)) :
    positiveRectangleDualConfigurationEquiv (x-(M : ℤ),0) (2*M-1) M (hostAugmentation M x y C) =
      embeddedConfigurationEmbedding (dualGraph M x y)
        (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (cellEmbedding M x hM)
        (dualGraph_map_le_rectangleDual M x y hM) (dualConfiguration M x y C) ∪
          (dualExteriorState M x y).val := by
  rw [dual_sample_reconstruction M x y hM hy hyM _ (augmented_dual_frozen_record M x y C),
    dualHostRestriction_augmented_dual M x y hM hy hyM C]

end
end PottsContinuity.PlanarMixed.FiniteSlit
