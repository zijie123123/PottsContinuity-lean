module

public import PottsContinuity.DualityExt.PositiveDomainMarkov
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Positive-`q` dual transport for edge subgraphs of a rectangle

The dual carrier of a rectangle subgraph is represented as the rectangle dual
with the duals of deleted primal bonds removed. Those deleted dual bonds are
forced open, and their connectivity is recorded in the induced boundary
partition.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open PottsContinuity.PD.Duality

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}
variable {G : SimpleGraph (RectangleVertex a w h)}

local instance subgraphDualPrimalEdgeFintype :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _
local instance subgraphDualDualEdgeFintype :
    Fintype (rectangleDualGraph a w h).edgeSet := Fintype.ofFinite _
local instance subgraphDualPrimalConfigFintype :
    Fintype (Configuration (rectangleGraph a w h)) := Fintype.ofFinite _
local instance subgraphDualDualConfigFintype :
    Fintype (Configuration (rectangleDualGraph a w h)) := Fintype.ofFinite _
local instance subgraphDualGraphConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance subgraphDualGraphEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance subgraphDualPrimalEdgeDecidableEq :
    DecidableEq (rectangleGraph a w h).edgeSet := positiveDMPEdgeDecidableEq
local instance subgraphDualDualEdgeDecidableEq :
    DecidableEq (rectangleDualGraph a w h).edgeSet := positiveDMPEdgeDecidableEq
local instance subgraphDualGraphEdgeDecidableEq :
    DecidableEq G.edgeSet := positiveDMPEdgeDecidableEq
local instance subgraphDualRemovedPrimalFintype (R : Configuration (rectangleGraph a w h)) :
    Fintype (RemovedConfiguration (rectangleGraph a w h) R) := Fintype.ofFinite _
local instance subgraphDualRemainingPrimalFintype (R : Configuration (rectangleGraph a w h)) :
    Fintype (RemainingConfiguration (rectangleGraph a w h) R) := Fintype.ofFinite _
local instance subgraphDualRemovedDualFintype (R : Configuration (rectangleDualGraph a w h)) :
    Fintype (RemovedConfiguration (rectangleDualGraph a w h) R) := Fintype.ofFinite _
local instance subgraphDualRemainingDualFintype (R : Configuration (rectangleDualGraph a w h)) :
    Fintype (RemainingConfiguration (rectangleDualGraph a w h) R) := Fintype.ofFinite _

/-- Relabel a rectangle primal edge by the unique dual edge that it crosses. -/
def rectangleDualEdgeEquiv (a : LatticeVertex) (w h : ℕ) :
    (rectangleGraph a w h).edgeSet ≃ (rectangleDualGraph a w h).edgeSet :=
  (rectanglePrimalDualEdgeEquiv a w h).trans (rectangleDualGraphEdgeEquiv a w h)

/-- Duals of precisely the primal bonds removed from the rectangular host. -/
def rectangleSubgraphRemovedDualEdges (_hG : G ≤ rectangleGraph a w h) :
    Configuration (rectangleDualGraph a w h) :=
  (subgraphRemovedEdges G (rectangleGraph a w h)).map
    (rectangleDualEdgeEquiv a w h).toEmbedding

private theorem mem_rectangleSubgraphRemovedDualEdges
    (hG : G ≤ rectangleGraph a w h) (e : (rectangleDualGraph a w h).edgeSet) :
    e ∈ rectangleSubgraphRemovedDualEdges hG ↔
      ∃ f ∈ subgraphRemovedEdges G (rectangleGraph a w h),
        rectangleDualEdgeEquiv a w h f = e := by
  classical
  change e ∈ (subgraphRemovedEdges G (rectangleGraph a w h)).map
      (rectangleDualEdgeEquiv a w h).toEmbedding ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨f, hf, hfe⟩
    refine ⟨f, hf, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hfe
  · rintro ⟨f, hf, hfe⟩
    refine ⟨f, hf, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hfe

/-- The complementary edge-state relation in the graph-edge carrier. -/
@[simp] theorem rectangleDualEdgeEquiv_mem_dualConfiguration
    (A : Configuration (rectangleGraph a w h))
    (e : (rectangleGraph a w h).edgeSet) :
    rectangleDualEdgeEquiv a w h e ∈
      positiveRectangleDualConfigurationEquiv a w h A ↔ e ∉ A := by
  change rectangleDualGraphEdgeEquiv a w h (rectanglePrimalDualEdgeEquiv a w h e) ∈
      positiveRectangleDualConfigurationEquiv a w h A ↔ e ∉ A
  exact mem_positiveRectangleDualConfigurationEquiv a w h A
    (rectanglePrimalDualEdgeEquiv a w h e)

/-- Every dual of a deleted primal edge is forced open by the complementary
dual configuration of the subgraph configuration extended by closed bonds. -/
theorem rectangleSubgraphRemovedDualEdges_subset_dualConfiguration
    (hG : G ≤ rectangleGraph a w h) (A : Configuration G) :
    rectangleSubgraphRemovedDualEdges hG ⊆
      positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A) := by
  intro e he
  rcases (mem_rectangleSubgraphRemovedDualEdges hG e).mp he with ⟨f, hf, hfe⟩
  have hfnot : f ∉ subgraphConfigurationEmbedding hG A := by
    intro hfa
    change f ∈ A.map (subgraphEdgeEmbedding hG) at hfa
    rcases Finset.mem_map.mp hfa with ⟨g, hg, hgf⟩
    have hfg : g.val = f.val := by
      have := congrArg Subtype.val hgf
      simpa only [subgraphEdgeEmbedding_coe] using this
    have hfG : f.val ∈ G.edgeSet := by rw [← hfg]; exact g.property
    exact ((mem_subgraphRemovedEdges (G := G)
      (H := rectangleGraph a w h) f).mp hf) hfG
  have hd : rectangleDualEdgeEquiv a w h f ∈
      positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A) :=
    (rectangleDualEdgeEquiv_mem_dualConfiguration _ f).2 hfnot
  simpa [hfe] using hd

/-- A dual configuration with every deleted-bond dual open, after discarding
those forced edges. This is the actual dual edge-subgraph carrier. -/
def rectangleSubgraphDualRemainingEquiv
    (hG : G ≤ rectangleGraph a w h) :
    Configuration G ≃ RemainingConfiguration (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG) := by
  classical
  let R := subgraphRemovedEdges G (rectangleGraph a w h)
  let K := rectangleSubgraphRemovedDualEdges hG
  let E := positiveRectangleDualConfigurationEquiv a w h
  let emb := subgraphConfigurationEmbedding hG
  let toFun (A : Configuration G) : RemainingConfiguration (rectangleDualGraph a w h) K :=
    (configurationSplitEquiv (rectangleDualGraph a w h) K (E (emb A))).1
  let invFun (B : RemainingConfiguration (rectangleDualGraph a w h) K) : Configuration G :=
    subgraphConfigurationRestriction hG
      (E.symm (B.val ∪ K))
  have hK (A : Configuration G) : K ⊆ E (emb A) := by
    exact rectangleSubgraphRemovedDualEdges_subset_dualConfiguration hG A
  have hEmbed_left (A : Configuration G) :
      subgraphConfigurationRestriction hG (emb A) = A :=
    subgraphConfigurationRestriction_embedding hG A
  have hNoRemoved (B : RemainingConfiguration (rectangleDualGraph a w h) K) :
      ∀ e ∈ R, e ∉ E.symm (B.val ∪ K) := by
    intro e he hopen
    have hd : rectangleDualEdgeEquiv a w h e ∈ B.val ∪ K := by
      apply Finset.mem_union_right
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    have hdopen : rectangleDualEdgeEquiv a w h e ∈ E (E.symm (B.val ∪ K)) := by
      simpa using hd
    exact (rectangleDualEdgeEquiv_mem_dualConfiguration _ e).mp hdopen hopen
  have hEmbed_right (B : RemainingConfiguration (rectangleDualGraph a w h) K) :
      emb (invFun B) = E.symm (B.val ∪ K) := by
    apply Finset.ext
    intro e
    change e ∈ subgraphConfigurationEmbedding hG
        (subgraphConfigurationRestriction hG (E.symm (B.val ∪ K))) ↔
      e ∈ E.symm (B.val ∪ K)
    unfold subgraphConfigurationEmbedding
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨f, hf, hfe⟩
      have hopen := (mem_subgraphConfigurationRestriction hG
        (E.symm (B.val ∪ K)) f).mp hf
      rw [← hfe]
      exact hopen
    · intro he
      have hn : e ∉ R := by
        intro hr
        exact hNoRemoved B e hr he
      have hGedge : e.val ∈ G.edgeSet := by
        by_contra hg
        exact hn ((mem_subgraphRemovedEdges (G := G)
          (H := rectangleGraph a w h) e).2 hg)
      refine Finset.mem_map.mpr ⟨⟨e.val, hGedge⟩, ?_, ?_⟩
      · exact (mem_subgraphConfigurationRestriction hG
          (E.symm (B.val ∪ K)) ⟨e.val, hGedge⟩).mpr (by
            have heq : (subgraphEdgeEmbedding hG ⟨e.val, hGedge⟩ :
                (rectangleGraph a w h).edgeSet) = e := by
              apply Subtype.ext
              rfl
            rw [heq]
            exact he)
      · apply Subtype.ext
        rfl
  refine Equiv.ofBijective toFun ?_
  constructor
  · intro A A' hAA'
    have hdual : E (emb A) = E (emb A') := by
      have hs := congrArg Subtype.val hAA'
      change (E (emb A) \ K) = (E (emb A') \ K) at hs
      ext e
      have hiff := congrArg (fun S : Finset (rectangleDualGraph a w h).edgeSet => e ∈ S) hs
      by_cases hek : e ∈ K
      · constructor
        · intro _
          exact hK A' hek
        · intro _
          exact hK A hek
      · simpa [Finset.mem_sdiff, hek] using hiff
    have hemb : emb A = emb A' := E.injective hdual
    have hrest := congrArg (subgraphConfigurationRestriction hG) hemb
    simpa [emb, hEmbed_left] using hrest
  · intro B
    refine ⟨invFun B, ?_⟩
    change (configurationSplitEquiv (rectangleDualGraph a w h) K
        (E (emb (invFun B)))).1 = B
    rw [hEmbed_right B, E.apply_symm_apply]
    apply Subtype.ext
    ext e
    change e ∈ (B.val ∪ K) \ K ↔ e ∈ B.val
    rw [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hB | hK, hnotK⟩
      · exact hB
      · exact (hnotK hK).elim
    · intro hB
      exact ⟨Or.inl hB, Finset.disjoint_left.mp B.property hB⟩

@[simp] theorem rectangleSubgraphDualRemainingEquiv_apply
    (hG : G ≤ rectangleGraph a w h) (A : Configuration G) :
    rectangleSubgraphDualRemainingEquiv hG A =
      (configurationSplitEquiv (rectangleDualGraph a w h)
        (rectangleSubgraphRemovedDualEdges hG)
        (positiveRectangleDualConfigurationEquiv a w h
          (subgraphConfigurationEmbedding hG A))).1 := by
  classical
  unfold rectangleSubgraphDualRemainingEquiv
  rfl

/-- The free subgraph weight agrees with the host weight after closing every
deleted primal edge. -/
private theorem positiveFKWeight_subgraphEmbedding
    (hG : G ≤ rectangleGraph a w h) {q p : ℝ} (ξ : BoundaryCondition _)
    (A : Configuration G) :
    positiveFKWeight (rectangleGraph a w h) q p ξ
        (subgraphConfigurationEmbedding hG A) =
      (1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card *
        positiveFKWeight G q p ξ A := by
  have hcount : componentCount (rectangleGraph a w h) ξ
      (subgraphConfigurationEmbedding hG A) = componentCount G ξ A := by
    simp only [componentCount, componentSetoid,
      openGraph_subgraphConfigurationEmbedding]
  have hcard : Nat.card (rectangleGraph a w h).edgeSet -
      (subgraphRemovedEdges G (rectangleGraph a w h)).card = Nat.card G.edgeSet :=
    subgraph_edge_card hG
  have hA : A.card ≤ Nat.card G.edgeSet := by
    simpa using (Finset.card_le_univ A)
  have hRcard : (subgraphRemovedEdges G (rectangleGraph a w h)).card ≤
      Nat.card (rectangleGraph a w h).edgeSet := by
    simpa using (Finset.card_le_univ
      (subgraphRemovedEdges G (rectangleGraph a w h)))
  have hsplitCard : (subgraphRemovedEdges G (rectangleGraph a w h)).card +
      Nat.card G.edgeSet = Nat.card (rectangleGraph a w h).edgeSet := by omega
  have hclosed : Nat.card (rectangleGraph a w h).edgeSet - A.card =
      (subgraphRemovedEdges G (rectangleGraph a w h)).card +
        (Nat.card G.edgeSet - A.card) := by omega
  rw [positiveFKWeight, positiveFKWeight, hcount]
  change p ^ (A.map (subgraphEdgeEmbedding hG)).card * (1 - p) ^
        (Nat.card (rectangleGraph a w h).edgeSet -
          (A.map (subgraphEdgeEmbedding hG)).card) *
      q ^ componentCount G ξ A =
    (1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card *
      (p ^ A.card * (1 - p) ^ (Nat.card G.edgeSet - A.card) *
        q ^ componentCount G ξ A)
  rw [Finset.card_map, hclosed, pow_add]
  ring

private theorem rectangleSubgraphDual_frozenState
    (hG : G ≤ rectangleGraph a w h) (A : Configuration G) :
    (configurationSplitEquiv (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG)
      (positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A))).2.val =
      rectangleSubgraphRemovedDualEdges hG := by
  classical
  have hK := rectangleSubgraphRemovedDualEdges_subset_dualConfiguration hG A
  apply Finset.ext
  intro e
  constructor
  · intro he
    change e ∈
      positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A) ∩ rectangleSubgraphRemovedDualEdges hG at he
    exact (Finset.mem_inter.mp he).2
  · intro he
    change e ∈
      positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A) ∩ rectangleSubgraphRemovedDualEdges hG
    exact Finset.mem_inter.mpr ⟨hK he, he⟩

/-- The positive-`q` free law on any same-carrier edge subgraph of a rectangle
pushes through complementary-edge duality to the dual edge subgraph. The
dual boundary partition is exactly rectangle wired boundary joined with the
connectivity generated by the forced-open duals of deleted primal bonds. -/
theorem positive_free_subgraph_map_dual_remaining
    (hG : G ≤ rectangleGraph a w h)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    (positiveFKLaw G q p hq hp hp1 (BoundaryCondition.free ∅)).map
      (rectangleSubgraphDualRemainingEquiv hG) =
      positiveRemainingLaw q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
        (frozenBoundary (rectangleDualBoundaryCondition a w h)
          (rectangleSubgraphRemovedDualEdges hG))
        (rectangleSubgraphRemovedDualEdges hG) := by
  let K := rectangleSubgraphRemovedDualEdges hG
  let e := rectangleSubgraphDualRemainingEquiv hG
  let ξ := rectangleDualBoundaryCondition a w h
  let H : RemovedConfiguration (rectangleDualGraph a w h) K :=
    ⟨K, Finset.Subset.rfl⟩
  let c := (positiveRectangleDualityFactor q p a w h *
    dualParameter q p ^ K.card) /
    (1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos
      (mul_pos (positiveRectangleDualityFactor_pos hq hp hp1 a w h)
        (pow_pos (dualParameter_pos hq hp hp1) _))
      (pow_pos (sub_pos.mpr hp1) _)
  have hweight (A : Configuration G) :
      positiveFKWeight G q p (BoundaryCondition.free ∅) A =
        c * positiveRemainingWeight q (dualParameter q p)
          (frozenBoundary ξ K) K (e A) := by
    have hprimal := positiveFKWeight_subgraphEmbedding hG (q := q) (p := p)
      (BoundaryCondition.free ∅) A
    have hrect := positive_rectangle_weight_eq_factor_mul_dual_weight
      hq hp hp1 a w h (subgraphConfigurationEmbedding hG A)
    have hsplit := (configurationSplitEquiv (rectangleDualGraph a w h) K).symm_apply_apply
      (positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A))
    have hforced := rectangleSubgraphDual_frozenState hG A
    have hdecomp : positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A) = (e A).val ∪ K := by
      change (configurationSplitEquiv (rectangleDualGraph a w h) K
        (positiveRectangleDualConfigurationEquiv a w h
          (subgraphConfigurationEmbedding hG A))).1.val ∪
        (configurationSplitEquiv (rectangleDualGraph a w h) K
          (positiveRectangleDualConfigurationEquiv a w h
            (subgraphConfigurationEmbedding hG A))).2.val = _ at hsplit
      rw [hforced] at hsplit
      exact hsplit.symm
    have hdualFactor := positiveFKWeight_union_frozen_factorization
      (q := q) (p := dualParameter q p) (ξ := ξ)
      (R := K) (A := e A) H
    have hHval : H.val = K := rfl
    have hdualFactor' := hdualFactor
    rw [hHval] at hdualFactor'
    have hremoved : positiveRemovedWeight (dualParameter q p) K H =
        dualParameter q p ^ K.card := by
      simp [positiveRemovedWeight, H]
    have hdualfull : positiveFKWeight (rectangleDualGraph a w h) q
        (dualParameter q p) ξ
        (positiveRectangleDualConfigurationEquiv a w h
          (subgraphConfigurationEmbedding hG A)) =
        dualParameter q p ^ K.card *
          positiveRemainingWeight q (dualParameter q p)
            (frozenBoundary ξ K) K (e A) := by
      calc
        _ = positiveFKWeight (rectangleDualGraph a w h) q
              (dualParameter q p) ξ ((e A).val ∪ K) := by rw [hdecomp]
        _ = positiveRemainingWeight q (dualParameter q p)
              (frozenBoundary ξ K) K (e A) *
              positiveRemovedWeight (dualParameter q p) K H := hdualFactor'
        _ = _ := by rw [hremoved]; ring
    have hd : 0 < (1 - p) ^ (subgraphRemovedEdges G
        (rectangleGraph a w h)).card := pow_pos (sub_pos.mpr hp1) _
    have hdne : (1 - p) ^ (subgraphRemovedEdges G
        (rectangleGraph a w h)).card ≠ 0 := hd.ne'
    calc
      _ = ((1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card *
          positiveFKWeight G q p (BoundaryCondition.free ∅) A) /
          (1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card := by
            field_simp [hdne]
      _ = positiveFKWeight (rectangleGraph a w h) q p
          (BoundaryCondition.free ∅)
          (subgraphConfigurationEmbedding hG A) /
          (1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card := by
            rw [hprimal]
      _ = (positiveRectangleDualityFactor q p a w h * dualParameter q p ^ K.card) *
          positiveRemainingWeight q (dualParameter q p)
            (frozenBoundary ξ K) K (e A) /
          (1 - p) ^ (subgraphRemovedEdges G (rectangleGraph a w h)).card := by
            rw [hrect, hdualfull]
            ring_nf
      _ = c * positiveRemainingWeight q (dualParameter q p)
          (frozenBoundary ξ K) K (e A) := by
            dsimp [c]
            field_simp [hdne]
  unfold positiveFKLaw positiveRemainingLaw
  apply FiniteProbability.pmf_map_equiv_of_common_factor
    (rectangleSubgraphDualRemainingEquiv hG) c _ _ hc
    (positiveFKWeight_pos' hq hp hp1 (BoundaryCondition.free ∅))
    (positiveRemainingWeight_pos hq (dualParameter_pos hq hp hp1)
      (dualParameter_lt_one hq hp hp1)
      (frozenBoundary (rectangleDualBoundaryCondition a w h)
        (rectangleSubgraphRemovedDualEdges hG)) (rectangleSubgraphRemovedDualEdges hG))
    hweight

end
end PottsContinuity.DualityExt
