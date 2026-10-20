module

public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}
variable {G : SimpleGraph (RectangleVertex a w h)}

local instance conditionedSubgraphHostEdgeFintype :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _
local instance conditionedSubgraphDualHostEdgeFintype :
    Fintype (rectangleDualGraph a w h).edgeSet := Fintype.ofFinite _
local instance conditionedSubgraphHostEdgeDecidableEq :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance conditionedSubgraphDualHostEdgeDecidableEq :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _
local instance conditionedSubgraphEdgeDecidableEq :
    DecidableEq G.edgeSet := Classical.decEq _
local instance conditionedSubgraphEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance conditionedSubgraphDualEdgeFintype (hG : G ≤ rectangleGraph a w h) :
    Fintype (rectangleSubgraphDualGraph hG).edgeSet := Fintype.ofFinite _
local instance conditionedSubgraphHostConfigFintype :
    Fintype (Configuration (rectangleGraph a w h)) := Fintype.ofFinite _
local instance conditionedSubgraphDualHostConfigFintype :
    Fintype (Configuration (rectangleDualGraph a w h)) := Fintype.ofFinite _
local instance conditionedSubgraphConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance conditionedSubgraphDualConfigFintype (hG : G ≤ rectangleGraph a w h) :
    Fintype (Configuration (rectangleSubgraphDualGraph hG)) := Fintype.ofFinite _
local instance conditionedEmbeddedConfigFintype {V : Type*} [Finite V]
    {J : SimpleGraph V} : Fintype (Configuration J) := Fintype.ofFinite _
local instance conditionedEmbeddedMappedConfigFintype {V : Type*} [Finite V]
    {J : SimpleGraph V} (e : V ↪ RectangleVertex a w h) :
    Fintype (Configuration (J.map e)) := Fintype.ofFinite _
local instance conditionedEmbeddedDualConfigFintype {V : Type*} [Finite V]
    {J : SimpleGraph V} (e : V ↪ RectangleVertex a w h)
    (hJ : J.map e ≤ rectangleGraph a w h) :
    Fintype (Configuration (rectangleSubgraphDualGraph hJ)) := Fintype.ofFinite _

/-- The dual bonds forced open by the deleted primal bonds fixed closed. -/
def rectangleSubgraphDualOpenRemovedState
    (hG : G ≤ rectangleGraph a w h)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges G (rectangleGraph a w h))) :
    RemovedConfiguration (rectangleDualGraph a w h)
      (rectangleSubgraphRemovedDualEdges hG) := by
  let M := subgraphRemovedEdges G (rectangleGraph a w h)
  let Mstar := rectangleSubgraphRemovedDualEdges hG
  let Hstar := H.val.map (rectangleDualEdgeEquiv a w h).toEmbedding
  exact ⟨Mstar \ Hstar, Finset.sdiff_subset⟩

private theorem rectangleSubgraphDualRemovedState_map_subset
    (hG : G ≤ rectangleGraph a w h)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges G (rectangleGraph a w h))) :
    H.val.map (rectangleDualEdgeEquiv a w h).toEmbedding ⊆
      rectangleSubgraphRemovedDualEdges hG := by
  intro e he
  rcases Finset.mem_map.mp he with ⟨f, hf, hfe⟩
  exact Finset.mem_map.mpr ⟨f, H.property hf, hfe⟩

private theorem positiveRemainingWeight_subgraph_conditioned
    (hG : G ≤ rectangleGraph a w h) {q p : ℝ}
    (ξ : BoundaryCondition (RectangleVertex a w h)) (A : Configuration G) :
    positiveRemainingWeight q p ξ
        (subgraphRemovedEdges G (rectangleGraph a w h))
        (subgraphRemainingConfigurationEquiv hG A) =
      positiveFKWeight G q p ξ A := by
  have hcount : componentCount (rectangleGraph a w h) ξ
      (subgraphConfigurationEmbedding hG A) = componentCount G ξ A := by
    simp only [componentCount, componentSetoid,
      openGraph_subgraphConfigurationEmbedding]
  have hcard : Nat.card (rectangleGraph a w h).edgeSet -
      (subgraphRemovedEdges G (rectangleGraph a w h)).card = Nat.card G.edgeSet :=
    subgraph_edge_card hG
  rw [positiveRemainingWeight, subgraphRemainingConfigurationEquiv_val,
    positiveFKWeight, hcount]
  change p ^ (A.map (subgraphEdgeEmbedding hG)).card * (1 - p) ^
        (Nat.card (rectangleGraph a w h).edgeSet -
          (subgraphRemovedEdges G (rectangleGraph a w h)).card -
            (A.map (subgraphEdgeEmbedding hG)).card) *
      q ^ componentCount G ξ A =
    p ^ A.card * (1 - p) ^ (Nat.card G.edgeSet - A.card) *
      q ^ componentCount G ξ A
  rw [Finset.card_map, hcard]

private theorem rectangleSubgraphDualConditioned_decomposition
    (hG : G ≤ rectangleGraph a w h)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges G (rectangleGraph a w h)))
    (A : Configuration G) :
    positiveRectangleDualConfigurationEquiv a w h
        (subgraphConfigurationEmbedding hG A ∪ H.val) =
      (rectangleSubgraphDualRemainingEquiv hG A).val ∪
        (rectangleSubgraphDualOpenRemovedState hG H).val := by
  classical
  let M := subgraphRemovedEdges G (rectangleGraph a w h)
  let Mstar := rectangleSubgraphRemovedDualEdges hG
  let Hstar := H.val.map (rectangleDualEdgeEquiv a w h).toEmbedding
  let K := rectangleSubgraphDualOpenRemovedState hG H
  let E := positiveRectangleDualConfigurationEquiv a w h
  let e := rectangleSubgraphDualRemainingEquiv hG
  have hforced : Mstar ⊆ E (subgraphConfigurationEmbedding hG A) :=
    rectangleSubgraphRemovedDualEdges_subset_dualConfiguration hG A
  have hsplit := (configurationSplitEquiv (rectangleDualGraph a w h) Mstar
    ).symm_apply_apply (E (subgraphConfigurationEmbedding hG A))
  have hstate : (configurationSplitEquiv (rectangleDualGraph a w h) Mstar
      (E (subgraphConfigurationEmbedding hG A))).2.val = Mstar := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      exact (Finset.mem_inter.mp hd).2
    · intro hd
      exact Finset.mem_inter.mpr ⟨hforced hd, hd⟩
  have hdecomp : E (subgraphConfigurationEmbedding hG A) = (e A).val ∪ Mstar := by
    change (configurationSplitEquiv (rectangleDualGraph a w h) Mstar
      (E (subgraphConfigurationEmbedding hG A))).1.val ∪
        (configurationSplitEquiv (rectangleDualGraph a w h) Mstar
          (E (subgraphConfigurationEmbedding hG A))).2.val = _ at hsplit
    rw [hstate] at hsplit
    have hfirst : (configurationSplitEquiv (rectangleDualGraph a w h) Mstar
        (E (subgraphConfigurationEmbedding hG A))).1 = e A := by
      simpa only [Mstar, E, e] using
        (rectangleSubgraphDualRemainingEquiv_apply hG A).symm
    rw [hfirst] at hsplit
    exact hsplit.symm
  have hsubtract : E (subgraphConfigurationEmbedding hG A ∪ H.val) =
      E (subgraphConfigurationEmbedding hG A) \ Hstar := by
    apply Finset.ext
    intro d
    let f := (rectangleDualEdgeEquiv a w h).symm d
    have hfd : rectangleDualEdgeEquiv a w h f = d :=
      (rectangleDualEdgeEquiv a w h).apply_symm_apply d
    have hdual (X : Configuration (rectangleGraph a w h)) :
        d ∈ E X ↔ f ∉ X := by
      rw [← hfd]
      exact rectangleDualEdgeEquiv_mem_dualConfiguration X f
    have hmapH : d ∈ Hstar ↔ f ∈ H.val := by
      change d ∈ Finset.map (rectangleDualEdgeEquiv a w h).toEmbedding H.val ↔ _
      rw [Finset.mem_map]
      constructor
      · rintro ⟨x, hx, hxd⟩
        have hxf : x = f := (rectangleDualEdgeEquiv a w h).injective
          (hxd.trans hfd.symm)
        simpa [hxf] using hx
      · intro hf
        exact ⟨f, hf, hfd⟩
    rw [hdual, Finset.mem_sdiff, hdual, hmapH]
    constructor
    · intro hf
      exact ⟨fun hx => hf (Finset.mem_union_left _ hx),
        fun hx => hf (Finset.mem_union_right _ hx)⟩
    · rintro ⟨hfA, hfH⟩ hx
      rcases Finset.mem_union.mp hx with hxA | hxH
      · exact hfA hxA
      · exact hfH hxH
  have hHstar_subset : Hstar ⊆ Mstar := by
    exact rectangleSubgraphDualRemovedState_map_subset hG H
  have hedisj : Disjoint (e A).val Mstar := (e A).property
  rw [hsubtract, hdecomp]
  change ((e A).val ∪ Mstar) \ Hstar =
    (e A).val ∪ (Mstar \ Hstar)
  apply Finset.ext
  intro d
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hB | hM, hnH⟩
    · exact Or.inl hB
    · exact Or.inr ⟨hM, hnH⟩
  · rintro (hB | ⟨hM, hnH⟩)
    · refine ⟨Or.inl hB, ?_⟩
      intro hh
      exact Finset.disjoint_left.mp hedisj hB (hHstar_subset hh)
    · exact ⟨Or.inr hM, hnH⟩

private theorem positiveRemovedWeight_pos_conditioned {q p : ℝ}
    (_hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    {V : Type*} [Finite V] {J : SimpleGraph V}
    (R : Configuration J) (H : RemovedConfiguration J R) :
    0 < positiveRemovedWeight p R H := by
  unfold positiveRemovedWeight
  exact mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp1) _)

/-- Exact dual law after fixing an arbitrary state on the deleted primal
bonds. The boundary on each side is generated by the corresponding open
fixed bonds and the rectangle's dual exterior wiring. -/
theorem positive_subgraph_conditioned_duality_law
    (hG : G ≤ rectangleGraph a w h)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges G (rectangleGraph a w h))) :
    (positiveFKLaw G q p hq hp hp1
      (frozenBoundary (BoundaryCondition.free ∅) H.val)).map
        (rectangleSubgraphDualConfigurationEquiv hG) =
      positiveFKLaw (rectangleSubgraphDualGraph hG) q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
        (frozenBoundary (rectangleDualBoundaryCondition a w h)
          (rectangleSubgraphDualOpenRemovedState hG H).val) := by
  classical
  let M := subgraphRemovedEdges G (rectangleGraph a w h)
  let Mstar := rectangleSubgraphRemovedDualEdges hG
  let K := rectangleSubgraphDualOpenRemovedState hG H
  let e := rectangleSubgraphDualRemainingEquiv hG
  let d := rectangleSubgraphDualConfigurationEquiv hG
  let ξp := frozenBoundary (BoundaryCondition.free ∅) H.val
  let ξd := frozenBoundary (rectangleDualBoundaryCondition a w h) K.val
  let c := (positiveRectangleDualityFactor q p a w h *
    positiveRemovedWeight (dualParameter q p) Mstar K) /
      positiveRemovedWeight p M H
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos
      (mul_pos (positiveRectangleDualityFactor_pos hq hp hp1 a w h)
        (positiveRemovedWeight_pos_conditioned hq (dualParameter_pos hq hp hp1)
          (dualParameter_lt_one hq hp hp1) Mstar K))
      (positiveRemovedWeight_pos_conditioned hq hp hp1 M H)
  have hweight (A : Configuration G) :
      positiveFKWeight G q p ξp A = c *
        positiveFKWeight (rectangleSubgraphDualGraph hG) q (dualParameter q p)
          ξd (d A) := by
    let Arem := subgraphRemainingConfigurationEquiv hG A
    let Brem := e A
    let Δ := positiveRectangleDualConfigurationEquiv a w h
    have hprimalFactor := positiveFKWeight_union_frozen_factorization
      (q := q) (p := p) (ξ := BoundaryCondition.free ∅) (R := M)
      (A := Arem) H
    have hprimalRemain := positiveRemainingWeight_subgraph_conditioned
      (hG := hG) (q := q) (p := p) ξp A
    have hprimalHost :
        positiveFKWeight (rectangleGraph a w h) q p
          (BoundaryCondition.free ∅) (subgraphConfigurationEmbedding hG A ∪ H.val) =
          positiveFKWeight G q p ξp A * positiveRemovedWeight p M H := by
      have hEmbedSet : Arem.val = subgraphConfigurationEmbedding hG A := by
        exact subgraphRemainingConfigurationEquiv_val (hGH := hG) A
      have hUnion : subgraphConfigurationEmbedding hG A ∪ H.val =
          Arem.val ∪ H.val := by
        ext f
        simp only [Finset.mem_union]
        rw [hEmbedSet]
      calc
        _ = positiveFKWeight (rectangleGraph a w h) q p
              (BoundaryCondition.free ∅) (Arem.val ∪ H.val) :=
              congrArg (fun X : Configuration (rectangleGraph a w h) =>
                positiveFKWeight (rectangleGraph a w h) q p
                  (BoundaryCondition.free ∅) X) hUnion
        _ = positiveRemainingWeight q p
              (frozenBoundary (BoundaryCondition.free ∅) H.val) M Arem *
              positiveRemovedWeight p M H := by
              exact hprimalFactor
        _ = positiveRemainingWeight q p ξp M Arem *
              positiveRemovedWeight p M H := rfl
        _ = _ := by
          exact congrArg (fun x => x * positiveRemovedWeight p M H)
            hprimalRemain
    have hrect := positive_rectangle_weight_eq_factor_mul_dual_weight
      hq hp hp1 a w h (subgraphConfigurationEmbedding hG A ∪ H.val)
    have hdualDecomp := rectangleSubgraphDualConditioned_decomposition hG H A
    have hdualFactor := positiveFKWeight_union_frozen_factorization
      (q := q) (p := dualParameter q p)
      (ξ := rectangleDualBoundaryCondition a w h) (R := Mstar)
      (A := Brem) K
    have hdualHost :
        positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
          (rectangleDualBoundaryCondition a w h)
          (Δ (subgraphConfigurationEmbedding hG A ∪ H.val)) =
          positiveFKWeight (rectangleSubgraphDualGraph hG) q (dualParameter q p)
            ξd (d A) * positiveRemovedWeight (dualParameter q p) Mstar K := by
      have hdval : edgeRestrictionConfigurationEquiv
          (rectangleDualGraph a w h) Mstar (d A) = Brem := by
        change (edgeRestrictionConfigurationEquiv
          (rectangleDualGraph a w h) Mstar)
            ((edgeRestrictionConfigurationEquiv
              (rectangleDualGraph a w h) Mstar).symm (e A)) = e A
        exact Equiv.apply_symm_apply _ _
      have hdvalSet : Brem.val =
          (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
            Mstar (d A)).val := congrArg Subtype.val hdval.symm
      have hUnion :
          (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
            Mstar (d A)).val ∪ K.val = Brem.val ∪ K.val := by
        ext f
        simp only [Finset.mem_union]
        rw [hdvalSet]
      have hdualFactor' :
          positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
            (rectangleDualBoundaryCondition a w h)
            ((edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
              Mstar (d A)).val ∪ K.val) =
          positiveRemainingWeight q (dualParameter q p) ξd Mstar Brem *
            positiveRemovedWeight (dualParameter q p) Mstar K := by
        have hdualFactorHost :
            positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
              (rectangleDualBoundaryCondition a w h) (Brem.val ∪ K.val) =
            positiveRemainingWeight q (dualParameter q p)
              (frozenBoundary (rectangleDualBoundaryCondition a w h) K.val)
              Mstar Brem * positiveRemovedWeight (dualParameter q p) Mstar K := by
          exact hdualFactor
        calc
          _ = positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
                (rectangleDualBoundaryCondition a w h) (Brem.val ∪ K.val) :=
                congrArg (fun X : Configuration (rectangleDualGraph a w h) =>
                  positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
                    (rectangleDualBoundaryCondition a w h) X) hUnion
          _ = _ := by simpa only [ξd, K] using hdualFactorHost
      have hconfig : Δ (subgraphConfigurationEmbedding hG A ∪ H.val) =
          (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h) Mstar
            (d A)).val ∪ K.val := by
        rw [hdval]
        exact hdualDecomp
      calc
        _ = positiveFKWeight (rectangleDualGraph a w h) q (dualParameter q p)
              (rectangleDualBoundaryCondition a w h)
              ((edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
                Mstar (d A)).val ∪ K.val) := by rw [hconfig]
        _ = positiveRemainingWeight q (dualParameter q p) ξd Mstar Brem *
              positiveRemovedWeight (dualParameter q p) Mstar K := hdualFactor'
        _ = positiveRemainingWeight q (dualParameter q p) ξd Mstar
              (edgeRestrictionConfigurationEquiv (rectangleDualGraph a w h)
                Mstar (d A)) * positiveRemovedWeight (dualParameter q p) Mstar K := by
              rw [← hdval]
        _ = positiveFKWeight (rectangleSubgraphDualGraph hG) q
              (dualParameter q p) ξd (d A) *
              positiveRemovedWeight (dualParameter q p) Mstar K := by
              rw [positiveRemainingWeight, positiveFKWeight]
              rw [edgeRestriction_card,
                card_edgeRestrictionConfigurationEquiv,
                componentCount_edgeRestriction]
    have hmul := hrect
    rw [hprimalHost, hdualHost] at hmul
    have hremP : positiveRemovedWeight p M H ≠ 0 :=
      (positiveRemovedWeight_pos_conditioned hq hp hp1 M H).ne'
    have hremD : positiveRemovedWeight (dualParameter q p) Mstar K ≠ 0 :=
      (positiveRemovedWeight_pos_conditioned hq (dualParameter_pos hq hp hp1)
        (dualParameter_lt_one hq hp hp1) Mstar K).ne'
    dsimp [c]
    field_simp [hremP, hremD]
    nlinarith [hmul]
  unfold positiveFKLaw
  exact FiniteProbability.pmf_map_equiv_of_common_factor d c _ _ hc
    (positiveFKWeight_pos' hq hp hp1 ξp)
    (positiveFKWeight_pos' hq (dualParameter_pos hq hp hp1)
      (dualParameter_lt_one hq hp hp1) ξd)
    hweight

/-- Embedded form of the fixed-state dual law. The two partition identities
are the precise geometric inputs: the deleted primal state induces the source
boundary, and the complementary deleted-dual state induces the requested dual
boundary. -/
theorem positive_embedded_subgraph_conditioned_duality_law_of_partition_eq
    {V : Type*} [Finite V] {J : SimpleGraph V}
    (f : V ↪ RectangleVertex a w h)
    (hJ : J.map f ≤ rectangleGraph a w h)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges (J.map f) (rectangleGraph a w h)))
    (hξ : ξ.partition =
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary (BoundaryCondition.free ∅) H.val)).partition)
    (η : BoundaryCondition (RectangleDualVertex a w h))
    (hη : (frozenBoundary (rectangleDualBoundaryCondition a w h)
        (rectangleSubgraphDualOpenRemovedState hJ H).val).partition = η.partition) :
    (positiveFKLaw J q p hq hp hp1 ξ).map
        ((isolatedExtensionConfigurationEquiv J f).trans
          (rectangleSubgraphDualConfigurationEquiv hJ)) =
      positiveFKLaw (rectangleSubgraphDualGraph hJ) q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1) η := by
  classical
  let ξr := frozenBoundary (BoundaryCondition.free ∅) H.val
  let ξpull := isolatedExtensionPullbackBoundary f ξr
  let ξd := frozenBoundary (rectangleDualBoundaryCondition a w h)
    (rectangleSubgraphDualOpenRemovedState hJ H).val
  let ι := isolatedExtensionConfigurationEquiv J f
  let δ := rectangleSubgraphDualConfigurationEquiv hJ
  have hsource := positiveFKLaw_eq_of_partition_eq
    (G := J) hq hp hp1 ξ ξpull hξ
  have hembed := positiveFKLaw_isolatedExtension_map_boundary_pullback
    (G := J) f hq hp hp1 ξr
  have hrectangle := positive_subgraph_conditioned_duality_law
    (G := J.map f) hJ hq hp hp1 H
  have htarget := positiveFKLaw_eq_of_partition_eq
    (G := rectangleSubgraphDualGraph hJ) hq
      (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
      ξd η hη
  calc
    _ = (positiveFKLaw J q p hq hp hp1 ξpull).map (ι.trans δ) := by
      rw [hsource]
    _ = ((positiveFKLaw J q p hq hp hp1 ξpull).map ι).map δ := by
      rw [PMF.map_comp]
      rfl
    _ = (positiveFKLaw (J.map f) q p hq hp hp1 ξr).map δ := by
      rw [hembed]
    _ = positiveFKLaw (rectangleSubgraphDualGraph hJ) q (dualParameter q p)
          hq (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1) ξd := by
      simpa only [ξd, δ] using hrectangle
    _ = positiveFKLaw (rectangleSubgraphDualGraph hJ) q (dualParameter q p)
          hq (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1) η := htarget

/-- Embedded PD-law form at the explicit self-dual parameter. The two
partition equalities are the exact finite geometry obligations for a mixed
boundary subgraph and its complementary dual arcs. -/
theorem embedded_subgraph_conditioned_duality_law_PD_at_selfDualParameter_of_partition_eq
    {V : Type*} [Finite V] {J : SimpleGraph V}
    (f : V ↪ RectangleVertex a w h)
    (hJ : J.map f ≤ rectangleGraph a w h)
    (q : Set.Ici (1 : ℝ))
    (ξ : BoundaryCondition V)
    (H : RemovedConfiguration (rectangleGraph a w h)
      (subgraphRemovedEdges (J.map f) (rectangleGraph a w h)))
    (hξ : ξ.partition =
      (isolatedExtensionPullbackBoundary f
        (frozenBoundary (BoundaryCondition.free ∅) H.val)).partition)
    (η : BoundaryCondition (RectangleDualVertex a w h))
    (hη : (frozenBoundary (rectangleDualBoundaryCondition a w h)
        (rectangleSubgraphDualOpenRemovedState hJ H).val).partition = η.partition) :
    (law J (criticalParameters q) ξ).map
        ((isolatedExtensionConfigurationEquiv J f).trans
          (rectangleSubgraphDualConfigurationEquiv hJ)) =
      law (rectangleSubgraphDualGraph hJ) (criticalParameters q) η := by
  have hq : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one q.property
  rw [← positiveFKLaw_eq_PD_law (θ := criticalParameters q) (ξ := ξ)]
  rw [← positiveFKLaw_eq_PD_law
    (G := rectangleSubgraphDualGraph hJ) (θ := criticalParameters q) (ξ := η)]
  have hlaw := positive_embedded_subgraph_conditioned_duality_law_of_partition_eq
    (J := J) f hJ hq
    (squareRootDualityParameter_mem_Ioo hq).1
    (squareRootDualityParameter_mem_Ioo hq).2 ξ H hξ η hη
  have hfixed : dualParameter (↑q)
      (Real.sqrt (↑q) / (1 + Real.sqrt (↑q))) =
      Real.sqrt (↑q) / (1 + Real.sqrt (↑q)) := by
    simpa only [squareRootDualityParameter] using
      dualParameter_squareRoot_fixed hq
  simpa only [criticalParameters, edgeParameter, PD.rcCriticalParameter,
    squareRootDualityParameter, hfixed] using hlaw

end

end PottsContinuity.DualityExt
