module

public import PottsContinuity.DualityExt.PositiveInducedWiredDuality
public import PottsContinuity.DualityExt.PositiveDualSubgraphEdgeState
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

/-- Edge labels on an active carrier agree with the edges on its full graph. -/
noncomputable def positiveActiveEdgeToGraphEquiv {V : Type*} [Finite V]
    (H : SimpleGraph V) :
    (positiveActiveGraph H).edgeSet ≃ H.edgeSet :=
  (isolatedExtensionEdgeEquiv (positiveActiveGraph H)
      (positiveActiveInclusion H)).trans
    (Set.equivOfEq (congrArg (fun G : SimpleGraph V => G.edgeSet)
      (positiveActiveGraph_map_subtype H)))

theorem configurationCast_setEq_eq_edgeMap {α : Type*} (s t : Set α) (h : s = t)
    (A : Finset s) :
    Equiv.cast (congrArg (fun r : Set α => Finset r) h) A =
      A.map (Set.equivOfEq h).toEmbedding := by
  cases h
  have he : Set.equivOfEq (rfl : s = s) = Equiv.refl s := by
    ext x
    rfl
  rw [he]
  simp

/-- The active-carrier configuration equivalence preserves the state at the
edge with the corresponding full-carrier label. -/
theorem positiveActiveConfigurationEquiv_apply_edgeMap {V : Type*} [Finite V]
    (H : SimpleGraph V) (C : Configuration (positiveActiveGraph H)) :
    positiveActiveConfigurationEquiv H C =
      C.map (positiveActiveEdgeToGraphEquiv H).toEmbedding := by
  have hEdge : ((positiveActiveGraph H).map
      (positiveActiveInclusion H)).edgeSet = H.edgeSet :=
    congrArg (fun J : SimpleGraph V => J.edgeSet)
      (positiveActiveGraph_map_subtype H)
  change Equiv.cast (congrArg (fun s : Set (Sym2 V) => Finset s) hEdge)
      (C.map (isolatedExtensionEdgeEquiv (positiveActiveGraph H)
        (positiveActiveInclusion H)).toEmbedding) = _
  rw [configurationCast_setEq_eq_edgeMap ((positiveActiveGraph H).map
      (positiveActiveInclusion H)).edgeSet H.edgeSet hEdge]
  simp [positiveActiveEdgeToGraphEquiv, Finset.map_map]

/-- The active-carrier configuration equivalence preserves each named edge
state. -/
theorem positiveActiveConfigurationEquiv_edgeState {V : Type*} [Finite V]
    (H : SimpleGraph V) (C : Configuration (positiveActiveGraph H))
    (g : (positiveActiveGraph H).edgeSet) :
    positiveActiveEdgeToGraphEquiv H g ∈ positiveActiveConfigurationEquiv H C ↔
      g ∈ C := by
  rw [positiveActiveConfigurationEquiv_apply_edgeMap]
  simp

/-- The wired subgraph-dual configuration map reverses the state at the
corresponding active dual edge. -/
theorem positiveWiredSubgraphDualConfigurationEquiv_edgeState
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    {W : Type*} [Finite W]
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃ W)
    (C : Configuration ((positiveActiveGraph
      (rectangleSubgraphDualGraph hK)).map e.toEmbedding))
    (k : K.edgeSet) :
    k ∈ positiveWiredSubgraphDualConfigurationEquiv hK e C ↔
      (isolatedExtensionEdgeEquiv
        (positiveActiveGraph (rectangleSubgraphDualGraph hK)) e.toEmbedding
        ((positiveActiveEdgeToGraphEquiv
          (rectangleSubgraphDualGraph hK)).symm
          (rectangleSubgraphDualEdgeEmbedding hK k))) ∉ C := by
  classical
  let H := rectangleSubgraphDualGraph hK
  let G := positiveActiveGraph H
  let d := rectangleSubgraphDualEdgeEmbedding hK k
  let g := (positiveActiveEdgeToGraphEquiv H).symm d
  let gm := isolatedExtensionEdgeEquiv G e.toEmbedding g
  let E := positiveWiredSubgraphDualConfigurationEquiv hK e
  let AEquiv := positiveActiveConfigurationEquiv H
  let I := isolatedExtensionConfigurationEquiv G e.toEmbedding
  let D := rectangleSubgraphDualConfigurationEquiv hK
  have hstate := rectangleSubgraphDualConfigurationEquiv_edgeState hK (E C) k
  have hF : I (AEquiv.symm (D (E C))) = C := by
    change E.symm (E C) = C
    exact E.symm_apply_apply C
  have hA : AEquiv.symm (D (E C)) = I.symm C := by
    apply I.injective
    calc
      I (AEquiv.symm (D (E C))) = C := hF
      _ = I (I.symm C) := (I.apply_symm_apply C).symm
  have hD : D (E C) = AEquiv (I.symm C) := by
    calc
      D (E C) = AEquiv (AEquiv.symm (D (E C))) :=
        (AEquiv.apply_symm_apply (D (E C))).symm
      _ = AEquiv (I.symm C) := congrArg AEquiv hA
  have hActVal := positiveActiveConfigurationEquiv_apply_edgeMap H (I.symm C)
  have hDualState : d ∈ D (E C) ↔ gm ∈ C := by
    rw [hD, hActVal]
    change d ∈ Finset.map _ _ ↔ gm ∈ C
    rw [Finset.mem_map_equiv]
    change g ∈ I.symm C ↔ gm ∈ C
    have hIinv : I.symm C = C.map
        (isolatedExtensionEdgeEquiv G e.toEmbedding).symm.toEmbedding := by
      apply Finset.ext
      intro x
      simp only [I, isolatedExtensionConfigurationEquiv,
        Equiv.finsetCongr_symm, Equiv.finsetCongr_apply,
        Finset.mem_map_equiv]
    rw [hIinv]
    change g ∈ Finset.map _ _ ↔ gm ∈ C
    rw [Finset.mem_map_equiv]
    rfl
  have hstate' : d ∈ D (E C) ↔ k ∉ E C := by
    simpa only [d, D] using hstate
  have hopen : k ∈ E C ↔ d ∉ D (E C) := by
    constructor
    · intro hk hd
      exact (hstate'.mp hd) hk
    · intro hd
      by_contra hk
      exact hd (hstate'.mpr hk)
  change k ∈ E C ↔ gm ∉ C
  exact hopen.trans (not_congr hDualState)

end

end PottsContinuity.DualityExt
