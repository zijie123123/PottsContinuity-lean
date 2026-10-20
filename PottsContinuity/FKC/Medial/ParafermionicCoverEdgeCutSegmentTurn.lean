-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutSegmentTurn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutPathSystem
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutTurnInvariant
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance edgeCutSegmentTurnPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := parafermionicCoverFinitePortFintype n

local instance edgeCutSegmentTurnGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

theorem parafermionicCoverFiniteEdgeCutSourcePath_toggle_transport_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    ((parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).mapLe
      (le_of_eq (parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e))).copy rfl
        (congrArg Subtype.val
          (parafermionicCoverFiniteEdgeCutPartner_toggle_eq n hn A e
            (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1)) =
      parafermionicCoverFiniteEdgeCutSourcePath n hn
        (toggleEdgeConfiguration e A) e i := by
  let q := ((parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).mapLe
      (le_of_eq (parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e))).copy rfl
        (congrArg Subtype.val
          (parafermionicCoverFiniteEdgeCutPartner_toggle_eq n hn A e
            (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1))
  have hq : q.IsPath := by
    simpa [q, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_mapLe_eq_support] using
        parafermionicCoverFiniteEdgeCutSourcePath_isPath n hn A e i
  exact parafermionicCoverFiniteEdgeCutSourcePath_unique n hn
    (toggleEdgeConfiguration e A) e i q hq

private theorem edgeCutSegmentTurn_mapLe_trans
    {V : Type*} {G H K : SimpleGraph V} (h₁ : G ≤ H) (h₂ : H ≤ K)
    {u v : V} (p : G.Walk u v) :
    (p.mapLe h₁).mapLe h₂ = p.mapLe (le_trans h₁ h₂) := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      simp [SimpleGraph.Walk.mapLe, ih]

def parafermionicCoverFiniteEdgeCutSourceSegmentTurn (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) : ℤ :=
  parafermionicCoverFinitePairingWalkTurn n hn A
    ((parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).mapLe
      (by
        intro x y hxy
        exact hxy.1))


theorem parafermionicCoverFiniteEdgeCutSourceSegmentTurn_toggle_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn A e i =
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn n hn
        (toggleEdgeConfiguration e A) e i := by
  let hgraph : parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteEdgeCutGraph n hn (toggleEdgeConfiguration e A) e :=
    le_of_eq (parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e)
  let hA : parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn A := fun _ _ h => h.1
  let hT : parafermionicCoverFiniteEdgeCutGraph n hn (toggleEdgeConfiguration e A) e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn (toggleEdgeConfiguration e A) :=
    fun _ _ h => h.1
  let hAT : parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn (toggleEdgeConfiguration e A) :=
    le_trans hgraph hT
  let p := parafermionicCoverFiniteEdgeCutSourcePath n hn A e i
  let q := (p.mapLe hgraph).copy rfl
      (congrArg Subtype.val
        (parafermionicCoverFiniteEdgeCutPartner_toggle_eq n hn A e
          (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1)
        : (parafermionicCoverFiniteEdgeCutPartner n hn A e
            (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1 =
          (parafermionicCoverFiniteEdgeCutPartner n hn
            (toggleEdgeConfiguration e A) e
            (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1)
  have htransport : q =
      parafermionicCoverFiniteEdgeCutSourcePath n hn
        (toggleEdgeConfiguration e A) e i := by
    dsimp [q, p]
    exact parafermionicCoverFiniteEdgeCutSourcePath_toggle_transport_eq n hn A e i
  have hpartner := congrArg Subtype.val
    (parafermionicCoverFiniteEdgeCutPartner_toggle_eq n hn A e
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1)
  have hmap : q.mapLe hT = (p.mapLe hAT).copy rfl hpartner := by
    change ((p.mapLe hgraph).copy rfl hpartner).map (SimpleGraph.Hom.ofLE hT) =
      (p.mapLe hAT).copy rfl hpartner
    rw [SimpleGraph.Walk.map_copy]
    have hcomp : (p.mapLe hgraph).map (SimpleGraph.Hom.ofLE hT) = p.mapLe hAT := by
      change (p.mapLe hgraph).map (SimpleGraph.Hom.ofLE hT) =
        p.mapLe (le_trans hgraph hT)
      exact edgeCutSegmentTurn_mapLe_trans hgraph hT p
    rw [hcomp]
  have hcanonical := congrArg
      (fun w => parafermionicCoverFinitePairingWalkTurn n hn
        (toggleEdgeConfiguration e A) (w.mapLe hT)) htransport
  rw [parafermionicCoverFiniteEdgeCutSourceSegmentTurn,
      parafermionicCoverFiniteEdgeCutSourceSegmentTurn]
  change parafermionicCoverFinitePairingWalkTurn n hn A (p.mapLe hA) =
    parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A)
      ((parafermionicCoverFiniteEdgeCutSourcePath n hn
        (toggleEdgeConfiguration e A) e i).mapLe hT)
  rw [← hcanonical]
  rw [hmap]
  have hcopy : parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A) ((p.mapLe hAT).copy rfl hpartner) =
    parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A) (p.mapLe hAT) := by
    simp [parafermionicCoverFinitePairingWalkTurn, SimpleGraph.Walk.darts_copy]
  rw [hcopy]
  exact parafermionicCoverFiniteEdgeCutWalkTurn_toggle_eq n hn A e p

end
end PottsContinuity.FKC.FiniteFK
