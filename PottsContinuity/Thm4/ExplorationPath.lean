/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverExplorationSupport.lean`.
Adaptation: namespace/import relocation only; path chosen from proved unique existence.
-/
module

public import PottsContinuity.Thm4.Exploration
public import PottsContinuity.Thm4.PrimalConnectivity
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

theorem parafermionicCoverFiniteCornerCutPairingGraph_le
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverFiniteCornerCutPairingGraph n hn A ≤
      parafermionicCoverFinitePairingGraph n A := by
  let L := parafermionicCoverFiniteLocalPairPerm n A
  let B := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let hL := parafermionicCoverFiniteLocalPairPerm_involutive n A
  let hB := parafermionicCoverFiniteCornerPairPerm_involutive n
  let C := pairingSingleCutPerm B s hB
  let hC := pairingSingleCut_involutive B s hB
  intro u v hadj
  change (pairingGraph L C hL hC).Adj u v at hadj
  change (pairingGraph L B hL hB).Adj u v
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv
  · exact (@pairingGraph_adj_false_false _ L B hL hB u v).2
      ((@pairingGraph_adj_false_false _ L C hL hC u v).mp hadj)
  · exact (@pairingGraph_adj_false_true _ L B hL hB u v).2
      ((@pairingGraph_adj_false_true _ L C hL hC u v).mp hadj)
  · exact (@pairingGraph_adj_true_false _ L B hL hB u v).2
      ((@pairingGraph_adj_true_false _ L C hL hC u v).mp hadj)
  · have hcut := (@pairingGraph_adj_true_true _ L C hL hC u v).mp hadj
    have hnot : ¬ (u = s ∨ u = B s) := by
      intro hu
      have hfix : C u = u :=
        (pairingSingleCutPerm_fixed_iff B s u hB
          (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n)).2 hu
      exact hcut.2 (hcut.1.symm.trans hfix).symm
    have happly : C u = B u := by
      change pairingSingleCut B s u = B u
      simp [pairingSingleCut, hnot]
    exact (@pairingGraph_adj_true_true _ L B hL hB u v).2
      ⟨happly.symm.trans hcut.1, hcut.2⟩

/-- The unique actual open path in the finite corner-cut pairing graph, chosen
with its literal origin-port endpoints. -/
def parafermionicCoverFiniteOriginExplorationPath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteOriginCornerPort n hn, true)
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) :=
  Classical.choose (parafermionicCoverFiniteCornerCut_existsUnique_isPath n hn A)

theorem parafermionicCoverFiniteOriginExplorationPath_isPath (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    (parafermionicCoverFiniteOriginExplorationPath n hn A).IsPath :=
  (Classical.choose_spec (parafermionicCoverFiniteCornerCut_existsUnique_isPath n hn A)).1

theorem parafermionicCoverFiniteOriginExplorationPath_support_actualConnected
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {z : ParafermionicCoverFinitePort n × Bool}
    (hz : z ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteOriginCornerPort n hn))
      (parafermionicCoverFinitePortPrimalVertex n z.1) := by
  classical
  obtain ⟨q, r, hdecomp⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_append).mp hz
  have hq := q.mapLe (parafermionicCoverFiniteCornerCutPairingGraph_le n hn A)
  have hconn := parafermionicCoverFinitePairingWalk_actualConnected n A hq
  simpa [SimpleGraph.Walk.mapLe] using hconn

end
end PottsContinuity.Thm4
