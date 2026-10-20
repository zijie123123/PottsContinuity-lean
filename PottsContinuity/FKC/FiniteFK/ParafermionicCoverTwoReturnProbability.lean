-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverTwoReturnProbability.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverTwoReturnNonconnection
public import PottsContinuity.FKC.FiniteFK.CriticalEdgeToggle
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverAtomicDefectToggle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
noncomputable section

local instance parafermionicCoverTwoReturnProbabilityEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

/-- Under free boundary, a closed two-return edge toggle has the reciprocal
critical FK mass ratio. The endpoints are the seed and actual open-pair port;
nonconnection is proved for actual open paths. -/
theorem parafermionicCoverFiniteEdgeCutTwoReturn_free_toggle_probability
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) * loopWeight q =
      configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A := by
  let G := ParafermionicAmbientGraph n
  let u := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e)
  let v := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort
  have hnonconn := parafermionicCoverClosedTwoReturn_not_actualConnected
    n hn A e hclosed hπ0 hπ1
  have hpair := parafermionicCoverFiniteEdgeCutSelectedEdge_eq_seedOpenPort_endpoints n hn e
  have huv : G.Adj u v := by
    apply G.mem_edgeSet.mp
    dsimp [u, v]
    rw [← hpair]
    exact e.property
  have hedge : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) = e :=
    Subtype.ext hpair.symm
  have hne : ¬ (componentSetoid G
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A).r u v := by
    rw [componentSetoid_free]
    exact hnonconn
  have hratio := configurationProbability_insert_mul_loopWeight_of_not_related
    q (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A huv
      (by simpa [hedge] using hclosed) hne
  have htoggle : insert e A = toggleEdgeConfiguration e A := by
    ext f
    simp [toggleEdgeConfiguration, hclosed]
  rw [← htoggle]
  simpa [toggleEdgeConfiguration, hclosed, hedge] using hratio

/-- The actual closed two-return atomic defect cancels in pairs when weighted
by its normalized finite FK probabilities under free boundary. -/
theorem parafermionicCoverContourFiniteEdgeAtomicDefect_two_return_free_probability_pair_cancel
    (n : ℕ) (hn : 1 ≤ n) (q : ClusterWeight)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (hclosed : e ∉ A)
    (hπ0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (hπ1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
      (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
          (toggleEdgeConfiguration e A) = 0 := by
  have hprob := parafermionicCoverFiniteEdgeCutTwoReturn_free_toggle_probability
    n hn q A e hclosed hπ0 hπ1
  have hprob' : (configurationProbability (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
      A : ℂ) =
      (loopWeight q : ℂ) *
        (configurationProbability (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
          (toggleEdgeConfiguration e A) : ℂ) := by
    calc
      _ = (configurationProbability (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
          (toggleEdgeConfiguration e A) : ℂ) * (loopWeight q : ℂ) := by
        exact_mod_cast hprob.symm
      _ = _ := by ring

  have hdef := parafermionicCoverContourFiniteEdgeAtomicDefect_toggle_closed_return_two
    q n hn A e hclosed hπ0 hπ1
  calc
    _ = (configurationProbability (ParafermionicAmbientGraph n) q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) : ℂ) *
        ((loopWeight q : ℂ) * parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
          parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
            (toggleEdgeConfiguration e A)) := by
      rw [hprob']
      ring
    _ = 0 := by
      rw [show (loopWeight q : ℂ) *
        parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e A +
          parafermionicCoverContourFiniteEdgeAtomicDefect q n hn e
            (toggleEdgeConfiguration e A) = 0 by linear_combination hdef]
      simp

end
end PottsContinuity.FKC.FiniteFK
