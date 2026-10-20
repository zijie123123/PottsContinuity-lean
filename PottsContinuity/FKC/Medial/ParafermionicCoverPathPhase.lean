-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverPathPhase.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport
public import PottsContinuity.FKC.ParafermionicBoundaryPhase
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial SimpleGraph
noncomputable section

private theorem walk_dropUntil_end_eq_nil {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.dropUntil v p.end_mem_support = SimpleGraph.Walk.nil := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
      have htail : p.IsPath := hp.of_cons
      have hnot : a ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff hab p).mp hp |>.2
      have hne : a ≠ c := by
        intro hac
        exact hnot (hac ▸ p.end_mem_support)
      simp [SimpleGraph.Walk.dropUntil, hne, ih htail]

/-- The phase carried by the actual selected exploration path's suffix from a
layered port. Vertices outside the actual path support receive zero. -/
def parafermionicCoverPathPhaseAtom (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (z : ParafermionicCoverFinitePort n × Bool) : ℂ :=
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  if hz : z ∈ p.support then
    Complex.exp (Complex.I *
      (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil z hz) : ℝ)))
  else 0

theorem parafermionicCoverPathPhaseAtom_norm (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (z : ParafermionicCoverFinitePort n × Bool) :
    ‖parafermionicCoverPathPhaseAtom q n hn A z‖ =
      if z ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support then 1 else 0 := by
  simp only [parafermionicCoverPathPhaseAtom]
  split_ifs with hz
  · convert Complex.norm_exp_I_mul_ofReal
        (parafermionicBoundarySpin q * (Real.pi / 2) *
          (parafermionicCoverFinitePairingWalkTurn n hn A
            ((parafermionicCoverFiniteOriginExplorationPath n hn A).dropUntil z hz) : ℝ))
      using 1; push_cast; ring
  · simp

theorem parafermionicCoverPathPhaseAtom_source (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteOriginCornerPort n hn, true) =
    Complex.exp (Complex.I *
      (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFinitePairingWalkTurn n hn A
          (parafermionicCoverFiniteOriginExplorationPath n hn A) : ℝ))) := by
  simp [parafermionicCoverPathPhaseAtom, SimpleGraph.Walk.dropUntil_first,
    parafermionicCoverFiniteOriginExplorationPath]

theorem parafermionicCoverPathPhaseAtom_target (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) = 1 := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hend := p.end_mem_support
  have hdrop := walk_dropUntil_end_eq_nil _ p hp
  have hturn : parafermionicCoverFinitePairingWalkTurn n hn A
      (p.dropUntil _ hend) = 0 := by
    rw [hdrop]
    simp [parafermionicCoverFinitePairingWalkTurn]
  simp [parafermionicCoverPathPhaseAtom, p, hend, hturn]

end
end PottsContinuity.FKC.FiniteFK
