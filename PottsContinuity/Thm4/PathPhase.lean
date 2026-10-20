/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverPathPhase.lean`.
Adaptation: closed real [1,4] parameter; separate actual winding atom for q=4.
The exponential phase at q=4 is a visit indicator, not the source winding observable.
-/
module

public import PottsContinuity.Thm4.WalkTurn
public import PottsContinuity.Thm4.ExplorationPath
public import PottsContinuity.Thm4.BoundaryPhase
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial SimpleGraph
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
def parafermionicCoverPathPhaseAtom (q : Set.Icc (1 : ℝ) 4) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (z : ParafermionicCoverFinitePort n × Bool) : ℂ :=
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  if hz : z ∈ p.support then
    Complex.exp (Complex.I *
      (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil z hz) : ℝ)))
  else 0

theorem parafermionicCoverPathPhaseAtom_norm (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
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
      using 1
    push_cast
    ring
  · simp

theorem parafermionicCoverPathPhaseAtom_source (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverPathPhaseAtom q n hn A
      (parafermionicCoverFiniteOriginCornerPort n hn, true) =
    Complex.exp (Complex.I *
      (parafermionicBoundarySpin q * (Real.pi / 2) *
        (parafermionicCoverFinitePairingWalkTurn n hn A
          (parafermionicCoverFiniteOriginExplorationPath n hn A) : ℝ))) := by
  simp [parafermionicCoverPathPhaseAtom, SimpleGraph.Walk.dropUntil_first,
    parafermionicCoverFiniteOriginExplorationPath]

theorem parafermionicCoverPathPhaseAtom_target (q : Set.Icc (1 : ℝ) 4) (n : ℕ)
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

/-- The actual exploration suffix winding, in radians, with zero off its support
as in DCST TeX 1917-1922. No winding value is imposed on a visited port. -/
def parafermionicCoverPathWindingAtom (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (z : ParafermionicCoverFinitePort n × Bool) : ℝ :=
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  if hz : z ∈ p.support then
    (Real.pi / 2) * (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil z hz) : ℝ)
  else 0

/-- The endpoint winding is zero, since its suffix is the empty walk. -/
lemma parafermionicCoverPathWindingAtom_target (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverPathWindingAtom n hn A
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) = 0 := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hend := p.end_mem_support
  have hdrop := walk_dropUntil_end_eq_nil _ p hp
  simp only [parafermionicCoverPathWindingAtom]
  change (if hz : _ ∈ p.support then
    (Real.pi / 2) * (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil _ hz) : ℝ)
    else 0) = 0
  rw [dite_eq_left hend, hdrop]
  simp only [parafermionicCoverFinitePairingWalkTurn, SimpleGraph.Walk.darts_nil,
    List.map_nil, List.sum_nil, Int.cast_zero, mul_zero]

/-- The literal source modified observable integrand on the actual finite path.
The q=4 branch is winding, not the exponential-phase limit. -/
def parafermionicCoverModifiedPathAtom (q : Set.Icc (1 : ℝ) 4)
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (z : ParafermionicCoverFinitePort n × Bool) : ℂ :=
  if q.val = 4 then (parafermionicCoverPathWindingAtom n hn A z : ℂ)
  else parafermionicCoverPathPhaseAtom q n hn A z

end
end PottsContinuity.Thm4
