/- Additive winding counterpart of the proved exponential recurrence.
Proof adapted from FKconvergence/Medial/ParafermionicCoverPathPhaseRecurrence.lean;
actual quarter-turn suffix sums replace exponentials. No q=4 limit is assumed.
-/
module

public import PottsContinuity.Thm4.PathPhase
public import PottsContinuity.Thm4.DirectedPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial SimpleGraph
noncomputable section

def windingOfWalk (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (z : ParafermionicCoverFinitePort n × Bool) : ℝ :=
  if hz : z ∈ p.support then
    (Real.pi / 2) *
      (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil z hz) : ℝ)
  else 0

private theorem dart_snd_mem_support_of_mem_darts
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} :
    ∀ (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.snd ∈ p.support
  | .nil, d, hd => by simp at hd
  | .cons h p, d, hd => by
      simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
      rcases hd with hd | hd
      · cases hd
        simp [SimpleGraph.Walk.support_cons]
      · exact List.mem_cons_of_mem _ (dart_snd_mem_support_of_mem_darts p hd)

private theorem windingOfWalk_darts_recurrence
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hp : p.IsPath) :
    ∀ d ∈ p.darts,
      windingOfWalk n hn A p d.fst =
        (Real.pi / 2) * (parafermionicCoverFinitePairingStepTurn n A d.fst d.snd : ℝ) +
          windingOfWalk n hn A p d.snd := by
  induction p with
  | nil => intro d hd; simp at hd
  | @cons x y z hxy tail ih =>
      intro d hd
      have htailPath : tail.IsPath := hp.of_cons
      have hxNotTail : x ∉ tail.support :=
        (SimpleGraph.Walk.cons_isPath_iff hxy tail).mp hp |>.2
      have hxyne : x ≠ y := hxy.ne
      simp only [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
      rcases hd with hd | hd
      · cases hd
        have hxMem : x ∈ (SimpleGraph.Walk.cons hxy tail).support := by simp
        have hyMem : y ∈ (SimpleGraph.Walk.cons hxy tail).support := by
          exact List.mem_cons_of_mem _ tail.start_mem_support
        have hdropX : (SimpleGraph.Walk.cons hxy tail).dropUntil x hxMem =
            SimpleGraph.Walk.cons hxy tail :=
          SimpleGraph.Walk.dropUntil_first _ _
        have hdropY : (SimpleGraph.Walk.cons hxy tail).dropUntil y hyMem = tail := by
          simp [SimpleGraph.Walk.dropUntil, hxyne]
        have hturn : parafermionicCoverFinitePairingWalkTurn n hn A
            (SimpleGraph.Walk.cons hxy tail) =
            parafermionicCoverFinitePairingStepTurn n A x y +
              parafermionicCoverFinitePairingWalkTurn n hn A tail := by
          simp [parafermionicCoverFinitePairingWalkTurn,
            SimpleGraph.Walk.darts_cons, List.sum_cons]
        have hmul : (Real.pi / 2) *
              ((parafermionicCoverFinitePairingStepTurn n A x y +
                parafermionicCoverFinitePairingWalkTurn n hn A tail : ℤ) : ℝ) =
            (Real.pi / 2) * (parafermionicCoverFinitePairingStepTurn n A x y : ℝ) +
              (Real.pi / 2) * (parafermionicCoverFinitePairingWalkTurn n hn A tail : ℝ) := by
          push_cast
          ring
        unfold windingOfWalk
        rw [dite_eq_left hxMem, dite_eq_left hyMem, hdropX, hdropY,
          hturn, hmul]
      · have hfst : d.fst ∈ tail.support :=
          SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts tail hd
        have hsnd : d.snd ∈ tail.support :=
          dart_snd_mem_support_of_mem_darts tail hd
        have hfstP : d.fst ∈ (SimpleGraph.Walk.cons hxy tail).support :=
          List.mem_cons_of_mem _ hfst
        have hsndP : d.snd ∈ (SimpleGraph.Walk.cons hxy tail).support :=
          List.mem_cons_of_mem _ hsnd
        have hxfst : x ≠ d.fst := by
          intro h
          exact hxNotTail (h ▸ hfst)
        have hxSnd : x ≠ d.snd := by
          intro h
          exact hxNotTail (h ▸ hsnd)
        have hdropF : (SimpleGraph.Walk.cons hxy tail).dropUntil d.fst hfstP =
            tail.dropUntil d.fst hfst := by
          simp [SimpleGraph.Walk.dropUntil, hxfst]
        have hdropS : (SimpleGraph.Walk.cons hxy tail).dropUntil d.snd hsndP =
            tail.dropUntil d.snd hsnd := by
          simp [SimpleGraph.Walk.dropUntil, hxSnd]
        have heqF : windingOfWalk n hn A (SimpleGraph.Walk.cons hxy tail) d.fst =
            windingOfWalk n hn A tail d.fst := by
          simp [windingOfWalk, hfst, hdropF]
        have heqS : windingOfWalk n hn A (SimpleGraph.Walk.cons hxy tail) d.snd =
            windingOfWalk n hn A tail d.snd := by
          simp [windingOfWalk, hsnd, hdropS]
        rw [heqF, heqS]
        exact ih htailPath d hd

theorem parafermionicCoverPathWindingAtom_darts_recurrence
    (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    ∀ d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts,
      parafermionicCoverPathWindingAtom n hn A d.fst =
        (Real.pi / 2) * (parafermionicCoverFinitePairingStepTurn n A d.fst d.snd : ℝ) +
          parafermionicCoverPathWindingAtom n hn A d.snd := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hrec := windingOfWalk_darts_recurrence n hn A p hp
  simpa [parafermionicCoverPathWindingAtom, windingOfWalk, p] using hrec

end
end PottsContinuity.Thm4
