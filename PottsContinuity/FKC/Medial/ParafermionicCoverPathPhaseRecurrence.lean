-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverPathPhaseRecurrence.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPathPhase
public import PottsContinuity.FKC.Medial.ParafermionicCoverDirectedPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial SimpleGraph
noncomputable section

 def phaseOfWalk (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (z : ParafermionicCoverFinitePort n × Bool) : ℂ :=
  if hz : z ∈ p.support then
    Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
      (parafermionicCoverFinitePairingWalkTurn n hn A (p.dropUntil z hz) : ℝ)))
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

private theorem phaseOfWalk_darts_recurrence
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (hp : p.IsPath) :
    ∀ d ∈ p.darts,
      phaseOfWalk q n hn A p d.fst =
        Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
          (parafermionicCoverFinitePairingStepTurn n A d.fst d.snd : ℝ))) *
          phaseOfWalk q n hn A p d.snd := by
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
        have hmul : Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
              ((parafermionicCoverFinitePairingStepTurn n A x y +
                parafermionicCoverFinitePairingWalkTurn n hn A tail : ℤ) : ℝ)) =
            Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
              (parafermionicCoverFinitePairingStepTurn n A x y : ℝ)) +
            Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
              (parafermionicCoverFinitePairingWalkTurn n hn A tail : ℝ)) := by
          push_cast
          ring
        unfold phaseOfWalk
        rw [dite_eq_left hxMem, dite_eq_left hyMem, hdropX, hdropY,
          hturn, hmul, Complex.exp_add]
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
        have heqF : phaseOfWalk q n hn A (SimpleGraph.Walk.cons hxy tail) d.fst =
            phaseOfWalk q n hn A tail d.fst := by
          simp [phaseOfWalk, hfst, hdropF]
        have heqS : phaseOfWalk q n hn A (SimpleGraph.Walk.cons hxy tail) d.snd =
            phaseOfWalk q n hn A tail d.snd := by
          simp [phaseOfWalk, hsnd, hdropS]
        rw [heqF, heqS]
        exact ih htailPath d hd

theorem parafermionicCoverPathPhaseAtom_darts_recurrence
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    ∀ d ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).darts,
      parafermionicCoverPathPhaseAtom q n hn A d.fst =
        Complex.exp (Complex.I * (parafermionicBoundarySpin q * (Real.pi / 2) *
          (parafermionicCoverFinitePairingStepTurn n A d.fst d.snd : ℝ))) *
          parafermionicCoverPathPhaseAtom q n hn A d.snd := by
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hp : p.IsPath := parafermionicCoverFiniteOriginExplorationPath_isPath n hn A
  have hrec := phaseOfWalk_darts_recurrence q n hn A p hp
  simpa [parafermionicCoverPathPhaseAtom, phaseOfWalk, p] using hrec

end
end PottsContinuity.FKC.FiniteFK
