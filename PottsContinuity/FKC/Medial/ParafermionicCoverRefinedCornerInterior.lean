-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedCornerInterior.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerPath
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedOwner
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- The strict interior vertices of the canonical four-edge corner route. -/
def parafermionicCoverRefinedCornerWalkInterior
    (c : ParafermionicCoverPort) : List ParafermionicCoverVertex :=
  (parafermionicCoverRefinedCornerWalk c).support.tail.dropLast

theorem parafermionicCoverRefinedCornerWalkInterior_eq
    (c : ParafermionicCoverPort) :
    parafermionicCoverRefinedCornerWalkInterior c =
      [parafermionicCoverRefinedCornerMid₁ c,
       parafermionicCoverRefinedCornerElbow c,
       parafermionicCoverRefinedCornerMid₂ c] := by
  simp [parafermionicCoverRefinedCornerWalkInterior]

theorem parafermionicCoverRefinedCornerInterior_owner
    (c : ParafermionicCoverPort) {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedCornerWalkInterior c) :
    parafermionicCoverRefinedCoarseOwner z = parafermionicCoverPortVertex c := by
  rw [parafermionicCoverRefinedCornerWalkInterior_eq] at hz
  simp only [List.mem_cons, List.not_mem_nil] at hz
  rcases hz with h | h | h | h
  all_goals try subst z
  all_goals try contradiction
  all_goals
    rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCoarseOwner,
        parafermionicCoverPortVertex,
        parafermionicCoverRefinedCornerMid₁,
        parafermionicCoverRefinedCornerMid₂,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverCornerPair, parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical, LatticePort.cornerPair,
        LatticePort.primalVertex, LatticeBond.endpoint,
        LatticeBond.source, LatticeBond.target] <;> omega

theorem parafermionicCoverRefinedCornerInterior_offset_small
    (c : ParafermionicCoverPort) {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedCornerWalkInterior c) :
    -2 ≤ z.1.1 - (9 * (parafermionicCoverPortVertex c).1.1 - 4) ∧
      z.1.1 - (9 * (parafermionicCoverPortVertex c).1.1 - 4) ≤ 2 ∧
    -2 ≤ z.1.2 - (9 * (parafermionicCoverPortVertex c).1.2 + 4) ∧
      z.1.2 - (9 * (parafermionicCoverPortVertex c).1.2 + 4) ≤ 2 := by
  rw [parafermionicCoverRefinedCornerWalkInterior_eq] at hz
  simp only [List.mem_cons, List.not_mem_nil] at hz
  rcases hz with h | h | h | h
  all_goals try subst z
  all_goals try contradiction
  all_goals
    rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverPortVertex,
        parafermionicCoverRefinedCornerMid₁,
        parafermionicCoverRefinedCornerMid₂,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverCornerPair, parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical, LatticePort.cornerPair,
        LatticePort.primalVertex, LatticeBond.endpoint,
        LatticeBond.source, LatticeBond.target] <;> omega

theorem parafermionicCoverRefinedPortEmbedding_offset_large
    (d : ParafermionicCoverPort) (layer : Bool) :
    let z := parafermionicCoverRefinedPortEmbedding (d, layer)
    let v := parafermionicCoverPortVertex d
    z.1.1 - (9 * v.1.1 - 4) ≤ -3 ∨ 3 ≤ z.1.1 - (9 * v.1.1 - 4) ∨
      z.1.2 - (9 * v.1.2 + 4) ≤ -3 ∨ 3 ≤ z.1.2 - (9 * v.1.2 + 4) := by
  rcases d with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;> cases layer <;>
    simp [parafermionicCoverPortVertex, parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical, LatticePort.primalVertex,
      LatticeBond.endpoint, LatticeBond.source, LatticeBond.target] <;> omega

theorem parafermionicCoverRefinedCornerInterior_ne_portEmbedding
    (c d : ParafermionicCoverPort) (layer : Bool)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedCornerWalkInterior c) :
    z ≠ parafermionicCoverRefinedPortEmbedding (d, layer) := by
  intro h
  have hzc := parafermionicCoverRefinedCornerInterior_owner c hz
  have hdc := parafermionicCoverRefinedCoarseOwner_portEmbedding d layer
  have howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d := by
    calc
      parafermionicCoverPortVertex c = parafermionicCoverRefinedCoarseOwner z := hzc.symm
      _ = parafermionicCoverRefinedCoarseOwner
          (parafermionicCoverRefinedPortEmbedding (d, layer)) := congrArg _ h
      _ = parafermionicCoverPortVertex d := hdc
  have hcenter := congrArg
    (fun v : ParafermionicCoverVertex => (9 * v.1.1 - 4, 9 * v.1.2 + 4)) howner
  have hsmall := parafermionicCoverRefinedCornerInterior_offset_small c hz
  have hlarge := parafermionicCoverRefinedPortEmbedding_offset_large d layer
  have hx := congrArg (fun v : ParafermionicCoverVertex => v.1.1) h
  have hy := congrArg (fun v : ParafermionicCoverVertex => v.1.2) h
  rcases hlarge with hneg | hpos | hneg | hpos <;>
    rcases hsmall with ⟨hsmallx₁, hsmallx₂, hsmally₁, hsmally₂⟩ <;>
    simp only [Prod.mk.injEq] at hcenter
  all_goals omega

theorem parafermionicCoverRefinedClosedCapMiddle_offset_large
    (d : ParafermionicCoverPort) :
    let z := parafermionicCoverRefinedClosedCapMiddle d
    let v := parafermionicCoverPortVertex d
    z.1.1 - (9 * v.1.1 - 4) ≤ -4 ∨ 4 ≤ z.1.1 - (9 * v.1.1 - 4) ∨
      z.1.2 - (9 * v.1.2 + 4) ≤ -4 ∨ 4 ≤ z.1.2 - (9 * v.1.2 + 4) := by
  rcases d with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverPortVertex,
      parafermionicCoverRefinedClosedCapMiddle_horizontal,
      parafermionicCoverRefinedClosedCapMiddle_vertical,
      LatticePort.primalVertex, LatticeBond.endpoint,
      LatticeBond.source, LatticeBond.target] <;> omega

theorem parafermionicCoverRefinedCornerInterior_ne_closedCapMiddle
    (c d : ParafermionicCoverPort) {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedCornerWalkInterior c) :
    z ≠ parafermionicCoverRefinedClosedCapMiddle d := by
  intro h
  have hzc := parafermionicCoverRefinedCornerInterior_owner c hz
  have hdc := parafermionicCoverRefinedCoarseOwner_closedCapMiddle d
  have howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d := by
    calc
      parafermionicCoverPortVertex c = parafermionicCoverRefinedCoarseOwner z := hzc.symm
      _ = parafermionicCoverRefinedCoarseOwner
          (parafermionicCoverRefinedClosedCapMiddle d) := congrArg _ h
      _ = parafermionicCoverPortVertex d := hdc
  have hcenter := congrArg
    (fun v : ParafermionicCoverVertex => (9 * v.1.1 - 4, 9 * v.1.2 + 4)) howner
  have hsmall := parafermionicCoverRefinedCornerInterior_offset_small c hz
  have hlarge := parafermionicCoverRefinedClosedCapMiddle_offset_large d
  have hx := congrArg (fun v : ParafermionicCoverVertex => v.1.1) h
  have hy := congrArg (fun v : ParafermionicCoverVertex => v.1.2) h
  rcases hlarge with hneg | hpos | hneg | hpos <;>
    rcases hsmall with ⟨hsmallx₁, hsmallx₂, hsmally₁, hsmally₂⟩ <;>
    simp only [Prod.mk.injEq] at hcenter
  all_goals omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Mid₁_Mid₁
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerMid₁ c = parafermionicCoverRefinedCornerMid₁ d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Mid₁_Elbow
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerMid₁ c = parafermionicCoverRefinedCornerElbow d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Mid₁_Mid₂
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerMid₁ c = parafermionicCoverRefinedCornerMid₂ d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Elbow_Mid₁
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerElbow c = parafermionicCoverRefinedCornerMid₁ d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Elbow_Elbow
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerElbow c = parafermionicCoverRefinedCornerElbow d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, OfNat.ofNat_ne_zero, add_left_inj, sub_left_inj,
      mul_eq_mul_left_iff, and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Elbow_Mid₂
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerElbow c = parafermionicCoverRefinedCornerMid₂ d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Mid₂_Mid₁
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerMid₂ c = parafermionicCoverRefinedCornerMid₁ d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Mid₂_Elbow
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerMid₂ c = parafermionicCoverRefinedCornerElbow d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

private theorem parafermionicCoverRefinedCornerInterior_eq_classification_Mid₂_Mid₂
    (c d : ParafermionicCoverPort)
    (howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d)
    (hpoint : parafermionicCoverRefinedCornerMid₂ c = parafermionicCoverRefinedCornerMid₂ d) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  rcases d with ⟨⟨⟨⟨xp, yp⟩, axp⟩, tipp, sidep⟩, kp⟩
  simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
    LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Prod.mk.injEq] at howner
  cases ax <;> cases tip <;> cases side <;>
    cases axp <;> cases tipp <;> cases sidep <;>
    simp only [parafermionicCoverCornerPair, LatticePort.cornerPair,
      parafermionicCoverRefinedCornerMid₂,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      LatticePort.mk.injEq, LatticeBond.mk.injEq, Prod.mk.injEq,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, reduceCtorEq,
      Int.reduceNeg, Int.reduceSub, add_left_inj,
      and_false, and_self, and_true, false_and, false_or,
      or_false, or_self] at howner hpoint ⊢ <;> omega

theorem parafermionicCoverRefinedCornerInterior_eq_classification
    (c d : ParafermionicCoverPort) {z w : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedCornerWalkInterior c)
    (hw : w ∈ parafermionicCoverRefinedCornerWalkInterior d)
    (hzw : z = w) :
    d = c ∨ d = parafermionicCoverCornerPair c := by
  have howner : parafermionicCoverPortVertex c = parafermionicCoverPortVertex d := by
    calc
      parafermionicCoverPortVertex c = parafermionicCoverRefinedCoarseOwner z :=
        (parafermionicCoverRefinedCornerInterior_owner c hz).symm
      _ = parafermionicCoverRefinedCoarseOwner w := congrArg _ hzw
      _ = parafermionicCoverPortVertex d :=
        parafermionicCoverRefinedCornerInterior_owner d hw
  subst w
  rw [parafermionicCoverRefinedCornerWalkInterior_eq] at hz hw
  simp only [List.mem_cons, List.not_mem_nil] at hz hw
  rcases hz with rfl | rfl | rfl | hfalse
  all_goals try contradiction
  all_goals
    rcases hw with hpoint | hpoint | hpoint | hfalse
    all_goals try contradiction
    all_goals
      first
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Mid₁_Mid₁ _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Mid₁_Elbow _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Mid₁_Mid₂ _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Elbow_Mid₁ _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Elbow_Elbow _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Elbow_Mid₂ _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Mid₂_Mid₁ _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Mid₂_Elbow _ _ howner hpoint
      | exact parafermionicCoverRefinedCornerInterior_eq_classification_Mid₂_Mid₂ _ _ howner hpoint

end PottsContinuity.FKC.Medial
