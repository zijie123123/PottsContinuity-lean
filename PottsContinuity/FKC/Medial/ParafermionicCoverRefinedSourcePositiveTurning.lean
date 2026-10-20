-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedSourcePositiveTurning.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourceGeometry
public import PottsContinuity.FKC.Medial.ParafermionicCoverBranchCorridorCoefficient
public import PottsContinuity.FKC.Medial.ParafermionicCoverSimpleCycleSignedTurning
public import PottsContinuity.FKC.Medial.ParafermionicCoverCycleCompassTurn
public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceSetBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open SimpleGraph

/-- The actual named refined source cycle has positive cyclic compass turn. Its
orientation is fixed by the explicit north closing dart and the corridor sign. -/
theorem parafermionicCoverRefinedSourceCycle_cyclicCompassTurn_eq_four
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverWalkCyclicCompassTurn
      (parafermionicCoverRefinedSourceCycle n hn A) = 4 := by
  obtain ⟨N, hN, hbox, hp, hmap⟩ :=
    parafermionicCoverRefinedSourceCycle_exists_box_restriction n hn A
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  let p : (parafermionicCoverBoxGraph N).Walk _ _ :=
    (parafermionicCoverRefinedSourceCycle n hn A).induce
      (parafermionicCoverBoxVertices N) hbox
  have hpCycle : p.IsCycle := by simpa [p, parafermionicCoverBoxGraph] using hp
  let S := parafermionicCoverSimpleCycleFillingSet hN1 p hpCycle
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hN1 p hpCycle
  have hzero : ∀ u v : ParafermionicCoverBoxVertex N,
      parafermionicCoverRefinedCentralRectangle u.1 →
      parafermionicCoverRefinedCentralRectangle v.1 →
      parafermionicCoverFaceBoundaryCoefficient S u v = 0 := by
    intro u v hu hv
    by_contra hnot
    have hedge : s(u,v) ∈ p.edges := by
      exact (hspec.2.2 u v).mp hnot
    have huP : u ∈ p.support := p.fst_mem_support_of_mem_edges hedge
    have huMap : (u : ParafermionicCoverVertex) ∈ (p.map
        (SimpleGraph.Embedding.induce
          (parafermionicCoverBoxVertices N)).toHom).support := by
      rw [Walk.support_map]
      exact List.mem_map.mpr ⟨u, huP, rfl⟩
    have huFull : (u : ParafermionicCoverVertex) ∈
        (parafermionicCoverRefinedSourceCycle n hn A).support := by
      exact congrArg Walk.support hmap ▸ huMap
    exact (parafermionicCoverRefinedSourceCycle_support_avoidsCentralRectangle
      n hn A huFull) hu

  obtain ⟨d, hdSource, hdval⟩ :=
    parafermionicCoverRefinedSourceCycle_northClosingDart n hn A
  have hdMapped : d ∈ (p.map
      (SimpleGraph.Embedding.induce
        (parafermionicCoverBoxVertices N)).toHom).darts := by
    rw [hmap]
    exact hdSource
  rw [Walk.darts_map] at hdMapped
  obtain ⟨e, he, hde⟩ := List.mem_map.mp hdMapped
  have hdFst : d.fst = (((-3 : ℤ), (1 : ℤ)), (0 : ℤ)) := by
    have h := congrArg Prod.fst hdval
    simpa [Dart.toProd] using h
  have hdSnd : d.snd = (((-3 : ℤ), (2 : ℤ)), (0 : ℤ)) := by
    have h := congrArg Prod.snd hdval
    simpa [Dart.toProd] using h
  have heFst : (e.fst : ParafermionicCoverVertex) =
      (((-3 : ℤ), (1 : ℤ)), (0 : ℤ)) := by
    have h := congrArg (fun x => x.toProd.1) hde
    change (e.toProd.1 : ParafermionicCoverVertex) = d.toProd.1 at h
    exact h.trans hdFst
  have heSnd : (e.snd : ParafermionicCoverVertex) =
      (((-3 : ℤ), (2 : ℤ)), (0 : ℤ)) := by
    have h := congrArg (fun x => x.toProd.2) hde
    change (e.toProd.2 : ParafermionicCoverVertex) = d.toProd.2 at h
    exact h.trans hdSnd
  have hneZero : parafermionicCoverFaceBoundaryCoefficient S e.toProd.1 e.toProd.2 ≠ 0 := by
    apply (hspec.2.2 e.toProd.1 e.toProd.2).2
    have hedge : e.edge ∈ p.edges := by
      rw [Walk.edges]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    simpa [Dart.edge] using hedge
  have haBox : (((-3 : ℤ), (1 : ℤ)), (0 : ℤ)) ∈ parafermionicCoverBoxVertices N := by
    rw [parafermionicCoverBoxVertices_mem]
    change -(N : ℤ) ≤ -3 ∧ -3 ≤ (N : ℤ) ∧
      -(N : ℤ) ≤ 1 ∧ 1 ≤ (N : ℤ) ∧
      -((N ^ 5 : ℕ) : ℤ) ≤ 0 ∧ 0 ≤ ((N ^ 5 : ℕ) : ℤ)
    have hpow : 0 ≤ ((N ^ 5 : ℕ) : ℤ) := Int.natCast_nonneg _
    exact ⟨by omega, by omega, by omega, by omega, by omega, hpow⟩
  have hbBox : (((-3 : ℤ), (2 : ℤ)), (0 : ℤ)) ∈ parafermionicCoverBoxVertices N := by
    rw [parafermionicCoverBoxVertices_mem]
    change -(N : ℤ) ≤ -3 ∧ -3 ≤ (N : ℤ) ∧
      -(N : ℤ) ≤ 2 ∧ 2 ≤ (N : ℤ) ∧
      -((N ^ 5 : ℕ) : ℤ) ≤ 0 ∧ 0 ≤ ((N ^ 5 : ℕ) : ℤ)
    have hpow : 0 ≤ ((N ^ 5 : ℕ) : ℤ) := Int.natCast_nonneg _
    exact ⟨by omega, by omega, by omega, by omega, by omega, hpow⟩
  let a : ParafermionicCoverBoxVertex N := ⟨(((-3 : ℤ), (1 : ℤ)), (0 : ℤ)), haBox⟩
  let b : ParafermionicCoverBoxVertex N := ⟨(((-3 : ℤ), (2 : ℤ)), (0 : ℤ)), hbBox⟩
  have haEq : a = e.toProd.1 := Subtype.ext heFst.symm
  have hbEq : b = e.toProd.2 := Subtype.ext heSnd.symm
  have hanchorRaw : 0 ≤ parafermionicCoverFaceBoundaryCoefficient S a b := by
    have h := parafermionicCoverBranchCorridor_anchor_coefficient_nonneg N hN S hzero
    change 0 ≤ parafermionicCoverFaceBoundaryCoefficient S a b
    exact h
  have hanchor : 0 ≤ parafermionicCoverFaceBoundaryCoefficient S e.toProd.1 e.toProd.2 := by
    rw [← haEq, ← hbEq]
    exact hanchorRaw
  have hcoefRange := parafermionicCoverFaceBoundaryCoefficient_mem S e.toProd.1 e.toProd.2
  have hcoef : parafermionicCoverFaceBoundaryCoefficient S e.toProd.1 e.toProd.2 = 1 := by
    change _ = -1 ∨ _ = 0 ∨ _ = 1 at hcoefRange
    rcases hcoefRange with hneg | hzero | hone <;> omega
  have hturn := parafermionicCoverSimpleCycle_signedTurning_eq_four_mul_coefficient
    hN1 p hpCycle e he
  have hprimal : parafermionicCoverPrimalCycleTurnSum p hpCycle = 4 := by
    rw [hturn, hcoef]
    norm_num
  calc
      parafermionicCoverWalkCyclicCompassTurn
        (parafermionicCoverRefinedSourceCycle n hn A) =
      parafermionicCoverPrimalCycleTurnSum p hpCycle := by
        calc
          parafermionicCoverWalkCyclicCompassTurn
              (parafermionicCoverRefinedSourceCycle n hn A) =
            parafermionicCoverWalkCyclicCompassTurn
              (p.map (SimpleGraph.Embedding.induce
                (parafermionicCoverBoxVertices N)).toHom) :=
              congrArg parafermionicCoverWalkCyclicCompassTurn hmap.symm
          _ = parafermionicCoverPrimalCycleTurnSum p hpCycle :=
            parafermionicCoverWalkCyclicCompassTurn_map_boxCycle_eq_primalTurnSum p hpCycle
    _ = 4 := hprimal

end PottsContinuity.FKC.Medial
