-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverSimpleCycleSignedTurning.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverSimpleCycleSectorProfile
public import PottsContinuity.FKC.Medial.ParafermionicCoverSimpleCycleBoundaryDefect
public import PottsContinuity.FKC.Medial.ParafermionicCoverPrimalCycleTurnSum
public import PottsContinuity.FKC.Medial.ParafermionicCoverSelectedCornerCoefficient
public import PottsContinuity.FKC.Medial.ParafermionicCoverPrimalCycleDirections
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkCompass
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC
open SimpleGraph

private theorem signedTurn_dart_fst_injective {n : ℕ}
    {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    {d e : (parafermionicCoverBoxGraph n).Dart}
    (hd : d ∈ p.darts) (he : e ∈ p.darts) (h : d.fst = e.fst) : d = e := by
  have hmap : (p.reverse.darts.map fun x => x.snd).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.reverse.support_nodup
  have hnodup : p.reverse.darts.Nodup := List.Nodup.of_map (fun x => x.snd) hmap
  have hinj := (List.nodup_map_iff_inj_on hnodup).mp hmap
  have hd' : d.symm ∈ p.reverse.darts := by simpa using hd
  have he' : e.symm ∈ p.reverse.darts := by simpa using he
  have h' : d.symm.snd = e.symm.snd := h
  simpa using congrArg Dart.symm (hinj d.symm hd' e.symm he' h')

/-- The signed turning total equals four times the selected filling coefficient
on any actual dart of the same finite-box simple cycle. -/
theorem parafermionicCoverSimpleCycle_signedTurning_eq_four_mul_coefficient
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (d : (parafermionicCoverBoxGraph n).Dart) (hd : d ∈ p.darts) :
    parafermionicCoverPrimalCycleTurnSum p hp = 4 *
      parafermionicCoverFaceBoundaryCoefficient
        (parafermionicCoverSimpleCycleFillingSet hn p hp) d.fst d.snd := by
  obtain ⟨k, hk, hprofile⟩ := parafermionicCoverSimpleCycleSectorProfile hn p hp
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  have hlocal (v : ParafermionicCoverBoxVertex n) (hv : v ∈ p.support) :
      parafermionicCoverPrimalCycleQuarterTurn p hp v hv =
        k * (2 -
          ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) := by
    let din := parafermionicCoverPrimalCycleIncomingDirection p hp v hv
    let dout := parafermionicCoverPrimalCycleOutgoingDirection p hp v hv
    let Q := parafermionicCoverFiniteFaceSelectedCorners S v
    have hnonback : din ≠ dout + 2 := by
      simpa [din, dout] using
        parafermionicCoverPrimalCycleIncomingDirection_ne_outgoing_opposite p hp v hv
    have hdouble (a : Fin 4) : a + 2 + 2 = a := by fin_cases a <;> decide
    have hab : din + 2 ≠ dout := by
      intro h
      apply hnonback
      calc
        din = din + 2 + 2 := (hdouble din).symm
        _ = dout + 2 := by rw [h]
    have hturn := primalCompassQuarterTurn_eq_sector_boundary_formula
      Q (din + 2) dout k hab hk (by
        intro a
        simpa [Q, S, din, dout] using hprofile v hv a)
    calc
      parafermionicCoverPrimalCycleQuarterTurn p hp v hv =
          primalCompassQuarterTurn din dout := rfl
      _ = primalCompassQuarterTurn (din + 2 + 2) dout := by rw [hdouble]
      _ = k * (2 - (Q.card : ℤ)) := hturn
      _ = k * (2 -
          ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) := by
        rw [parafermionicCoverFiniteFaceSelectedCorners_card]

  have hturnsum : parafermionicCoverPrimalCycleTurnSum p hp = k * 4 := by
    have hturn := parafermionicCoverPrimalCycleTurnSum_eq_support_sum_of_local_eq
      p hp (fun v => k * (2 -
        ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ))) hlocal
    have hboundary := parafermionicCoverSimpleCycleFilling_boundary_defect hn p hp
    have hboundarySupport :
        Finset.sum p.support.toFinset (fun v => (2 : ℤ) -
          ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) = 4 := by
      rw [← parafermionicCoverSimpleCycleFillingSet_boundarySupport_toFinset hn p hp]
      exact hboundary
    calc
      parafermionicCoverPrimalCycleTurnSum p hp =
          Finset.sum p.support.toFinset (fun v => k * (2 -
            ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ))) := hturn
      _ = k * Finset.sum p.support.toFinset (fun v => (2 : ℤ) -
            ((parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card : ℤ)) := by
              rw [← Finset.mul_sum]
      _ = k * 4 := by rw [hboundarySupport]

  have hv : d.fst ∈ p.support := Walk.dart_fst_mem_support_of_mem_darts p hd
  let v := d.fst
  let r := parafermionicCoverPrimalCycleRotate p v hv
  have hcycle : r.IsCycle := by
    simpa [r, parafermionicCoverPrimalCycleRotate] using hp.rotate hv
  have hnil : ¬ r.Nil := by
    have hlen := hcycle.three_le_length
    exact (Walk.not_nil_iff_lt_length).2 (by omega)
  have hfirstMem := r.firstDart_mem_darts hnil
  have hfirstP : r.firstDart hnil ∈ p.darts :=
    (p.rotate_darts v hv).mem_iff.mp hfirstMem
  have hfirst : r.firstDart hnil = d := by
    apply signedTurn_dart_fst_injective p hp hfirstP hd
    simp [r, parafermionicCoverPrimalCycleRotate, Walk.firstDart, v]
  have hdir : parafermionicCoverPrimalCycleOutgoingDirection p hp v hv =
      parafermionicCoverCompassDirection d.fst.1 d.snd.1 (by exact d.adj) := by
    apply (parafermionicCoverCompassNeighbor_injective d.fst.1)
    calc
      parafermionicCoverCompassNeighbor d.fst.1
          (parafermionicCoverPrimalCycleOutgoingDirection p hp v hv) = r.snd.1 := by
            simpa [r, v, parafermionicCoverPrimalCycleRotate] using
              parafermionicCoverPrimalCycleOutgoingDirection_neighbor p hp v hv
      _ = d.snd.1 := by
            have h := congrArg (fun z : (parafermionicCoverBoxGraph n).Dart => z.snd.1) hfirst
            simpa [Walk.firstDart, r, parafermionicCoverPrimalCycleRotate] using h
      _ = parafermionicCoverCompassNeighbor d.fst.1
          (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj) := by
            symm
            exact parafermionicCoverCompassDirection_neighbor d.fst.1 d.snd.1 d.adj
  have hcoef : parafermionicCoverFaceBoundaryCoefficient S d.fst d.snd = k := by
    have hsector := hprofile v hv
      (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj)
    have hdout : parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj =
        parafermionicCoverPrimalCycleOutgoingDirection p hp v hv := by
      exact hdir.symm
    have hdouble (a : Fin 4) : a + 2 + 2 = a := by fin_cases a <;> decide
    have hnonback : parafermionicCoverPrimalCycleIncomingDirection p hp v hv ≠
        parafermionicCoverPrimalCycleOutgoingDirection p hp v hv + 2 := by
      simpa using parafermionicCoverPrimalCycleIncomingDirection_ne_outgoing_opposite
        p hp v hv
    have hnot : parafermionicCoverPrimalCycleOutgoingDirection p hp v hv ≠
        parafermionicCoverPrimalCycleIncomingDirection p hp v hv + 2 := by
      intro heq
      apply hnonback
      calc
        parafermionicCoverPrimalCycleIncomingDirection p hp v hv =
            parafermionicCoverPrimalCycleIncomingDirection p hp v hv + 2 + 2 :=
              (hdouble _).symm
        _ = parafermionicCoverPrimalCycleOutgoingDirection p hp v hv + 2 := by rw [heq]
    have hsectoreq : compassSectorBoundary
        (parafermionicCoverFiniteFaceSelectedCorners S v)
        (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj) = k := by
      rw [hsector, ite_eq_left hdout]
    have hneighbor : d.snd.1 = parafermionicCoverCompassNeighbor d.fst.1
        (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj) := by
      symm
      exact parafermionicCoverCompassDirection_neighbor d.fst.1 d.snd.1 d.adj
    have hcoeff := parafermionicCoverFaceBoundaryCoefficient_eq_selectedCornerIndicators
      S d.fst d.snd (parafermionicCoverCompassDirection d.fst.1 d.snd.1 d.adj) hneighbor
    simpa [v, compassSectorBoundary] using hcoeff.trans hsectoreq
  rw [hturnsum, hcoef]
  ring

end PottsContinuity.FKC.Medial
