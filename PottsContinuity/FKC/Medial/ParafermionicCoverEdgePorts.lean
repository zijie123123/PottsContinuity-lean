-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgePorts.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPorts
public import PottsContinuity.FKC.Medial.ParafermionicCoverFinitePorts
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverConfigurationExtension
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC PottsContinuity.FKC.FiniteFK LatticePort

theorem parafermionicCoverPortEdge_eq_iff_four (c d : ParafermionicCoverPort) :
    parafermionicCoverPortEdge d = parafermionicCoverPortEdge c ↔
      d = c ∨ d = parafermionicCoverOpenPair c ∨
        d = parafermionicCoverClosedPair c ∨
        d = parafermionicCoverOpenPair (parafermionicCoverClosedPair c) := by
  constructor
  · intro hEdge
    rcases c with ⟨⟨bc, tc, sc⟩, kc⟩
    rcases d with ⟨⟨bd, td, sd⟩, kd⟩
    have hval := congrArg Subtype.val hEdge
    have hproj := congrArg (Sym2.map Prod.fst) hval
    rw [parafermionicCoverPortEdge_projection,
      parafermionicCoverPortEdge_projection] at hproj
    have hb : bd = bc := LatticeBond.toSym2_injective hproj
    subst bd
    have hsource :
        parafermionicCoverPortSourceSheet ((⟨bc, td, sd⟩ : LatticePort), kd) =
          parafermionicCoverPortSourceSheet ((⟨bc, tc, sc⟩ : LatticePort), kc) := by
      have hpair :
          s((bc.source, parafermionicCoverPortSourceSheet ((⟨bc, td, sd⟩ : LatticePort), kd)),
            (bc.target, parafermionicCoverPortSourceSheet ((⟨bc, td, sd⟩ : LatticePort), kd) +
              parafermionicCoverSheetShift bc.source bc.target)) =
          s((bc.source, parafermionicCoverPortSourceSheet ((⟨bc, tc, sc⟩ : LatticePort), kc)),
            (bc.target, parafermionicCoverPortSourceSheet ((⟨bc, tc, sc⟩ : LatticePort), kc) +
              parafermionicCoverSheetShift bc.source bc.target)) := by
        simpa only [parafermionicCoverPortEdge_val] using hval
      rcases (Sym2.eq_iff.mp hpair) with hpair | hpair
      · exact congrArg Prod.snd hpair.1
      · have hbad : bc.source = bc.target := congrArg Prod.fst hpair.1
        exact False.elim (bc.source_ne_target hbad)
    cases tc <;> cases sc <;> cases td <;> cases sd <;>
      simp [parafermionicCoverOpenPair, parafermionicCoverClosedPair,
        parafermionicCoverPortSourceSheet, parafermionicCoverPortOtherVertex,
        LatticePort.openPair, LatticePort.closedPair, LatticeBond.source,
        LatticeBond.target] at * <;> aesop
  · rintro (rfl | rfl | rfl | rfl)
    · rfl
    · apply Subtype.ext
      exact parafermionicCoverOpenPair_edge_val_eq c
    · apply Subtype.ext
      exact parafermionicCoverClosedPair_edge_val_eq c
    · apply Subtype.ext
      rw [parafermionicCoverOpenPair_edge_val_eq,
        parafermionicCoverClosedPair_edge_val_eq]

theorem parafermionicCoverPort_four_pairwise_ne (c : ParafermionicCoverPort) :
    (parafermionicCoverOpenPair c ≠ c) ∧
      (parafermionicCoverClosedPair c ≠ c) ∧
      (parafermionicCoverOpenPair (parafermionicCoverClosedPair c) ≠ c) ∧
      (parafermionicCoverOpenPair c ≠ parafermionicCoverClosedPair c) ∧
      (parafermionicCoverOpenPair (parafermionicCoverClosedPair c) ≠
        parafermionicCoverOpenPair c) ∧
      (parafermionicCoverOpenPair (parafermionicCoverClosedPair c) ≠
        parafermionicCoverClosedPair c) := by
  refine ⟨parafermionicCoverOpenPair_ne c, parafermionicCoverClosedPair_ne c, ?_, ?_, ?_, ?_⟩
  · intro h
    have hp := congrArg Prod.fst h
    rcases c with ⟨⟨b, t, s⟩, k⟩
    cases t <;> cases s <;> simp [parafermionicCoverOpenPair,
      parafermionicCoverClosedPair, LatticePort.openPair, LatticePort.closedPair] at hp
  · intro h
    have hp := congrArg Prod.fst h
    rcases c with ⟨⟨b, t, s⟩, k⟩
    cases t <;> cases s <;> simp [parafermionicCoverOpenPair,
      parafermionicCoverClosedPair, LatticePort.openPair, LatticePort.closedPair] at hp
  · intro h
    have hp := congrArg Prod.fst h
    rcases c with ⟨⟨b, t, s⟩, k⟩
    cases t <;> cases s <;> simp [parafermionicCoverOpenPair,
      parafermionicCoverClosedPair, LatticePort.openPair, LatticePort.closedPair] at hp
  · intro h
    have hp := congrArg Prod.fst h
    rcases c with ⟨⟨b, t, s⟩, k⟩
    cases t <;> cases s <;> simp [parafermionicCoverOpenPair,
      parafermionicCoverClosedPair, LatticePort.openPair, LatticePort.closedPair] at hp

theorem parafermionicCoverPort_four_mem_finite (n : ℕ) (c : ParafermionicCoverPort)
    (hbox : ∀ v ∈ (parafermionicCoverPortEdge c).1,
      v ∈ parafermionicCoverBoxVertices n) :
    ∃ c₀ c₁ c₂ c₃ : ParafermionicCoverFinitePort n,
      c₀.1 = c ∧
      c₁.1 = parafermionicCoverOpenPair c ∧
      c₂.1 = parafermionicCoverClosedPair c ∧
      c₃.1 = parafermionicCoverOpenPair (parafermionicCoverClosedPair c) := by
  have hleft : parafermionicCoverPortVertex c ∈ parafermionicCoverBoxVertices n := by
    apply hbox
    rw [parafermionicCoverPortEdge_eq_incident_pair]
    exact Sym2.mem_mk_left _ _
  have hright : parafermionicCoverPortOtherVertex c ∈ parafermionicCoverBoxVertices n := by
    apply hbox
    rw [parafermionicCoverPortEdge_eq_incident_pair]
    exact Sym2.mem_mk_right _ _
  have hvertex (d : ParafermionicCoverPort) (hd :
      parafermionicCoverPortVertex d = parafermionicCoverPortVertex c ∨
      parafermionicCoverPortVertex d = parafermionicCoverPortOtherVertex c) :
      parafermionicCoverPortVertex d ∈ parafermionicCoverBoxVertices n := by
    rcases hd with hd | hd
    · rw [hd]
      exact hleft
    · rw [hd]
      exact hright
  refine ⟨⟨c, hvertex c (Or.inl rfl)⟩,
    ⟨parafermionicCoverOpenPair c, ?_⟩,
    ⟨parafermionicCoverClosedPair c, ?_⟩,
    ⟨parafermionicCoverOpenPair (parafermionicCoverClosedPair c), ?_⟩,
    rfl, rfl, rfl, rfl⟩
  · rw [parafermionicCoverOpenPair_vertex]
    exact hright
  · rw [parafermionicCoverClosedPair_vertex]
    exact hleft
  · rw [parafermionicCoverOpenPair_vertex]
    have hout : parafermionicCoverPortOtherVertex (parafermionicCoverClosedPair c) =
        parafermionicCoverPortOtherVertex c := by
      rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, t, s⟩, k⟩
      cases ax <;> cases t <;> simp [parafermionicCoverClosedPair,
        parafermionicCoverPortOtherVertex, LatticePort.closedPair,
        LatticeBond.source, LatticeBond.target]
    rw [hout]
    exact hright

end PottsContinuity.FKC.Medial
