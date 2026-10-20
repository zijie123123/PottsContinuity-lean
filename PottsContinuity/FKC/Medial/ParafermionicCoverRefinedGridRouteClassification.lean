-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedGridRouteClassification.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedGridAvoidance
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingSimplicity
public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitution
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph
open PottsContinuity.FKC.FiniteFK

/-- A grid-line vertex in an actual edge route can only be the middle of the
closed false-layer cap for that edge. -/
theorem parafermionicCoverRefinedPairingRoute_grid_support_classification
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hgrid : z.1.1 % 9 = 5 ∨ z.1.2 % 9 = 4)
    (hz : z ∈ (parafermionicCoverRefinedPairingRoute n hn A h).support) :
    u.2 = false ∧ v.2 = false ∧
      parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) u.1.1 = false ∧
      z = parafermionicCoverRefinedClosedCapMiddle u.1.1 := by
  rcases u with ⟨c, bc⟩
  rcases v with ⟨d, bd⟩
  rw [parafermionicCoverRefinedPairingRoute_support] at hz
  have hstart :
      z ≠ parafermionicCoverRefinedPairingEmbedding (c, bc) := by
    simpa [parafermionicCoverRefinedPairingEmbedding] using
      parafermionicCoverRefinedGridPoint_ne_portEmbedding hgrid c.1 bc
  have hend :
      z ≠ parafermionicCoverRefinedPairingEmbedding (d, bd) := by
    simpa [parafermionicCoverRefinedPairingEmbedding] using
      parafermionicCoverRefinedGridPoint_ne_portEmbedding hgrid d.1 bd
  cases bc <;> cases bd
  · by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c.1
    · simp [parafermionicCoverRefinedPairingRouteSupport, hs] at hz
      rcases hz with hzu | hzv
      · exact (hstart hzu).elim
      · exact (hend hzv).elim
    · simp [parafermionicCoverRefinedPairingRouteSupport, hs] at hz
      rcases hz with hzu | hzmid | hzv
      · exact (hstart hzu).elim
      · exact ⟨rfl, rfl, by simpa using hs, hzmid⟩
      · exact (hend hzv).elim
  · simp [parafermionicCoverRefinedPairingRouteSupport] at hz
    rcases hz with hzu | hzv
    · exact (hstart hzu).elim
    · exact (hend hzv).elim
  · simp [parafermionicCoverRefinedPairingRouteSupport] at hz
    rcases hz with hzu | hzv
    · exact (hstart hzu).elim
    · exact (hend hzv).elim
  · simp [parafermionicCoverRefinedPairingRouteSupport] at hz
    rcases hz with hzu | hz₁ | hz₂ | hz₃ | hzv
    · exact (hstart hzu).elim
    · have hcorner :
          parafermionicCoverRefinedCornerMid₁ c.1 ∈
            parafermionicCoverRefinedCornerWalkInterior c.1 := by
        rw [parafermionicCoverRefinedCornerWalkInterior_eq]
        simp
      exact (parafermionicCoverRefinedGridPoint_not_mem_cornerWalkInterior
        hgrid c.1 (hz₁ ▸ hcorner)).elim
    · have hcorner :
          parafermionicCoverRefinedCornerElbow c.1 ∈
            parafermionicCoverRefinedCornerWalkInterior c.1 := by
        rw [parafermionicCoverRefinedCornerWalkInterior_eq]
        simp
      exact (parafermionicCoverRefinedGridPoint_not_mem_cornerWalkInterior
        hgrid c.1 (hz₂ ▸ hcorner)).elim
    · have hcorner :
          parafermionicCoverRefinedCornerMid₂ c.1 ∈
            parafermionicCoverRefinedCornerWalkInterior c.1 := by
        rw [parafermionicCoverRefinedCornerWalkInterior_eq]
        simp
      exact (parafermionicCoverRefinedGridPoint_not_mem_cornerWalkInterior
        hgrid c.1 (hz₃ ▸ hcorner)).elim
    · exact (hend hzv).elim

private theorem graphWalkSubstitute_support_tail_local {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    (graphWalkSubstitute G H f route p).support.tail =
      p.darts.flatMap fun d => (route d.adj).support.tail := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | cons h p ih =>
      rw [graphWalkSubstitute_cons, Walk.tail_support_append,
        Walk.darts_cons, List.flatMap_cons, ih]

/-- A grid-line vertex in an actual refined pairing walk belongs to the closed
cap of an actual false-layer dart whose queried extended bond is closed. -/
theorem parafermionicCoverRefinedPairingWalk_grid_support_classification
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    {z : ParafermionicCoverVertex}
    (hgrid : z.1.1 % 9 = 5 ∨ z.1.2 % 9 = 4)
    (hz : z ∈ (parafermionicCoverRefinedPairingWalk n hn A p).support) :
    ∃ d ∈ p.darts,
      d.fst.2 = false ∧ d.snd.2 = false ∧
      parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) d.fst.1.1 = false ∧
      z = parafermionicCoverRefinedClosedCapMiddle d.fst.1.1 := by
  let f : ParafermionicCoverFinitePort n × Bool → ParafermionicCoverVertex :=
    parafermionicCoverRefinedPairingEmbedding
  let route := fun {a b} (h :
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj a b) =>
    parafermionicCoverRefinedPairingRoute n hn A h
  let q := parafermionicCoverRefinedPairingWalk n hn A p
  have htail : q.support.tail =
      p.darts.flatMap fun d =>
        (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail := by
    simpa [q, parafermionicCoverRefinedPairingWalk, f, route] using
      graphWalkSubstitute_support_tail_local
        (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
        parafermionicCoverGraph f route p
  have hzsupport : z ∈ q.support := by simpa [q] using hz
  rw [← Walk.cons_tail_support q] at hzsupport
  rcases List.mem_cons.mp hzsupport with hstart | htailmem
  · have hnot : z ≠ parafermionicCoverRefinedPairingEmbedding u := by
      rcases u with ⟨c, b⟩
      simpa [parafermionicCoverRefinedPairingEmbedding] using
        parafermionicCoverRefinedGridPoint_ne_portEmbedding hgrid c.1 b
    exact False.elim (hnot hstart)
  · rw [htail] at htailmem
    rcases List.mem_flatMap.mp htailmem with ⟨d, hd, hroute⟩
    let r := parafermionicCoverRefinedPairingRoute n hn A d.adj
    have hrouteSupport : z ∈ r.support := by
      rw [← Walk.cons_tail_support r]
      exact List.mem_cons_of_mem _ hroute
    have hclass := parafermionicCoverRefinedPairingRoute_grid_support_classification
      n hn A d.adj hgrid hrouteSupport
    exact ⟨d, hd, hclass.1, hclass.2.1, hclass.2.2.1, hclass.2.2.2⟩

end PottsContinuity.FKC.Medial
