-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedSourceGeometry.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedSourceCycle
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCorridorAvoidance
public import PottsContinuity.FKC.Medial.ParafermionicCoverWalkFiniteBox
public import PottsContinuity.FKC.FiniteFK.Graph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph
open PottsContinuity.FKC.FiniteFK
open Classical

private theorem graphWalkSubstitute_support_tail
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (route : ∀ {u v : V}, G.Adj u v → H.Walk (f u) (f v))
    {u v : V} (p : G.Walk u v) :
    (graphWalkSubstitute G H f route p).support.tail =
      p.darts.flatMap fun d => (route d.adj).support.tail := by
  induction p with
  | nil => simp [graphWalkSubstitute]
  | cons h p ih =>
      rw [graphWalkSubstitute_cons, Walk.tail_support_append, Walk.darts_cons,
        List.flatMap_cons, ih]

theorem parafermionicCoverRefinedSourceCycle_support_avoidsCentralRectangle
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (parafermionicCoverRefinedSourceCycle n hn A).support) :
    ¬ parafermionicCoverRefinedCentralRectangle z := by
  let P := parafermionicCoverFiniteOriginExplorationPath n hn A
  let q := parafermionicCoverRefinedPairingWalk n hn A P
  let c := parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther
  have hflat : q.support.tail = P.darts.flatMap fun d =>
      (parafermionicCoverRefinedPairingRoute n hn A d.adj).support.tail := by
    simpa [q, P, parafermionicCoverRefinedPairingWalk] using
      (graphWalkSubstitute_support_tail
        (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
        parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
        (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h) P)
  have hstart : ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedPairingEmbedding
        (parafermionicCoverFiniteOriginCornerPort n hn, true)) := by
    simpa [q, P, parafermionicCoverRefinedPairingWalk,
      parafermionicCoverRefinedPairingEmbedding] using
      (parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (parafermionicCoverFiniteOriginCornerPort n hn, true))
  have hqAvoid : ∀ z ∈ q.support, ¬ parafermionicCoverRefinedCentralRectangle z := by
    intro z hzq
    rw [← Walk.cons_tail_support q] at hzq
    simp only [List.mem_cons] at hzq
    rcases hzq with rfl | hztail
    · exact hstart
    · rw [hflat] at hztail
      rcases List.mem_flatMap.mp hztail with ⟨d, hd, hroute⟩
      exact parafermionicCoverRefinedPairingRoute_support_avoidsCentralRectangle
        n hn A d.adj (List.mem_of_mem_tail hroute)
  have hcAvoid : ∀ z ∈ c.support, ¬ parafermionicCoverRefinedCentralRectangle z := by
    intro z hzc
    exact parafermionicCoverRefinedCornerWalk_support_avoidsCentralRectangle
      parafermionicCoverOriginCornerPortOther hzc
  have hcycleSupport :
      (parafermionicCoverRefinedSourceCycle n hn A).support =
        q.support ++ c.support.tail := by
    change (q.append (c.copy _ _)).support = q.support ++ c.support.tail
    rw [Walk.support_append, Walk.support_copy]
  rw [hcycleSupport] at hz
  rcases List.mem_append.mp hz with hzq | hzc
  · exact hqAvoid z hzq
  · exact hcAvoid z (List.mem_of_mem_tail hzc)

theorem parafermionicCoverRefinedSourceCycle_northClosingDart
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    ∃ d ∈ (parafermionicCoverRefinedSourceCycle n hn A).darts,
      d.toProd = (((( -3 : ℤ), (1 : ℤ)), (0 : ℤ)), (((-3 : ℤ), (2 : ℤ)), (0 : ℤ))) := by
  let c := parafermionicCoverRefinedCornerWalk parafermionicCoverOriginCornerPortOther
  have hcNil : ¬ c.Nil := by
    change ¬ (SimpleGraph.Walk.cons _ _).Nil
    exact SimpleGraph.Walk.not_nil_cons
  let d := c.firstDart hcNil
  have hfirst : d ∈ c.darts := c.firstDart_mem_darts hcNil
  have hstart : parafermionicCoverRefinedPortEmbedding
      (parafermionicCoverOriginCornerPortOther, true) =
      (((-3 : ℤ), (1 : ℤ)), (0 : ℤ)) := by
    simp [parafermionicCoverOriginCornerPortOther, parafermionicCoverOriginCornerPort,
      parafermionicCoverOriginCornerPortOther, parafermionicCoverOriginCornerPort,

      parafermionicCoverRefinedPortEmbedding_vertical,
      parafermionicCoverCornerPair, LatticePort.cornerPair,

      ]
  have hsnd : c.snd = (((-3 : ℤ), (2 : ℤ)), (0 : ℤ)) := by
    change (parafermionicCoverRefinedCornerWalk
      parafermionicCoverOriginCornerPortOther).getVert 1 = _
    simp [SimpleGraph.Walk.getVert, parafermionicCoverRefinedCornerWalk,
      parafermionicCoverRefinedCornerMid₁,
      parafermionicCoverRefinedCornerElbow,
      parafermionicCoverOriginCornerPortOther, parafermionicCoverOriginCornerPort,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical,
      parafermionicCoverCornerPair, LatticePort.cornerPair,

      ]
  refine ⟨d, ?_, ?_⟩
  · rw [parafermionicCoverRefinedSourceCycle, Walk.darts_append]
    apply List.mem_append_right
    simp [d, c, Walk.darts_copy]
  · change (parafermionicCoverRefinedPortEmbedding
      (parafermionicCoverOriginCornerPortOther, true), c.snd) = _
    exact Prod.ext hstart hsnd

private theorem parafermionicCoverBoxVertices_mono {n m : ℕ} (hnm : n ≤ m)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverBoxVertices n) :
    z ∈ parafermionicCoverBoxVertices m := by
  rw [parafermionicCoverBoxVertices_mem] at hz ⊢
  rcases hz with ⟨hx₁, hx₂, hy₁, hy₂, hk₁, hk₂⟩
  have hnmZ : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast hnm
  have hpow : n ^ 5 ≤ m ^ 5 := by gcongr
  have hpowZ : ((n ^ 5 : ℕ) : ℤ) ≤ ((m ^ 5 : ℕ) : ℤ) := by exact_mod_cast hpow
  constructor <;> omega

theorem parafermionicCoverRefinedSourceCycle_exists_box_restriction
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    ∃ N : ℕ, 4 ≤ N ∧
      ∃ hbox : ∀ z ∈ (parafermionicCoverRefinedSourceCycle n hn A).support,
        z ∈ parafermionicCoverBoxVertices N,
        ((parafermionicCoverRefinedSourceCycle n hn A).induce
          (parafermionicCoverBoxVertices N) hbox).IsCycle ∧
        ((parafermionicCoverRefinedSourceCycle n hn A).induce
          (parafermionicCoverBoxVertices N) hbox).map
            (SimpleGraph.Embedding.induce
              (parafermionicCoverBoxVertices N)).toHom =
          parafermionicCoverRefinedSourceCycle n hn A := by
  let p := parafermionicCoverRefinedSourceCycle n hn A
  obtain ⟨N₀, hN₀, hbox₀, hcycle₀, hmap₀⟩ :=
    parafermionicCoverCycle_exists_box_restriction p
      (parafermionicCoverRefinedSourceCycle_isCycle n hn A)
  let N := max N₀ 4
  have hN : 4 ≤ N := le_trans (by decide : 4 ≤ 4) (Nat.le_max_right _ _)
  have hbox : ∀ z ∈ p.support, z ∈ parafermionicCoverBoxVertices N := by
    intro z hz
    exact parafermionicCoverBoxVertices_mono (Nat.le_max_left _ _) (hbox₀ z hz)
  have hmap : (p.induce (parafermionicCoverBoxVertices N) hbox).map
      (SimpleGraph.Embedding.induce (parafermionicCoverBoxVertices N)).toHom = p := by
    simpa [parafermionicCoverBoxGraph] using (SimpleGraph.Walk.map_induce p hbox)
  have hcycle : (p.induce (parafermionicCoverBoxVertices N) hbox).IsCycle := by
    have hmapped : ((p.induce (parafermionicCoverBoxVertices N) hbox).map
        (SimpleGraph.Embedding.induce (parafermionicCoverBoxVertices N)).toHom).IsCycle := by
      simpa [hmap] using parafermionicCoverRefinedSourceCycle_isCycle n hn A
    exact (SimpleGraph.Walk.isCycle_map_iff_of_injective
      (SimpleGraph.Embedding.induce
        (G := parafermionicCoverGraph)
        (parafermionicCoverBoxVertices N)).injective).mp hmapped
  exact ⟨N, hN, hbox, hcycle, hmap⟩

end PottsContinuity.FKC.Medial
