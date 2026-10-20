module

public import PottsContinuity.Thm4.LocalWinding
public import PottsContinuity.Thm4.EndpointDefect

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

local instance windingVisitPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

/-- Every occurrence of an actual finite edge has both endpoints in the retained box. -/
theorem windingEdgePorts_eq_queriedPorts (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    windingEdgePorts n e = parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
  classical
  ext c
  simp only [windingEdgePorts, parafermionicCoverFiniteEdgeCutQueriedPorts,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have hval : (parafermionicCoverFiniteEdgeEmbedding n e).val = Sym2.map Subtype.val e.val := rfl
  constructor
  · intro h
    exact Subtype.ext (h.2.trans hval.symm)
  · intro h
    refine ⟨?_, (congrArg Subtype.val h).trans hval⟩
    apply parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e
    rw [← h, parafermionicCoverPortEdge_eq_incident_pair]
    exact Sym2.mem_mk_right _ _

/-- The actual winding defect is the alternating four-port sum, with the unique
canonical incoming source-tip port fixing its sign. -/
theorem windingAtomicDefect_eq_four_ports (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
    let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
    windingAtomicDefect n hn e A =
      parafermionicCoverPathWindingAtom n hn A (seed, true) -
      parafermionicCoverPathWindingAtom n hn A (o.openPort, true) -
      parafermionicCoverPathWindingAtom n hn A (o.closedPort, true) +
      parafermionicCoverPathWindingAtom n hn A (o.openClosedPort, true) := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hflag := (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).2
  rw [windingAtomicDefect, windingEdgePorts_eq_queriedPorts,
    parafermionicCoverFiniteEdgeCutQueriedPorts_eq_seedOrbit n hn e]
  change (∑ c ∈ ({seed, o.openPort, o.closedPort, o.openClosedPort} : Finset _),
    (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℝ) else -1) *
      parafermionicCoverPathWindingAtom n hn A (c, true)) = _
  have h₀ : seed ∉ ({o.openPort, o.closedPort, o.openClosedPort} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨o.distinct_seed_open, o.distinct_seed_closed, o.distinct_seed_openClosed⟩
  have h₁ : o.openPort ∉ ({o.closedPort, o.openClosedPort} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨o.distinct_open_closed, o.distinct_open_openClosed⟩
  have h₂ : o.closedPort ∉ ({o.openClosedPort} : Finset _) := by
    exact fun h => o.distinct_closed_openClosed (Finset.mem_singleton.mp h)
  rw [Finset.sum_insert h₀, Finset.sum_insert h₁, Finset.sum_insert h₂,
    Finset.sum_singleton]
  simp only [show parafermionicCoverIncomingPrimalLeft seed.1 = true from hflag,
    o.open_incoming_false, o.closed_incoming_false, o.openClosed_incoming_true,
    Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  ring

/-- Number of the queried edge's two incoming local strands visited by the
actual exploration. Both possible strands are represented on the full carrier. -/
def windingIncomingVisitCount (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) : ℕ := by
  classical
  exact (if (parafermionicCoverFiniteEdgeCutSeedPort n hn e, false) ∈
      (parafermionicCoverFiniteOriginExplorationPath n hn A).support then 1 else 0) +
    (if ((parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openClosedPort, false) ∈
      (parafermionicCoverFiniteOriginExplorationPath n hn A).support then 1 else 0)

/-- The q=4 local winding defect counts actual visited strands, with a positive
quarter turn for a closed edge and a negative quarter turn for an open edge.
No fixed-loop or source total-turn normalization is needed for this identity. -/
theorem windingAtomicDefect_eq_signed_visit_count (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    windingAtomicDefect n hn e A =
      (Real.pi / 2) * (if e ∈ A then (-1 : ℝ) else 1) *
        (windingIncomingVisitCount n hn A e : ℝ) := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hs := pathWinding_queried_difference n hn A e seed
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).1
    (parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e).2
  have ho := pathWinding_queried_difference n hn A e o.openClosedPort
    o.openClosed_queried o.openClosed_incoming_true
  have hsum := windingAtomicDefect_eq_four_ports n hn A e
  have hseed := parafermionicCoverFiniteEdgeCutSeed_localPair_eq n hn A e
  have hoc := parafermionicCoverFiniteEdgeCutOpenClosed_localPair_eq n hn A e
  change parafermionicCoverFiniteLocalPairPerm n A seed = _ at hseed
  change parafermionicCoverFiniteLocalPairPerm n A o.openClosedPort = _ at hoc
  rw [hseed] at hs
  rw [hoc] at ho
  change windingAtomicDefect n hn e A =
    (Real.pi / 2) * (if e ∈ A then (-1 : ℝ) else 1) *
      (((if (seed, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
        then 1 else 0) +
       (if (o.openClosedPort, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
        then 1 else 0) : ℕ) : ℝ)
  by_cases he : e ∈ A <;>
    by_cases hv : (seed, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support <;>
    by_cases hw : (o.openClosedPort, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support
  all_goals simp only [he, hv, hw, ↓reduceIte, Nat.cast_add, Nat.cast_zero, Nat.cast_one] at hs ho ⊢
  all_goals dsimp only at hsum
  all_goals change windingAtomicDefect n hn e A =
    parafermionicCoverPathWindingAtom n hn A (seed, true) -
    parafermionicCoverPathWindingAtom n hn A (o.openPort, true) -
    parafermionicCoverPathWindingAtom n hn A (o.closedPort, true) +
    parafermionicCoverPathWindingAtom n hn A (o.openClosedPort, true) at hsum
  all_goals linarith

end
end PottsContinuity.Thm4
