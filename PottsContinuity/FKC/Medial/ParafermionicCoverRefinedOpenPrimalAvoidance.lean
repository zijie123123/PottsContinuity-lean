-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedOpenPrimalAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPrimalEdgeIntersections
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedGridRouteClassification
public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitution
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph
open PottsContinuity.FKC.FiniteFK

/-- An open actual coarse dart's nine-step primal refinement is disjoint from
any actual refined pairing walk. -/
theorem parafermionicCoverRefinedOpenPrimalEdgeWalk_avoidsPairingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (u : ParafermionicCoverVertex) (d : Fin 4)
    {a b : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a b)
    (hopen : parafermionicCoverConfigurationExtensionState n A
      (⟨s(u, parafermionicCoverCompassNeighbor u d), by
        apply parafermionicCoverGraph.mem_edgeSet.mpr
        exact ⟨(parafermionicCoverCompassNeighbor_adj u d).1, rfl⟩⟩ :
        parafermionicCoverGraph.edgeSet) = true) :
    ∀ z, z ∈ (parafermionicCoverRefinedPrimalEdgeWalk u d).support →
      z ∉ (parafermionicCoverRefinedPairingWalk n hn A p).support := by
  intro z hzprimal hzpair
  have hgrid := parafermionicCoverRefinedPrimalEdgeWalk_support_modulus u d z hzprimal
  obtain ⟨e, he, hfalse₁, hfalse₂, hclosed, hcap⟩ :=
    parafermionicCoverRefinedPairingWalk_grid_support_classification
      n hn A p hgrid hzpair
  have hcapMem : parafermionicCoverRefinedClosedCapMiddle e.fst.1.1 ∈
      (parafermionicCoverRefinedPrimalEdgeWalk u d).support := hcap ▸ hzprimal
  have hsame := parafermionicCoverRefinedClosedCapMiddle_walk_portEdge u d
    e.fst.1.1 hcapMem
  have hopenPort : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) e.fst.1.1 = true := by
    unfold parafermionicCoverPortBondState
    rw [hsame]
    exact hopen
  cases hclosed.symm.trans hopenPort

/-- Every actual coarse-cell center avoids every actual refined pairing walk. -/
theorem parafermionicCoverRefinedCoarseCenter_avoidsPairingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (u : ParafermionicCoverVertex)
    {a b : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a b) :
    parafermionicCoverRefinedCoarseCenter u ∉
      (parafermionicCoverRefinedPairingWalk n hn A p).support := by
  intro hz
  rcases u with ⟨⟨x,y⟩,k⟩
  have hgrid :
      (parafermionicCoverRefinedCoarseCenter ((x,y),k)).1.1 % 9 = 5 ∨
      (parafermionicCoverRefinedCoarseCenter ((x,y),k)).1.2 % 9 = 4 := by
    simp [parafermionicCoverRefinedCoarseCenter]
  obtain ⟨e, he, hfalse₁, hfalse₂, hclosed, hcap⟩ :=
    parafermionicCoverRefinedPairingWalk_grid_support_classification
      n hn A p hgrid hz
  let c : ParafermionicCoverPort := e.fst.1.1
  have hcap' : parafermionicCoverRefinedCoarseCenter ((x,y),k) =
      parafermionicCoverRefinedClosedCapMiddle c := by
    simpa [c] using hcap
  rcases c with ⟨⟨⟨⟨cx,cy⟩,axis⟩,tip,side⟩,sheet⟩
  cases axis
  · rw [parafermionicCoverRefinedClosedCapMiddle_horizontal] at hcap'
    simp only [parafermionicCoverRefinedCoarseCenter, Prod.mk.injEq] at hcap'
    omega
  · rw [parafermionicCoverRefinedClosedCapMiddle_vertical] at hcap'
    simp only [parafermionicCoverRefinedCoarseCenter, Prod.mk.injEq] at hcap'
    omega


/-- Replace each full-cover edge by its actual nine-step refined primal route. -/
noncomputable def parafermionicCoverRefinedPrimalRoute
    {u v : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedCoarseCenter u)
      (parafermionicCoverRefinedCoarseCenter v) := by
  let d := parafermionicCoverCompassDirection u v h
  have hn := parafermionicCoverCompassDirection_neighbor u v h
  exact (parafermionicCoverRefinedPrimalEdgeWalk u d).copy rfl (congrArg _ hn)

/-- Literal coarse-center substitution of every dart of a full-cover walk. -/
noncomputable def parafermionicCoverRefinedPrimalSubstitute
    {u v : ParafermionicCoverVertex}
    (p : parafermionicCoverGraph.Walk u v) :
    parafermionicCoverGraph.Walk
      (parafermionicCoverRefinedCoarseCenter u)
      (parafermionicCoverRefinedCoarseCenter v) :=
  graphWalkSubstitute parafermionicCoverGraph parafermionicCoverGraph
    parafermionicCoverRefinedCoarseCenter parafermionicCoverRefinedPrimalRoute p

@[simp] theorem parafermionicCoverRefinedPrimalSubstitute_nil (u : ParafermionicCoverVertex) :
    parafermionicCoverRefinedPrimalSubstitute
      (SimpleGraph.Walk.nil : parafermionicCoverGraph.Walk u u) = .nil := by
  rfl

@[simp] theorem parafermionicCoverRefinedPrimalSubstitute_cons
    {u v w : ParafermionicCoverVertex}
    (h : parafermionicCoverGraph.Adj u v)
    (p : parafermionicCoverGraph.Walk v w) :
    parafermionicCoverRefinedPrimalSubstitute (.cons h p) =
      (parafermionicCoverRefinedPrimalRoute h).append
        (parafermionicCoverRefinedPrimalSubstitute p) := by
  rfl

/-- Every actual route in the substituted walk lies on one of the two grid
families used to isolate closed-cap middles. -/
theorem parafermionicCoverRefinedPrimalSubstitute_support_modulus
    {u v : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (parafermionicCoverRefinedPrimalSubstitute p).support) :
    z.1.1 % 9 = 5 ∨ z.1.2 % 9 = 4 := by
  induction p with
  | nil =>
      simp only [parafermionicCoverRefinedPrimalSubstitute_nil,
        SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      rcases u with ⟨⟨x,y⟩,k⟩
      simp [parafermionicCoverRefinedCoarseCenter]
  | @cons a b c h p ih =>
      rw [parafermionicCoverRefinedPrimalSubstitute_cons] at hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hzroute | hztail
      · have hzedge : z ∈
            (parafermionicCoverRefinedPrimalEdgeWalk a
              (parafermionicCoverCompassDirection a b h)).support := by
          simpa [parafermionicCoverRefinedPrimalRoute] using hzroute
        exact parafermionicCoverRefinedPrimalEdgeWalk_support_modulus
          a (parafermionicCoverCompassDirection a b h) z hzedge
      · have hzfull : z ∈
            (parafermionicCoverRefinedPrimalSubstitute p).support := by
          rw [← SimpleGraph.Walk.cons_tail_support
            (parafermionicCoverRefinedPrimalSubstitute p)]
          exact List.mem_cons_of_mem _ hztail
        exact ih hzfull


private theorem parafermionicCoverRefinedPrimalSubstitute_support_tail
    {u v : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u v) :
    (parafermionicCoverRefinedPrimalSubstitute p).support.tail =
      p.darts.flatMap fun d =>
        (parafermionicCoverRefinedPrimalRoute d.adj).support.tail := by
  induction p with
  | nil => simp [parafermionicCoverRefinedPrimalSubstitute]
  | cons h p ih =>
      rw [parafermionicCoverRefinedPrimalSubstitute_cons,
        SimpleGraph.Walk.tail_support_append,
        SimpleGraph.Walk.darts_cons, List.flatMap_cons, ih]

private theorem parafermionicCoverRefinedPrimalRoute_avoidsPairingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (d : parafermionicCoverGraph.Dart)
    {a b : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a b)
    (hopen : parafermionicCoverConfigurationExtensionState n A
      ⟨d.edge, d.edge_mem⟩ = true) :
    ∀ z, z ∈ (parafermionicCoverRefinedPrimalRoute d.adj).support →
      z ∉ (parafermionicCoverRefinedPairingWalk n hn A p).support := by
  let dir := parafermionicCoverCompassDirection d.fst d.snd d.adj
  let e : parafermionicCoverGraph.edgeSet :=
    ⟨s(d.fst, parafermionicCoverCompassNeighbor d.fst dir),
      parafermionicCoverGraph.mem_edgeSet.mpr ⟨
        (parafermionicCoverCompassNeighbor_adj d.fst dir).1, rfl⟩⟩
  have hneighbor := parafermionicCoverCompassDirection_neighbor d.fst d.snd d.adj
  have he : e = ⟨d.edge, d.edge_mem⟩ := by
    apply Subtype.ext
    change s(d.fst, parafermionicCoverCompassNeighbor d.fst dir) = s(d.fst, d.snd)
    rw [hneighbor]
  have hopen' : parafermionicCoverConfigurationExtensionState n A e = true := by
    rw [he]
    exact hopen
  have havoid := parafermionicCoverRefinedOpenPrimalEdgeWalk_avoidsPairingWalk
    n hn A d.fst dir p hopen'
  intro z hz hzpair
  have hz' : z ∈
      (parafermionicCoverRefinedPrimalEdgeWalk d.fst dir).support := by
    simpa [parafermionicCoverRefinedPrimalRoute, dir] using hz
  exact havoid z hz' hzpair

/-- A coarse-center refinement of a full walk with every original edge open
avoids every actual refined pairing walk. -/
theorem parafermionicCoverRefinedPrimalSubstitute_avoidsPairingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverVertex} (p : parafermionicCoverGraph.Walk u v)
    {a b : ParafermionicCoverFinitePort n × Bool}
    (q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk a b)
    (hopen : ∀ d ∈ p.darts,
      parafermionicCoverConfigurationExtensionState n A ⟨d.edge, d.edge_mem⟩ = true) :
    ∀ z, z ∈ (parafermionicCoverRefinedPrimalSubstitute p).support →
      z ∉ (parafermionicCoverRefinedPairingWalk n hn A q).support := by
  intro z hz hzpair
  have htail : z ∈ (parafermionicCoverRefinedPrimalSubstitute p).support.tail := by
    rw [← SimpleGraph.Walk.cons_tail_support
      (parafermionicCoverRefinedPrimalSubstitute p)] at hz
    rcases List.mem_cons.mp hz with hstart | htail
    · have hcenterPair : parafermionicCoverRefinedCoarseCenter u ∈
          (parafermionicCoverRefinedPairingWalk n hn A q).support := by
        rw [← hstart]
        exact hzpair
      exact False.elim ((parafermionicCoverRefinedCoarseCenter_avoidsPairingWalk
        n hn A u q) hcenterPair)
    · exact htail
  rw [parafermionicCoverRefinedPrimalSubstitute_support_tail] at htail
  rcases List.mem_flatMap.mp htail with ⟨d, hd, hrouteTail⟩
  have hrouteMem : z ∈ (parafermionicCoverRefinedPrimalRoute d.adj).support := by
    rw [← SimpleGraph.Walk.cons_tail_support
      (parafermionicCoverRefinedPrimalRoute d.adj)]
    exact List.mem_cons_of_mem _ hrouteTail
  have havoid := parafermionicCoverRefinedPrimalRoute_avoidsPairingWalk
    n hn A d q (hopen d hd)
  exact havoid z hrouteMem hzpair

end PottsContinuity.FKC.Medial
