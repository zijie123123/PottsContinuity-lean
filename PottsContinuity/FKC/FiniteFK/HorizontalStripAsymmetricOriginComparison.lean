-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripAsymmetricOriginComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.EmbeddedMarginalLaw
public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCoreConnectivityLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripWindowTranslation
public import PottsContinuity.FKC.FiniteFK.Expectation
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverEq24RootCoreComparison
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory FiniteProbability
noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance originCmpAnyEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance originCmpAnyConfigurationFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype (Configuration G) := Fintype.ofFinite _

local instance originCmpOuterEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (-(n + 1 : ℤ), 0) (2 * (n + 1)) n).edgeSet := Fintype.ofFinite _
local instance originCmpInnerEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (-(n:ℤ)-1, 0) (2*n+1) n).edgeSet := Fintype.ofFinite _
local instance originCmpOuterConfigFintype (n : ℕ) :
    Fintype (Configuration (rectangleGraph (-(n + 1 : ℤ), 0) (2 * (n + 1)) n)) := Fintype.ofFinite _
local instance originCmpInnerConfigFintype (n : ℕ) :
    Fintype (Configuration (rectangleGraph (-(n:ℤ)-1, 0) (2*n+1) n)) := Fintype.ofFinite _
local instance originCmpOuterVertexDecidableEq (n : ℕ) :
    DecidableEq (RectangleVertex (-(n + 1 : ℤ), 0) (2 * (n + 1)) n) := Classical.decEq _
local instance originCmpInnerVertexDecidableEq (n : ℕ) :
    DecidableEq (RectangleVertex (-(n:ℤ)-1, 0) (2*n+1) n) := Classical.decEq _
 theorem originCmp_innerRect_subset (n : ℕ) :
    latticeRectangle (-(n:ℤ)-1, 0) (2*n+1) n ⊆
      latticeRectangle (-(n + 1 : ℤ), 0) (2*(n+1)) n := by
  intro z hz
  rw [mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hxl,hxu⟩,⟨hyl,hyu⟩⟩
  constructor
  · constructor <;> omega
  · exact ⟨hyl, hyu⟩

local instance originCmpOuterRemovedFintype (n : ℕ) :
    Fintype (RemovedConfiguration (rectangleGraph (-(n + 1 : ℤ), 0) (2 * (n + 1)) n)
      (subgraphRemovedEdges
        ((rectangleGraph (-(n:ℤ)-1, 0) (2*n+1) n).map
          (rectangleVertexEmbedding (originCmp_innerRect_subset n)))
        (rectangleGraph (-(n + 1 : ℤ), 0) (2 * (n + 1)) n))) := Fintype.ofFinite _

def originCmpOuterBoundary (n : ℕ) :
    Set (RectangleVertex (-(n + 1 : ℤ), 0) (2 * (n + 1)) n) :=
  {v | v.val.1 = -((n+1:ℕ):ℤ) ∨ v.val.1 = (n+1:ℤ) ∨ v.val.2 = (n:ℤ)}

def originCmpInnerBoundary (n : ℕ) :
    Set (RectangleVertex (-(n + 1 : ℤ), 0) (2*(n+1)) n) :=
  {v | v.val.1 ≤ (n:ℤ) ∧
    (v.val.1 = -((n+1:ℕ):ℤ) ∨ v.val.1 = (n:ℤ) ∨ v.val.2 = (n:ℤ))}


def originCmpVertexEmbedding (n : ℕ) :
    RectangleVertex (-(n:ℤ)-1, 0) (2*n+1) n ↪
      RectangleVertex (-(n + 1 : ℤ), 0) (2*(n+1)) n :=
  rectangleVertexEmbedding (by
    exact originCmp_innerRect_subset n)

@[simp] private theorem originCmpVertexEmbedding_val (n : ℕ)
    (v : RectangleVertex (-(n:ℤ)-1, 0) (2*n+1) n) :
    (originCmpVertexEmbedding n v).val = v.val := rfl

 theorem originCmpMapLe (n : ℕ) :
    (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).map (originCmpVertexEmbedding n) ≤
      rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n := by
  exact rectangleGraph_map_rectangleVertexEmbedding (originCmp_innerRect_subset n)

private theorem originCmp_walk_support_x_eq
    {V : Type*} {G : SimpleGraph V} {u v : V} (X : V → ℤ) (k : ℤ)
    (hstep : ∀ ⦃a b⦄, G.Adj a b → X b ≤ X a + 1)
    (p : G.Walk u v) (hu : X u ≤ k) (hv : k ≤ X v) :
    ∃ z ∈ p.support, X z = k := by
  induction p with
  | @nil a =>
      exact ⟨a, by simp, by omega⟩
  | @cons a b c hab tail ih =>
      by_cases hak : X a = k
      · exact ⟨a, by simp, hak⟩
      · have halt : X a < k := by omega
        have hba := hstep hab
        by_cases hbk : X b < k
        · obtain ⟨z, hz, hzk⟩ := ih (by omega) hv
          exact ⟨z, by simp [hz], hzk⟩
        · have hbeq : X b = k := by omega
          exact ⟨b, by simp [tail.start_mem_support], hbeq⟩

private theorem originCmp_firstBoundaryPrefix
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {B : Set V} {x y : V}
    (p : G.Walk x y) (hy : y ∈ B) (hp : p.IsPath) :
    ∃ z, z ∈ B ∧ ∃ q : G.Walk x z, q.IsPath ∧
      (∀ t ∈ q.support, t ∈ p.support) ∧
      (∀ t ∈ q.support, t ∈ B → t = z) := by
  induction p with
  | @nil a =>
      exact ⟨a, hy, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp, by simp⟩
  | @cons x y z hadj tail ih =>
      have hnodup := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      by_cases hx : x ∈ B
      · exact ⟨x, hx, .nil, .nil, by simp, by simp⟩
      · have htail : tail.IsPath := by simpa using hp.tail
        obtain ⟨t, ht, q, hq, hqSub, huniq⟩ := ih hy htail
        refine ⟨t, ht, SimpleGraph.Walk.cons hadj q, ?_, ?_, ?_⟩
        · apply SimpleGraph.Walk.IsPath.cons hq
          intro hxq
          exact hnodup.1 (hqSub x hxq)
        · intro s hs
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
          rcases hs with rfl | hs
          · simp
          · exact (by simp [hqSub s hs])
        · intro s hs hsB
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact (hx hsB).elim
          · exact huniq s hs hsB

def originCmpInnerVertices (n : ℕ) :
    Set (RectangleVertex (-(n+1:ℤ),0) (2*(n+1)) n) :=
  {v | v.val.1 ≤ (n:ℤ)}

def originCmpVertexEquiv (n : ℕ) :
    RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n ≃ originCmpInnerVertices n where
  toFun u := ⟨originCmpVertexEmbedding n u, by
    have hu := u.property
    rw [mem_latticeRectangle] at hu
    change u.val.1 ≤ (n:ℤ)
    calc
      u.val.1 ≤ (-(n:ℤ)-1) + ((2*n+1:ℕ):ℤ) := hu.1.2
      _ = (n:ℤ) := by push_cast; omega⟩
  invFun v := ⟨v.val.val, by
    have hv := v.val.property
    rw [mem_latticeRectangle] at hv
    have hvP : v.val.val.1 ≤ (n:ℤ) := v.property
    rw [mem_latticeRectangle]
    constructor
    · constructor <;> omega
    · exact hv.2⟩
  left_inv := by intro u; apply Subtype.ext; rfl
  right_inv := by intro v; apply Subtype.ext; rfl

@[simp] private theorem originCmpVertexEquiv_val (n : ℕ)
    (u : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n) :
    ((originCmpVertexEquiv n u).val).val = u.val := rfl

private theorem originCmp_inner_open_adj_of_outer
    (n : ℕ) (A : Configuration (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n))
    {u v : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n}
    (h : (openGraph (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n) A).Adj
      (originCmpVertexEmbedding n u) (originCmpVertexEmbedding n v)) :
    (openGraph (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n)
      (embeddedConfigurationRestriction _ _ (originCmpVertexEmbedding n) (originCmpMapLe n) A)).Adj u v := by
  rw [openGraph_adj] at h ⊢
  rcases h with ⟨e, heA, heval⟩
  have heA' : e ∈ A := by simpa [openEdges] using heA
  have hedj : (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n).Adj
      (originCmpVertexEmbedding n u) (originCmpVertexEmbedding n v) := by
    apply (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n).mem_edgeSet.mp
    rw [← heval]
    exact e.property
  have hcoords := (rectangleGraph_adj_iff _ _ _ _ _).mp hedj
  have hinnerAdj : (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).Adj u v := by
    apply (rectangleGraph_adj_iff _ _ _ _ _).2
    simpa [originCmpVertexEmbedding_val] using hcoords
  let ei : (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).edgeSet :=
    ⟨s(u,v), (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).mem_edgeSet.mpr hinnerAdj⟩
  have hmap : embeddedEdgeEmbedding _ _ (originCmpVertexEmbedding n)
      (originCmpMapLe n) ei = e := by
    apply Subtype.ext
    change s(originCmpVertexEmbedding n u, originCmpVertexEmbedding n v) = e.val
    rw [← heval]
  exact ⟨ei, (mem_embeddedConfigurationRestriction _ _ _ _ A ei).2 (by simpa [hmap] using heA'), by
    simp [ei]⟩

def originCmp_openGraphHom
    (n : ℕ) (A : Configuration (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n)) :
    (openGraph (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n) A).induce
      (originCmpInnerVertices n) →g
    openGraph (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n)
      (embeddedConfigurationRestriction _ _ (originCmpVertexEmbedding n) (originCmpMapLe n) A) where
  toFun v := (originCmpVertexEquiv n).symm v
  map_rel' := by
    intro u v huv
    let hu' : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n :=
      ⟨u.val.val, by
        have hout := u.val.property
        rw [mem_latticeRectangle] at hout
        have hx : u.val.val.1 ≤ (n:ℤ) := u.property
        rw [mem_latticeRectangle]
        constructor
        · constructor <;> omega
        · exact hout.2⟩
    let hv' : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n :=
      ⟨v.val.val, by
        have hout := v.val.property
        rw [mem_latticeRectangle] at hout
        have hx : v.val.val.1 ≤ (n:ℤ) := v.property
        rw [mem_latticeRectangle]
        constructor
        · constructor <;> omega
        · exact hout.2⟩
    have huval : originCmpVertexEmbedding n hu' = u.val := by
      apply Subtype.ext
      change hu'.val = u.val.val
      rfl
    have hvval : originCmpVertexEmbedding n hv' = v.val := by
      apply Subtype.ext
      change hv'.val = v.val.val
      rfl
    have hOuter : (openGraph (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n) A).Adj
        (originCmpVertexEmbedding n hu') (originCmpVertexEmbedding n hv') := by
      have huv' := (SimpleGraph.induce_adj.mp huv)
      change (openGraph (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n) A).Adj u.val v.val at huv'
      simpa only [huval, hvval] using huv'
    have hout := originCmp_inner_open_adj_of_outer n A hOuter
    change (openGraph (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n)
      (embeddedConfigurationRestriction _ _ (originCmpVertexEmbedding n) (originCmpMapLe n) A)).Adj
      ((originCmpVertexEquiv n).symm u) ((originCmpVertexEquiv n).symm v)
    simpa [originCmpVertexEquiv, hu', hv'] using hout


private theorem originCmp_outer_adj_x_step
    (n : ℕ) {u v : RectangleVertex (-(n+1:ℤ),0) (2*(n+1)) n}
    (h : (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n).Adj u v) :
    v.val.1 ≤ u.val.1 + 1 := by
  have hs := (rectangleGraph_adj_iff _ _ _ _ _).mp h
  rcases hs with hh | hv
  · rcases hh.1 with huv | hvu <;> omega
  · omega

private theorem originCmp_actual_event_subset (n : ℕ) (A : Configuration
    (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n))
    (hA : A ∈ horizontalStripOriginLocalConnectionEvent (n+1) n) :
    embeddedConfigurationRestriction _ _ (originCmpVertexEmbedding n) (originCmpMapLe n) A ∈
      parafermionicCoverEq24OrdinaryOriginEvent n := by
  rcases hA with ⟨z, hz, hconn⟩
  change (openGraph _ A).Reachable _ _ at hconn
  obtain ⟨p, hpath⟩ := hconn.exists_isPath
  have hzBoundary : z.val.1 = -((n+1:ℕ):ℤ) ∨ z.val.1 = (n+1:ℤ) ∨ z.val.2 = (n:ℤ) := by
    change z.val ∈ (rectangleLeftSide (-( (n+1:ℕ):ℤ),0) (2*(n+1)) n ∪
      rectangleRightSide (-( (n+1:ℕ):ℤ),0) (2*(n+1)) n) ∪
      rectangleTopSide (-( (n+1:ℕ):ℤ),0) (2*(n+1)) n at hz
    rcases Finset.mem_union.mp hz with hzLR | hzT
    · rcases Finset.mem_union.mp hzLR with hzL | hzR
      · simp only [rectangleLeftSide, Finset.mem_filter] at hzL
        exact Or.inl hzL.2
      · simp only [rectangleRightSide, Finset.mem_filter] at hzR
        exact Or.inr (Or.inl (by omega))
    · simp only [rectangleTopSide, Finset.mem_filter] at hzT
      exact Or.inr (Or.inr (by omega))
  have hstartle : (horizontalStripOriginLocalRoot (n+1) n).val.1 ≤ (n:ℤ) := by
    change (0:ℤ) ≤ (n:ℤ)
    exact_mod_cast Nat.zero_le n
  have hsupport_meet : ∃ t ∈ p.support, t.val.1 ≤ (n:ℤ) ∧
      (t.val.1 = -((n+1:ℕ):ℤ) ∨ t.val.1 = (n:ℤ) ∨ t.val.2 = (n:ℤ)) := by
    rcases hzBoundary with hleft | hright | htop
    · exact ⟨z, p.end_mem_support, by omega, Or.inl hleft⟩
    · obtain ⟨t, ht, htx⟩ := originCmp_walk_support_x_eq
        (fun v => v.val.1) (n:ℤ)
        (by intro a b hadj; exact originCmp_outer_adj_x_step n (openGraph_le _ A hadj))
        p hstartle (by omega)
      exact ⟨t, ht, le_of_eq htx, Or.inr (Or.inl htx)⟩
    · by_cases hzn : z.val.1 ≤ (n:ℤ)
      · exact ⟨z, p.end_mem_support, hzn, Or.inr (Or.inr htop)⟩
      · obtain ⟨t, ht, htx⟩ := originCmp_walk_support_x_eq
          (fun v => v.val.1) (n:ℤ)
          (by intro a b hadj; exact originCmp_outer_adj_x_step n (openGraph_le _ A hadj))
          p hstartle (by omega)
        exact ⟨t, ht, le_of_eq htx, Or.inr (Or.inl htx)⟩
  obtain ⟨t, ht, htX, htB0⟩ := hsupport_meet
  have htB : t ∈ originCmpInnerBoundary n := ⟨htX, htB0⟩
  let p' := p.takeUntil t ht
  have hp'path : p'.IsPath := hpath.takeUntil ht
  obtain ⟨b, hb, q, hqpath, hqsub', hfirst⟩ :=
    originCmp_firstBoundaryPrefix p' htB hp'path
  have hqsub : ∀ s ∈ q.support, s ∈ p.support := by
    intro s hs
    exact (p.support_takeUntil_subset_support ht) (hqsub' s hs)
  have hbnd : b.val.1 = -((n+1:ℕ):ℤ) ∨ b.val.1 = (n:ℤ) ∨ b.val.2 = (n:ℤ) := hb.2
  have hsupport_inner : ∀ v ∈ q.support, v.val.1 ≤ (n:ℤ) := by
    intro v hv
    have hvOuter := v.property
    rw [mem_latticeRectangle] at hvOuter
    by_contra hnot
    have hvRight : v.val.1 = (n+1:ℤ) := by omega
    obtain ⟨s, hs, hsx⟩ := originCmp_walk_support_x_eq
      (fun y => y.val.1) (n:ℤ)
      (by intro a b hadj; exact originCmp_outer_adj_x_step n (openGraph_le _ A hadj))
      (q.takeUntil v hv) hstartle (by omega)
    have hsQ : s ∈ q.support := q.support_takeUntil_subset_support hv hs
    have hsB : s ∈ originCmpInnerBoundary n :=
      ⟨le_of_eq hsx, Or.inr (Or.inl hsx)⟩
    have hsEq : s = b := hfirst s hsQ hsB
    have hne : b ≠ v := by
      intro hEq
      subst v
      have hbX : b.val.1 ≤ (n:ℤ) := hb.1
      omega
    have hnotEnd := SimpleGraph.Walk.endpoint_notMem_support_takeUntil hqpath hv hne
    exact hnotEnd (hsEq ▸ hs)
  have hqIn : ∀ v ∈ q.support, v ∈ originCmpInnerVertices n := by
    intro v hv
    change v.val.1 ≤ (n:ℤ)
    exact hsupport_inner v hv
  let qI := q.induce (originCmpInnerVertices n) hqIn
  let qInner := qI.map (originCmp_openGraphHom n A)
  let zInner := (originCmpVertexEquiv n).symm
    ⟨b, by
      change b.val.1 ≤ (n:ℤ)
      exact hb.1⟩
  have hboundary : zInner ∈
      generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n := by
    simp only [generalRectangleDualBottomCoreAmbientBoundary, Set.mem_ofPred_eq]
    have hv : zInner.val = b.val := by rfl
    rw [hv]
    rcases hbnd with hl | hr | ht' <;> omega
  refine ⟨zInner, hboundary, ?_⟩
  have hstartEq : (originCmpVertexEquiv n).symm
      ⟨horizontalStripOriginLocalRoot (n+1) n,
        by change (horizontalStripOriginLocalRoot (n+1) n).val.1 ≤ (n:ℤ); simp [horizontalStripOriginLocalRoot]⟩ =
      (parafermionicCoverEq24OrdinaryOriginVertex n) := by
    apply Subtype.ext
    rfl
  have hconnInner : ActualConnected
      (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n)
      (embeddedConfigurationRestriction _ _ (originCmpVertexEmbedding n) (originCmpMapLe n) A)
      (parafermionicCoverEq24OrdinaryOriginVertex n) zInner := by
    have hwalk := qInner
    change ActualConnected _ _ _ _
    rw [← hstartEq]
    exact hwalk.reachable
  exact hconnInner

private theorem originCmp_removedEdge_endpoints_zone (n : ℕ)
    (e : (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n).edgeSet)
    (he : e.val ∉ ((rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).map
      (originCmpVertexEmbedding n)).edgeSet) :
    ∀ ⦃u : RectangleVertex (-(n+1:ℤ),0) (2*(n+1)) n⦄,
      u ∈ e.val → u.val.1 = (n:ℤ) ∨ u.val.1 = (n+1:ℤ) := by
  classical
  let p := e.val.out
  have hrepr : s(p.1, p.2) = e.val := Quot.out_eq _
  have hadj : (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n).Adj p.1 p.2 := by
    apply (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n).mem_edgeSet.mp
    rw [hrepr]
    exact e.property
  have hsq := (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
  have hp1 := p.1.property
  have hp2 := p.2.property
  rw [mem_latticeRectangle] at hp1 hp2
  have hbounds1 : -((n+1:ℕ):ℤ) ≤ p.1.val.1 ∧ p.1.val.1 ≤ (n+1:ℤ) ∧
      0 ≤ p.1.val.2 ∧ p.1.val.2 ≤ (n:ℤ) := by
    rcases hp1 with ⟨⟨hlo,hhi⟩,⟨hylo,hyhi⟩⟩
    constructor
    · exact hlo
    · constructor
      · push_cast at hhi ⊢; omega
      · exact ⟨hylo,by push_cast at hyhi ⊢; omega⟩
  have hbounds2 : -((n+1:ℕ):ℤ) ≤ p.2.val.1 ∧ p.2.val.1 ≤ (n+1:ℤ) ∧
      0 ≤ p.2.val.2 ∧ p.2.val.2 ≤ (n:ℤ) := by
    rcases hp2 with ⟨⟨hlo,hhi⟩,⟨hylo,hyhi⟩⟩
    constructor
    · exact hlo
    · constructor
      · push_cast at hhi ⊢; omega
      · exact ⟨hylo,by push_cast at hyhi ⊢; omega⟩
  have hnotboth : ¬ (p.1.val.1 ≤ (n:ℤ) ∧ p.2.val.1 ≤ (n:ℤ)) := by
    intro hboth
    let u : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n :=
      ⟨p.1.val, by
        rw [mem_latticeRectangle]
        constructor
        · constructor <;> omega
        · constructor <;> omega⟩
    let v : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n :=
      ⟨p.2.val, by
        rw [mem_latticeRectangle]
        constructor
        · constructor <;> omega
        · constructor <;> omega⟩
    have hin : (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).Adj u v := by
      apply (rectangleGraph_adj_iff (-(n:ℤ)-1,0) (2*n+1) n u v).2
      simpa [u,v] using hsq
    have hmap : ((rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).map
        (originCmpVertexEmbedding n)).Adj
        (originCmpVertexEmbedding n u) (originCmpVertexEmbedding n v) :=
      (SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,hin,rfl,rfl⟩
    have he' : e.val = s(originCmpVertexEmbedding n u,originCmpVertexEmbedding n v) := by
      rw [← hrepr]
      apply (Sym2.eq_iff).2
      left
      constructor <;> apply Subtype.ext <;> rfl
    exact he (by
      rw [he']
      exact ((rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).map
        (originCmpVertexEmbedding n)).mem_edgeSet.mpr hmap)
  have hcoords1 : p.1.val.1 = (n:ℤ) ∨ p.1.val.1 = (n+1:ℤ) := by
    by_cases hle : p.1.val.1 ≤ (n:ℤ)
    · have hgt : (n:ℤ) < p.2.val.1 := by
        by_contra h
        exact hnotboth ⟨hle,le_of_not_gt h⟩
      rcases hsq with ⟨hh,hv⟩ | ⟨hx,hh⟩
      · rcases hh with h | h <;> omega
      · omega
    · right
      omega
  have hcoords2 : p.2.val.1 = (n:ℤ) ∨ p.2.val.1 = (n+1:ℤ) := by
    by_cases hle : p.2.val.1 ≤ (n:ℤ)
    · have hgt : (n:ℤ) < p.1.val.1 := by
        by_contra h
        exact hnotboth ⟨le_of_not_gt h,hle⟩
      rcases hsq with ⟨hh,hv⟩ | ⟨hx,hh⟩
      · rcases hh with h | h <;> omega
      · omega
    · right
      omega
  have hmember (u : RectangleVertex (-(n+1:ℤ),0) (2*(n+1)) n)
      (hu : u ∈ e.val) : u.val = p.1.val ∨ u.val = p.2.val := by
    rw [← hrepr] at hu
    rcases (Sym2.mem_iff').mp hu with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  intro u hu
  rcases hmember u hu with h | h
  · rw [h]
    exact hcoords1
  · rw [h]
    exact hcoords2


private theorem originCmp_innerBoundary_of_outer_union_D (n : ℕ)
    (u : RectangleVertex (-(n:ℤ)-1,0) (2*n+1) n)
    (hu : originCmpVertexEmbedding n u ∈
      originCmpOuterBoundary n ∪ {v | v.val.1 = (n:ℤ) ∨ v.val.1 = (n+1:ℤ)}) :
    u ∈ generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n := by
  have huBound : u.val.1 ≤ (n:ℤ) := by
    have hu' := u.property
    rw [mem_latticeRectangle] at hu'
    calc
      u.val.1 ≤ (-(n:ℤ)-1) + ((2*n+1:ℕ):ℤ) := hu'.1.2
      _ = (n:ℤ) := by push_cast; omega
  change originCmpVertexEmbedding n u ∈ originCmpOuterBoundary n ∨
    originCmpVertexEmbedding n u ∈ {v | v.val.1 = (n:ℤ) ∨ v.val.1 = (n+1:ℤ)} at hu
  have hv : (originCmpVertexEmbedding n u).val = u.val := rfl
  rcases hu with hξ | hD
  · have hξ' : (originCmpVertexEmbedding n u).val.1 = -((n+1:ℕ):ℤ) ∨
        (originCmpVertexEmbedding n u).val.1 = (n+1:ℤ) ∨
        (originCmpVertexEmbedding n u).val.2 = (n:ℤ) := by
      exact hξ
    rw [hv] at hξ'
    simp only [generalRectangleDualBottomCoreAmbientBoundary, Set.mem_ofPred_eq]
    rcases hξ' with hleft | hright | htop
    · left; push_cast at hleft ⊢; omega
    · exfalso; omega
    · right; right; omega
  · have hD' : (originCmpVertexEmbedding n u).val.1 = (n:ℤ) ∨
        (originCmpVertexEmbedding n u).val.1 = (n+1:ℤ) := by
      exact hD
    rw [hv] at hD'
    simp only [generalRectangleDualBottomCoreAmbientBoundary, Set.mem_ofPred_eq]
    rcases hD' with hright | hright
    · right; left; omega
    · exfalso; omega

private theorem originCmp_frozen_partition_le (n : ℕ)
    (K : RemovedConfiguration (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n)
      (subgraphRemovedEdges
        ((rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n).map (originCmpVertexEmbedding n))
        (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n))) :
    (isolatedExtensionPullbackBoundary (originCmpVertexEmbedding n)
      (frozenBoundary (BoundaryCondition.wired (originCmpOuterBoundary n)) K.val)).partition ≤
      (BoundaryCondition.wired
        (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n)).partition := by
  classical
  let ξ : BoundaryCondition (RectangleVertex (-(n+1:ℤ),0) (2*(n+1)) n) :=
    BoundaryCondition.wired (originCmpOuterBoundary n)
  let D : Set (RectangleVertex (-(n+1:ℤ),0) (2*(n+1)) n) :=
    {v | v.val.1 = (n:ℤ) ∨ v.val.1 = (n+1:ℤ)}
  have hcomp := componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val (by
    intro e he u hu
    have hnot := (mem_subgraphRemovedEdges e).mp (K.property he)
    exact originCmp_removedEdge_endpoints_zone n e hnot hu)
  intro u v huv
  change (frozenBoundary ξ K.val).partition.r
    (originCmpVertexEmbedding n u) (originCmpVertexEmbedding n v) at huv
  have hout := hcomp huv
  rcases (BoundaryCondition.wired_rel _ _ _).mp hout with heq | ⟨huOuter, hvOuter⟩
  · exact Or.inl ((originCmpVertexEmbedding n).injective heq)
  · exact Or.inr ⟨originCmp_innerBoundary_of_outer_union_D n u huOuter,
      originCmp_innerBoundary_of_outer_union_D n v hvOuter⟩



private theorem originCmp_outerBoundary_eq (n : ℕ) :
    originCmpOuterBoundary n = horizontalStripOriginLocalWiredSet (n+1) n := by
  ext v
  have hv := v.property
  rw [mem_latticeRectangle] at hv
  simp [originCmpOuterBoundary, horizontalStripOriginLocalWiredSet,
    rectangleLeftSide, rectangleRightSide, rectangleTopSide,
    Finset.mem_union, Finset.mem_filter, mem_latticeRectangle]; omega


private theorem originCmp_measure_toReal_eq_expectation
    {V : Type*} [Finite V] {G : SimpleGraph V} (q : ClusterWeight)
    (ξ : BoundaryCondition V) (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : Fintype (Configuration G) := Fintype.ofFinite _
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr
  · ext A
    simp only [Finset.mem_univ]
  · intro A hA
    simp [law_apply, ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]

private theorem originCmp_embedded_marginal_probability_le
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (hGH : G.map f ≤ H) (q : ClusterWeight) (ξ : BoundaryCondition W)
    (η : BoundaryCondition V)
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤ η.partition)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure H q ξ {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal ≤
      (measure G q η S).toReal := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : Fintype H.edgeSet := Fintype.ofFinite _
  let : Fintype (Configuration G) := Fintype.ofFinite _
  let : Fintype (Configuration H) := Fintype.ofFinite _
  let : Fintype (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :=
    Fintype.ofFinite _
  let ρ := embeddedConfigurationRestriction G H f hGH
  let φ := S.indicator (fun _ => (1 : ℝ))
  let p := law H q ξ
  let Klaw := frozenMarginalLaw q ξ (subgraphRemovedEdges (G.map f) H)
  let Q := fun K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H) =>
    law G q (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))
  have houter :
      (measure H q ξ {A | ρ A ∈ S}).toReal = expectation p (fun A => φ (ρ A)) := by
    rw [originCmp_measure_toReal_eq_expectation]
    change expectation (law H q ξ) ({A | ρ A ∈ S}.indicator (fun _ => (1 : ℝ))) =
      expectation (law H q ξ) (fun A => φ (ρ A))
    congr 1
  have hmap : p.map ρ = Klaw.bind Q := by
    dsimp [p, Klaw, Q, ρ]
    exact law_embeddedConfigurationRestriction_eq_bind_frozenMarginal G H f hGH q ξ
  have hcond (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
      expectation (Q K) φ ≤ expectation (law G q η) φ := by
    have h := measure_boundary_comparison q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) η (hpart K) S hS
    change expectation (law G q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)))
      (S.indicator (fun _ => (1 : ℝ))) ≤
      expectation (law G q η) (S.indicator (fun _ => (1 : ℝ)))
    rw [← originCmp_measure_toReal_eq_expectation q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S,
      ← originCmp_measure_toReal_eq_expectation q η S]
    exact h
  have htarget := originCmp_measure_toReal_eq_expectation q η S
  calc
    (measure H q ξ {A | ρ A ∈ S}).toReal = expectation p (fun A => φ (ρ A)) := houter
    _ = expectation (p.map ρ) φ := by rw [expectation_map]
    _ = expectation (Klaw.bind Q) φ := by rw [hmap]
    _ ≤ expectation Klaw (fun _ => expectation (law G q η) φ) := by
      rw [expectation_bind]
      apply expectation_mono
      intro K
      exact hcond K
    _ = expectation (law G q η) φ := by rw [expectation_const]
    _ = (measure G q η S).toReal := htarget.symm

private theorem originCmp_ordinaryEvent_upper (n : ℕ) :
    IsUpperSet (parafermionicCoverEq24OrdinaryOriginEvent n) := by
  intro A B hAB hA
  rcases hA with ⟨z, hz, hconn⟩
  exact ⟨z, hz, actualConnected_mono hAB hconn⟩


theorem measure_horizontalStripOriginLocalConnection_le_ordinaryOriginEvent
    (q : ClusterWeight) (n : ℕ) :
    (measure (rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n) q
      (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet (n+1) n))
      (horizontalStripOriginLocalConnectionEvent (n+1) n)).toReal ≤
    (measure (rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n) q
      (BoundaryCondition.wired
        (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n))
      (parafermionicCoverEq24OrdinaryOriginEvent n)).toReal := by
  classical
  let G := rectangleGraph (-(n:ℤ)-1,0) (2*n+1) n
  let H := rectangleGraph (-(n+1:ℤ),0) (2*(n+1)) n
  let f := originCmpVertexEmbedding n
  let hGH := originCmpMapLe n
  let ξ : BoundaryCondition _ := BoundaryCondition.wired (originCmpOuterBoundary n)
  let η : BoundaryCondition _ := BoundaryCondition.wired
    (generalRectangleDualBottomCoreAmbientBoundary (-(n:ℤ),0) (2*n) n)
  let S := parafermionicCoverEq24OrdinaryOriginEvent n
  let O := horizontalStripOriginLocalConnectionEvent (n+1) n
  have hxi : BoundaryCondition.wired (originCmpOuterBoundary n) =
      BoundaryCondition.wired (horizontalStripOriginLocalWiredSet (n+1) n) := by
    rw [originCmp_outerBoundary_eq]
  have hsubset : O ⊆ {A : Configuration H | embeddedConfigurationRestriction G H f hGH A ∈ S} := by
    intro A hA
    exact originCmp_actual_event_subset n A hA
  have hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤ η.partition := by
    intro K
    exact originCmp_frozen_partition_le n K
  have hmargin := originCmp_embedded_marginal_probability_le G H f hGH q ξ η
    hpart S (originCmp_ordinaryEvent_upper n)
  calc
    (measure H q (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet (n+1) n)) O).toReal
        = (measure H q ξ O).toReal := by rw [← hxi]
    _ ≤ (measure H q ξ {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ ≤ (measure G q η S).toReal := hmargin

end
end PottsContinuity.FKC.FiniteFK
