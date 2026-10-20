-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverContourEdgeSum.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverContourIdentity
public import PottsContinuity.FKC.Medial.ParafermionicCoverFiniteEdgePort
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial
open scoped BigOperators
noncomputable section

local instance contourEdgePortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) := Fintype.ofFinite _
local instance contourEdgeFintype (n : ℕ) : Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance contourEdgeAmbientEdgeDecidable (n : ℕ) : DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

def contourEdgeInternal (n : ℕ) (c : ParafermionicCoverFinitePort n) : Prop :=
  parafermionicCoverFinitePortOtherEndpointInBox n c

local instance contourEdgeInternalDecidable (n : ℕ) :
    DecidablePred (contourEdgeInternal n) := Classical.decPred _
local instance contourEdgeActualInternalDecidable (n : ℕ) :
    DecidablePred (fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverFinitePortOtherEndpointInBox n c) := Classical.decPred _

abbrev contourEdgeInternalPort (n : ℕ) :=
  {c : ParafermionicCoverFinitePort n // contourEdgeInternal n c}

 theorem contourEdge_exists_finiteEdge (n : ℕ)
    (c : ParafermionicCoverFinitePort n)
    (hc : contourEdgeInternal n c) :
    ∃ e : (ParafermionicAmbientGraph n).edgeSet,
      parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
  classical
  let x : ParafermionicAmbientVertex n := ⟨parafermionicCoverPortVertex c.1, c.2⟩
  let y : ParafermionicAmbientVertex n := ⟨parafermionicCoverPortOtherVertex c.1, hc⟩
  have hadjCover : parafermionicCoverGraph.Adj x.1 y.1 :=
    parafermionicCoverPortVertex_otherEndpoint_adj c.1
  have hadj : (ParafermionicAmbientGraph n).Adj x y := by
    change (parafermionicCoverBoxGraph n).Adj x y
    change parafermionicCoverGraph.Adj x.1 y.1
    exact hadjCover
  let e : (ParafermionicAmbientGraph n).edgeSet :=
    ⟨Sym2.mk x y, (ParafermionicAmbientGraph n).mem_edgeSet.mpr hadj⟩
  refine ⟨e, ?_⟩
  apply Subtype.ext
  rw [parafermionicCoverPortEdge_eq_incident_pair,
    parafermionicCoverFiniteEdgeEmbedding, embeddedEdgeEmbedding_coe]
  simp [e, Function.Embedding.sym2Map_apply, parafermionicCoverBoxVertexEmbedding]
  exact Or.inl ⟨rfl, rfl⟩

noncomputable def contourEdgeOfInternalPort (n : ℕ)
    (c : contourEdgeInternalPort n) : (ParafermionicAmbientGraph n).edgeSet :=
  Classical.choose (contourEdge_exists_finiteEdge n c.1 c.2)

private theorem contourEdgeOfInternalPort_spec (n : ℕ)
    (c : contourEdgeInternalPort n) :
    parafermionicCoverPortEdge c.1.1 =
      parafermionicCoverFiniteEdgeEmbedding n (contourEdgeOfInternalPort n c) :=
  Classical.choose_spec (contourEdge_exists_finiteEdge n c.1 c.2)

def contourEdgeSign (n : ℕ) (c : ParafermionicCoverFinitePort n) : ℂ :=
  if parafermionicCoverIncomingPrimalLeft c.1 then 1 else -1

def contourEdgeValue (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n)
    (c : ParafermionicCoverFinitePort n) : ℂ :=
  parafermionicCoverPathPhaseExpectation q n hn (c, true)

def parafermionicCoverContourFiniteEdgeDefect (q : ClusterWeight) (n : ℕ)
    (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet) : ℂ := by
  classical
  exact ∑ c ∈ (Finset.univ : Finset
      {c : ParafermionicCoverFinitePort n //
        parafermionicCoverFinitePortOtherEndpointInBox n c}).filter
      (fun c => parafermionicCoverPortEdge c.1.1 =
        parafermionicCoverFiniteEdgeEmbedding n e),
    (if parafermionicCoverIncomingPrimalLeft c.1.1 then (1 : ℂ) else -1) *
      parafermionicCoverPathPhaseExpectation q n hn (c.1, true)

theorem parafermionicCoverPathPhaseExpectation_contour_edge_sum
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    (∑ e : (ParafermionicAmbientGraph n).edgeSet,
      parafermionicCoverContourFiniteEdgeDefect q n hn e) =
      ∑ c ∈ Finset.univ.filter (fun c : ParafermionicCoverFinitePort n =>
          parafermionicCoverFinitePortOtherEndpointInBox n c),
        (if parafermionicCoverIncomingPrimalLeft c.1 then (1 : ℂ) else -1) *
          parafermionicCoverPathPhaseExpectation q n hn (c, true) := by
  classical
  change (∑ e : (ParafermionicAmbientGraph n).edgeSet,
      parafermionicCoverContourFiniteEdgeDefect q n hn e) =
    ∑ c ∈ Finset.univ.filter (contourEdgeInternal n),
      contourEdgeSign n c * contourEdgeValue q n hn c
  let F : Finset (ParafermionicCoverFinitePort n) :=
    Finset.univ.filter (contourEdgeInternal n)
  let g : contourEdgeInternalPort n → (ParafermionicAmbientGraph n).edgeSet :=
    contourEdgeOfInternalPort n
  have hmap : ∀ c ∈ Finset.univ, g c ∈
      (Finset.univ : Finset (ParafermionicAmbientGraph n).edgeSet) := by
    intro c hc
    simp
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun c : contourEdgeInternalPort n => contourEdgeSign n c.1 * contourEdgeValue q n hn c.1)
  have hconvert :
      (∑ c ∈ F, contourEdgeSign n c * contourEdgeValue q n hn c) =
        ∑ c : contourEdgeInternalPort n,
          contourEdgeSign n c.1 * contourEdgeValue q n hn c.1 := by
    unfold F
    have hmem : ∀ c : ParafermionicCoverFinitePort n,
        c ∈ Finset.univ.filter (contourEdgeInternal n) ↔ contourEdgeInternal n c := by
      intro c
      simp
    rw [Finset.sum_subtype (Finset.univ.filter (contourEdgeInternal n)) hmem]
  rw [hconvert, ← hfiber]
  apply Finset.sum_congr rfl
  intro e he
  unfold parafermionicCoverContourFiniteEdgeDefect
  simp only [contourEdgeSign, contourEdgeValue, Finset.sum_filter]
  apply Finset.sum_congr (by
    apply Finset.ext
    intro c
    exact ⟨fun _ => Finset.mem_univ c, fun _ => Finset.mem_univ c⟩)
  intro c hc
  have hiff :
      (parafermionicCoverPortEdge c.1.1 = parafermionicCoverFiniteEdgeEmbedding n e) ↔
        g c = e := by
    constructor
    · intro hport
      apply (parafermionicCoverFiniteEdgeEmbedding n).injective
      calc
        parafermionicCoverFiniteEdgeEmbedding n (g c) = parafermionicCoverPortEdge c.1.1 :=
          (contourEdgeOfInternalPort_spec n c).symm
        _ = parafermionicCoverFiniteEdgeEmbedding n e := hport
    · intro hge
      calc
        parafermionicCoverPortEdge c.1.1 =
            parafermionicCoverFiniteEdgeEmbedding n (g c) :=
          contourEdgeOfInternalPort_spec n c
        _ = parafermionicCoverFiniteEdgeEmbedding n e := congrArg
          (parafermionicCoverFiniteEdgeEmbedding n) hge
  simp only [hiff]

theorem parafermionicCoverPathPhaseExpectation_contour_edge_identity
    (q : ClusterWeight) (n : ℕ) (hn : 1 ≤ n) :
    (∑ e : (ParafermionicAmbientGraph n).edgeSet,
      parafermionicCoverContourFiniteEdgeDefect q n hn e) =
      (∑ e ∈ parafermionicCoverExposedCorners n,
        (if parafermionicCoverIncomingPrimalLeft e.1.1 then (1 : ℂ) else -1) *
          parafermionicCoverPathPhaseExpectation q n hn (e.1, true)) +
        parafermionicCoverPathPhaseExpectation q n hn
          (parafermionicCoverFiniteOriginCornerPort n hn, true) -
        parafermionicCoverPathPhaseExpectation q n hn
          (parafermionicCoverFiniteCornerPairPerm n
            (parafermionicCoverFiniteOriginCornerPort n hn), true) := by
  rw [parafermionicCoverPathPhaseExpectation_contour_edge_sum,
    parafermionicCoverPathPhaseExpectation_contour_identity]

end
end PottsContinuity.FKC.FiniteFK
