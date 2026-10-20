/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/ParafermionicCoverPrimalConnectivity.lean`.
Adaptation: namespace/import relocation to PD actual paths and the full cover carrier.
-/
module

public import PottsContinuity.Thm4.FinitePorts
public import PottsContinuity.Thm4.PairingGraph
public import PottsContinuity.PD.FK.Graph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

/-- The actual finite-graph vertex represented by a retained lifted medial port. -/
def parafermionicCoverFinitePortPrimalVertex (n : ℕ)
    (c : ParafermionicCoverFinitePort n) : ParafermionicAmbientVertex n :=
  ⟨parafermionicCoverPortVertex c.1, c.2⟩

private theorem parafermionicCoverFiniteLocalPair_open_adj
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n)
    (hopen : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) c.1 = true) :
    (openGraph (ParafermionicAmbientGraph n) A).Adj
      (parafermionicCoverFinitePortPrimalVertex n c)
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteLocalPairPerm n A c)) := by
  classical
  let f := parafermionicCoverBoxVertexEmbedding n
  let eMap := embeddedEdgeEmbedding (ParafermionicAmbientGraph n) parafermionicCoverGraph
    f (parafermionicCoverBoxGraph_map_le n)
  have hmem : parafermionicCoverPortEdge c.1 ∈
      parafermionicCoverConfigurationExtension n A := by
    apply (parafermionicCoverConfigurationExtensionState_eq_true_iff n A
      (parafermionicCoverPortEdge c.1)).mp
    exact hopen
  rw [parafermionicCoverConfigurationExtension] at hmem
  rcases Finset.mem_map.mp hmem with ⟨e, heA, heMap⟩
  have hpair : (parafermionicCoverFiniteLocalPairPerm n A c).1 =
      parafermionicCoverOpenPair c.1 := by
    rw [parafermionicCoverFiniteLocalPairPerm_val]
    rw [parafermionicCoverLocalPair, ite_eq_left hopen]
  have hendpoint : parafermionicCoverPortOtherVertex c.1 =
      parafermionicCoverPortVertex
        ((parafermionicCoverFiniteLocalPairPerm n A c).1) := by
    calc
      parafermionicCoverPortOtherVertex c.1 =
          parafermionicCoverPortVertex (parafermionicCoverOpenPair c.1) :=
        (parafermionicCoverOpenPair_vertex c.1).symm
      _ = parafermionicCoverPortVertex
          ((parafermionicCoverFiniteLocalPairPerm n A c).1) :=
        congrArg parafermionicCoverPortVertex hpair.symm
  have hsym : Sym2.map f e.1 =
      s(f (parafermionicCoverFinitePortPrimalVertex n c),
        f (parafermionicCoverFinitePortPrimalVertex n
          (parafermionicCoverFiniteLocalPairPerm n A c))) := by
    calc
      Sym2.map f e.1 = (parafermionicCoverPortEdge c.1).1 := by
        have h := congrArg Subtype.val heMap
        simpa [eMap, embeddedEdgeEmbedding_coe] using h
      _ = s(parafermionicCoverPortVertex c.1,
          parafermionicCoverPortOtherVertex c.1) :=
        parafermionicCoverPortEdge_eq_incident_pair c.1
      _ = s(f (parafermionicCoverFinitePortPrimalVertex n c),
          f (parafermionicCoverFinitePortPrimalVertex n
            (parafermionicCoverFiniteLocalPairPerm n A c))) := by
        rw [hendpoint]
        rfl
  have heval : e.1 = s(parafermionicCoverFinitePortPrimalVertex n c,
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteLocalPairPerm n A c)) := by
    apply Sym2.map.injective f.injective
    simpa using hsym
  apply (openGraph_adj (ParafermionicAmbientGraph n) A _ _).2
  change s(parafermionicCoverFinitePortPrimalVertex n c,
    parafermionicCoverFinitePortPrimalVertex n
      (parafermionicCoverFiniteLocalPairPerm n A c)) ∈
      Subtype.val '' (↑A : Set (ParafermionicAmbientGraph n).edgeSet)
  exact ⟨e, heA, heval⟩

/-- One local pairing step preserves the actual primal FK component: an open
pairing uses the true original finite edge, while a closed pairing stays put. -/
theorem parafermionicCoverFiniteLocalPair_actualConnected
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n c)
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteLocalPairPerm n A c)) := by
  classical
  cases hstate : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) c.1 with
  | false =>
      have hvertex : parafermionicCoverFinitePortPrimalVertex n c =
          parafermionicCoverFinitePortPrimalVertex n
            (parafermionicCoverFiniteLocalPairPerm n A c) := by
        apply Subtype.ext
        change parafermionicCoverPortVertex c.1 =
          parafermionicCoverPortVertex ((parafermionicCoverFiniteLocalPairPerm n A c).1)
        rw [parafermionicCoverFiniteLocalPairPerm_val,
          parafermionicCoverLocalPair, ite_eq_right (by simpa using hstate)]
        exact (parafermionicCoverClosedPair_vertex c.1).symm
      simp [ActualConnected, hvertex]
  | true =>
      apply actualConnected_of_adj
      exact parafermionicCoverFiniteLocalPair_open_adj n A c hstate

/-- A corner-pair step preserves the actual primal vertex, hence its actual FK component. -/
theorem parafermionicCoverFiniteCornerPair_actualConnected
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n c)
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteCornerPairPerm n c)) := by
  have hvertex : parafermionicCoverFinitePortPrimalVertex n c =
      parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteCornerPairPerm n c) := by
    apply Subtype.ext
    change parafermionicCoverPortVertex c.1 =
      parafermionicCoverPortVertex ((parafermionicCoverFiniteCornerPairPerm n c).1)
    rw [parafermionicCoverFiniteCornerPairPerm_val]
    exact (parafermionicCoverCornerPair_vertex c.1).symm
  simp [ActualConnected, hvertex]

 theorem parafermionicCoverFinitePairingLocal_involutive
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n)) :
    Function.Involutive (parafermionicCoverFiniteLocalPairPerm n A) := by
  intro c
  apply Subtype.ext
  exact parafermionicCoverLocalPair_involutive _ c.1

 theorem parafermionicCoverFinitePairingCorner_involutive (n : ℕ) :
    Function.Involutive (parafermionicCoverFiniteCornerPairPerm n) := by
  intro c
  apply Subtype.ext
  exact parafermionicCoverCornerPair_involutive c.1

/-- The alternating graph of the actual finite local pairing and finite corner pairing. -/
def parafermionicCoverFinitePairingGraph (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    SimpleGraph (ParafermionicCoverFinitePort n × Bool) :=
  pairingGraph (parafermionicCoverFiniteLocalPairPerm n A)
    (parafermionicCoverFiniteCornerPairPerm n)
    (parafermionicCoverFinitePairingLocal_involutive n A)
    (parafermionicCoverFinitePairingCorner_involutive n)

private theorem parafermionicCoverFinitePairing_adj_actualConnected
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hadj : (parafermionicCoverFinitePairingGraph n A).Adj u v) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n u.1)
      (parafermionicCoverFinitePortPrimalVertex n v.1) := by
  rcases u with ⟨u, bu⟩
  rcases v with ⟨v, bv⟩
  cases bu <;> cases bv
  · have h := (pairingGraph_adj_false_false
      (parafermionicCoverFiniteLocalPairPerm n A)
      (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFinitePairingLocal_involutive n A)
      (parafermionicCoverFinitePairingCorner_involutive n) u v).mp hadj
    rw [← h.1]
    exact parafermionicCoverFiniteLocalPair_actualConnected n A u
  · have h := (pairingGraph_adj_false_true
      (parafermionicCoverFiniteLocalPairPerm n A)
      (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFinitePairingLocal_involutive n A)
      (parafermionicCoverFinitePairingCorner_involutive n) u v).mp hadj
    subst v
    exact SimpleGraph.Reachable.refl _
  · have h := (pairingGraph_adj_true_false
      (parafermionicCoverFiniteLocalPairPerm n A)
      (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFinitePairingLocal_involutive n A)
      (parafermionicCoverFinitePairingCorner_involutive n) u v).mp hadj
    subst v
    exact SimpleGraph.Reachable.refl _
  · have h := (pairingGraph_adj_true_true
      (parafermionicCoverFiniteLocalPairPerm n A)
      (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFinitePairingLocal_involutive n A)
      (parafermionicCoverFinitePairingCorner_involutive n) u v).mp hadj
    rw [← h.1]
    exact parafermionicCoverFiniteCornerPair_actualConnected n A u

/-- Every actual finite alternating medial walk projects to connectivity in the
same finite open FK configuration. -/
theorem parafermionicCoverFinitePairingWalk_actualConnected
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFinitePairingGraph n A).Walk u v) :
    ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n u.1)
      (parafermionicCoverFinitePortPrimalVertex n v.1) := by
  induction p with
  | nil =>
      exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj p ih =>
      exact (parafermionicCoverFinitePairing_adj_actualConnected n A hadj).trans ih

end
end PottsContinuity.Thm4
