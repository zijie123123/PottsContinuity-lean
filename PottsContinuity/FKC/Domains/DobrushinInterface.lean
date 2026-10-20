-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/DobrushinInterface.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.DobrushinBoundary
public import PottsContinuity.FKC.Medial.DobrushinPairing

/-!
# The finite port interface in the source's marked direction

For every actual marked lattice boundary, including its arbitrary admissible
boundary parametrization, a proved cyclic presentation realizes the genuine
wired half and its removed original edges. That presentation supplies the
actual finite port graph. The marked endpoint identities decide whether to
use its wired-start-to-finish path or its reverse, giving first mark to second
mark in all cases. No direction or path-existence hypothesis is added.

The cyclic presentation is chosen from a proved existence theorem. Its port
carrier is explicitly identified below with the retention rule using the
source's geometric removed-edge set. This module constructs an ordered finite
port walk, not a continuous curve or a scaling-limit statement.
-/

@[expose] public section

namespace PottsContinuity.FKC.MarkedLatticeBoundary

open Set Medial FiniteFK

noncomputable section

/-- A cyclic start provided by the proved model of the actual wired half. -/
def interfaceArcStart (B : MarkedLatticeBoundary) : ZMod (B.size + 3) :=
  Classical.choose B.exists_forwardArc_model

/-- The corresponding actual number of wired boundary edges. -/
def interfaceArcLength (B : MarkedLatticeBoundary) : ℕ :=
  Classical.choose (Classical.choose_spec B.exists_forwardArc_model)

private theorem interfaceArc_spec (B : MarkedLatticeBoundary) :
    1 ≤ B.interfaceArcLength ∧ B.interfaceArcLength ≤ B.size + 2 ∧
      ((B.interfaceArcStart = B.second ∧ B.interfaceArcStart + B.interfaceArcLength = B.first) ∨
       (B.interfaceArcStart = B.first ∧ B.interfaceArcStart + B.interfaceArcLength = B.second)) ∧
      B.wiredVertices = B.polygon.forwardArcVertices B.mesh B.interfaceArcStart B.interfaceArcLength ∧
      B.boundaryCondition = B.polygon.forwardArcBoundary B.mesh B.interfaceArcStart B.interfaceArcLength ∧
      B.removedEdges = B.polygon.forwardArcRemovedEdges B.mesh B.interfaceArcStart B.interfaceArcLength ∧
      ∀ q : ClusterWeight, B.fullLaw q =
        B.polygon.forwardArcLaw B.mesh q B.interfaceArcStart B.interfaceArcLength :=
  Classical.choose_spec (Classical.choose_spec B.exists_forwardArc_model)

theorem interfaceArc_length_pos (B : MarkedLatticeBoundary) : 1 ≤ B.interfaceArcLength :=
  B.interfaceArc_spec.1

theorem interfaceArc_length_proper (B : MarkedLatticeBoundary) :
    B.interfaceArcLength ≤ B.size + 2 := B.interfaceArc_spec.2.1

theorem interfaceArc_endpoints (B : MarkedLatticeBoundary) :
    ((B.interfaceArcStart = B.second ∧ B.interfaceArcStart + B.interfaceArcLength = B.first) ∨
     (B.interfaceArcStart = B.first ∧ B.interfaceArcStart + B.interfaceArcLength = B.second)) :=
  B.interfaceArc_spec.2.2.1

theorem interfaceArc_removedEdges (B : MarkedLatticeBoundary) :
    B.removedEdges = B.polygon.forwardArcRemovedEdges B.mesh B.interfaceArcStart B.interfaceArcLength :=
  B.interfaceArc_spec.2.2.2.2.2.1

/-- The actual retained port carrier in this proved presentation of the wired half. -/
abbrev InterfacePort (B : MarkedLatticeBoundary) :=
  B.polygon.RetainedPort B.mesh B.interfaceArcStart B.interfaceArcLength

/-- Retention is exactly the source's actual geometric removal rule. -/
def interfacePortEquiv (B : MarkedLatticeBoundary) :
    B.InterfacePort ≃ {p : DomainPort B.mesh (B.polygon.domain B.mesh) //
      openLatticeCell B.mesh p.toLatticePort.faceBase ⊆ B.polygon.domain B.mesh ∨
        p.bond.toGraphEdge ∉ B.removedEdges} where
  toFun p := ⟨p.val, by rw [B.interfaceArc_removedEdges]; exact p.property⟩
  invFun p := ⟨p.val, by rw [← B.interfaceArc_removedEdges]; exact p.property⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

/-- The finite actual graph uses the same original configuration and proved wired-edge mask. -/
def interfaceGraph (B : MarkedLatticeBoundary) (C : Configuration B.graph) :
    SimpleGraph (B.InterfacePort × Bool) :=
  B.polygon.dobrushinPortGraph B.mesh B.interfaceArcStart B.interfaceArcLength C

/-- The true local drawing state forces exactly the source's removed edges open. -/
theorem interfaceLocalPair_val (B : MarkedLatticeBoundary) (C : Configuration B.graph)
    (p : B.InterfacePort) :
    (B.polygon.retainedLocalPair B.mesh B.interfaceArcStart B.interfaceArcLength C p).val =
      DomainPort.localPair (C ∪ B.removedEdges) p.val := by
  rw [B.polygon.retainedLocalPair_val, B.interfaceArc_removedEdges]

/-- Select the endpoint at the source's first mark using the proved endpoint alternatives. -/
def firstInterfacePort (B : MarkedLatticeBoundary) : B.InterfacePort :=
  if B.interfaceArcStart = B.first then
    B.polygon.wiredStartPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper
  else B.polygon.wiredFinishPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper

/-- The other endpoint, at the source's second mark. -/
def secondInterfacePort (B : MarkedLatticeBoundary) : B.InterfacePort :=
  if B.interfaceArcStart = B.first then
    B.polygon.wiredFinishPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper
  else B.polygon.wiredStartPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper

theorem firstInterfacePort_primalVertex (B : MarkedLatticeBoundary) :
    B.firstInterfacePort.val.toLatticePort.primalVertex = B.polygon.vertex B.first := by
  unfold firstInterfacePort
  split_ifs with h
  · rw [B.polygon.wiredStartPort_primalVertex, h]
  · rw [B.polygon.wiredFinishPort_primalVertex]
    rcases B.interfaceArc_endpoints with he | he
    · rw [he.2]
    · exact (h he.1).elim

theorem secondInterfacePort_primalVertex (B : MarkedLatticeBoundary) :
    B.secondInterfacePort.val.toLatticePort.primalVertex = B.polygon.vertex B.second := by
  unfold secondInterfacePort
  split_ifs with h
  · rw [B.polygon.wiredFinishPort_primalVertex]
    rcases B.interfaceArc_endpoints with he | he
    · exact (B.marks_ne (h.symm.trans he.1)).elim
    · rw [he.2]
  · rw [B.polygon.wiredStartPort_primalVertex]
    rcases B.interfaceArc_endpoints with he | he
    · rw [he.1]
    · exact (h he.1).elim

theorem interfacePorts_ne (B : MarkedLatticeBoundary) :
    B.firstInterfacePort ≠ B.secondInterfacePort := by
  intro h
  have hv := congrArg (fun p : B.InterfacePort => p.val.toLatticePort.primalVertex) h
  rw [B.firstInterfacePort_primalVertex, B.secondInterfacePort_primalVertex] at hv
  exact B.marks_ne (B.polygon.vertex_injective hv)

/-- The attachment point of the first terminal is exactly the paper's first complex mark. -/
theorem firstInterfacePort_mark (B : MarkedLatticeBoundary) :
    latticeEmbed B.mesh B.firstInterfacePort.val.toLatticePort.primalVertex = B.markedDomain.a := by
  rw [B.firstInterfacePort_primalVertex, B.markedDomain_a]

/-- The attachment point of the second terminal is exactly the paper's second complex mark. -/
theorem secondInterfacePort_mark (B : MarkedLatticeBoundary) :
    latticeEmbed B.mesh B.secondInterfacePort.val.toLatticePort.primalVertex = B.markedDomain.b := by
  rw [B.secondInterfacePort_primalVertex, B.markedDomain_b]

private theorem existsUnique_isPath_reverse {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : ∃! p : G.Walk u v, p.IsPath) : ∃! p : G.Walk v u, p.IsPath := by
  obtain ⟨p, hp, huniq⟩ := h
  refine ⟨p.reverse, hp.reverse, ?_⟩
  intro q hq
  have he := congrArg (fun r : G.Walk u v => r.reverse) (huniq q.reverse hq.reverse)
  simpa only [SimpleGraph.Walk.reverse_reverse] using he

/-- The actual finite simple port path is unique in the paper's first-to-second direction. -/
theorem interfaceGraph_existsUnique_isPath (B : MarkedLatticeBoundary)
    (C : Configuration B.graph) :
    ∃! p : (B.interfaceGraph C).Walk (B.firstInterfacePort, true)
      (B.secondInterfacePort, true), p.IsPath := by
  have h := B.polygon.dobrushinPortGraph_existsUnique_isPath B.mesh B.interfaceArcStart
    B.interfaceArc_length_pos B.interfaceArc_length_proper C
  by_cases hfirst : B.interfaceArcStart = B.first
  · have hf : B.firstInterfacePort =
        B.polygon.wiredStartPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper := by
      simp only [firstInterfacePort, ite_eq_left hfirst]
    have hs : B.secondInterfacePort =
        B.polygon.wiredFinishPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper := by
      simp only [secondInterfacePort, ite_eq_left hfirst]
    rw [hf, hs]
    exact h
  · have hf : B.firstInterfacePort =
        B.polygon.wiredFinishPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper := by
      simp only [firstInterfacePort, ite_eq_right hfirst]
    have hs : B.secondInterfacePort =
        B.polygon.wiredStartPort B.mesh B.interfaceArcStart B.interfaceArc_length_proper := by
      simp only [secondInterfacePort, ite_eq_right hfirst]
    rw [hf, hs]
    exact existsUnique_isPath_reverse h

/-- The unique ordered actual port walk, oriented from the first mark to the second. -/
def interfaceWalk (B : MarkedLatticeBoundary) (C : Configuration B.graph) :
    (B.interfaceGraph C).Walk (B.firstInterfacePort, true) (B.secondInterfacePort, true) :=
  Classical.choose (B.interfaceGraph_existsUnique_isPath C)

theorem interfaceWalk_isPath (B : MarkedLatticeBoundary) (C : Configuration B.graph) :
    (B.interfaceWalk C).IsPath :=
  (Classical.choose_spec (B.interfaceGraph_existsUnique_isPath C)).1

theorem interfaceWalk_unique (B : MarkedLatticeBoundary) (C : Configuration B.graph)
    (p : (B.interfaceGraph C).Walk (B.firstInterfacePort, true) (B.secondInterfacePort, true))
    (hp : p.IsPath) : p = B.interfaceWalk C :=
  (Classical.choose_spec (B.interfaceGraph_existsUnique_isPath C)).2 p hp

end
end PottsContinuity.FKC.MarkedLatticeBoundary
