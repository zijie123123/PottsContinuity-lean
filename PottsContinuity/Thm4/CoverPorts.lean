/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverPorts.lean`.
Adaptation: namespace/import relocation to the exact frozen-base cover graph.
-/
module

public import PottsContinuity.Thm4.LatticePorts
public import PottsContinuity.Thm4.CoverGraph

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open LatticeAxis LatticePort

/-- A cover port remembers the sheet of its actual primal endpoint. -/
abbrev ParafermionicCoverPort := LatticePort × ℤ

/-- The actual cover vertex supporting a lifted medial port. -/
def parafermionicCoverPortVertex (c : ParafermionicCoverPort) : ParafermionicCoverVertex :=
  (c.1.primalVertex, c.2)

/-- Sheet of the normalized source endpoint for the bond underlying a lifted port. -/
def parafermionicCoverPortSourceSheet (c : ParafermionicCoverPort) : ℤ :=
  if c.1.tip then c.2 - parafermionicCoverSheetShift c.1.bond.source c.1.bond.target
  else c.2

/-- The other endpoint of the lifted original bond at a lifted port. -/
def parafermionicCoverPortOtherVertex (c : ParafermionicCoverPort) : ParafermionicCoverVertex :=
  if c.1.tip then
    (c.1.bond.source,
      c.2 - parafermionicCoverSheetShift c.1.bond.source c.1.bond.target)
  else
    (c.1.bond.target,
      c.2 + parafermionicCoverSheetShift c.1.bond.source c.1.bond.target)

/-- The opposite endpoint is precisely the unique neighbor lift from this port. -/
theorem parafermionicCoverPortOtherVertex_eq_neighborLift (c : ParafermionicCoverPort) :
    parafermionicCoverPortOtherVertex c =
      parafermionicCoverNeighborLift (parafermionicCoverPortVertex c)
        (if c.1.tip then c.1.bond.source else c.1.bond.target) := by
  rcases c with ⟨⟨b, tip, side⟩, k⟩
  cases tip
  · simp [parafermionicCoverPortOtherVertex, parafermionicCoverPortVertex,
      parafermionicCoverNeighborLift, LatticePort.primalVertex,
      LatticeBond.endpoint]
  · simp only [parafermionicCoverPortOtherVertex, parafermionicCoverPortVertex,
      parafermionicCoverNeighborLift, LatticePort.primalVertex,
      LatticeBond.endpoint, ite_true]
    rw [parafermionicCoverSheetShift_reverse]
    ring_nf

/-- The actual unordered cover-graph edge incident to a lifted medial port. -/
def parafermionicCoverPortEdge (c : ParafermionicCoverPort) : parafermionicCoverGraph.edgeSet :=
  let b := c.1.bond
  let k := parafermionicCoverPortSourceSheet c
  ⟨s((b.source, k), (b.target, k + parafermionicCoverSheetShift b.source b.target)), by
    apply parafermionicCoverGraph.mem_edgeSet.mpr
    exact ⟨b.adjacent, rfl⟩⟩

@[simp] theorem parafermionicCoverPortEdge_val (c : ParafermionicCoverPort) :
    (parafermionicCoverPortEdge c).val =
      s((c.1.bond.source, parafermionicCoverPortSourceSheet c),
        (c.1.bond.target, parafermionicCoverPortSourceSheet c +
          parafermionicCoverSheetShift c.1.bond.source c.1.bond.target)) := rfl

/-- The source/target sheet convention agrees exactly with the primal endpoint flag. -/
theorem parafermionicCoverPortEdge_eq_incident_pair (c : ParafermionicCoverPort) :
    (parafermionicCoverPortEdge c).val =
      s(parafermionicCoverPortVertex c, parafermionicCoverPortOtherVertex c) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;>
    simp [parafermionicCoverPortEdge, parafermionicCoverPortVertex,
      parafermionicCoverPortOtherVertex, parafermionicCoverPortSourceSheet,
      LatticePort.primalVertex, LatticeBond.endpoint, LatticeBond.source,
      LatticeBond.target, parafermionicCoverSheetShift]

/-- Projecting the actual lifted unordered edge gives exactly its normalized base bond. -/
theorem parafermionicCoverPortEdge_projection (c : ParafermionicCoverPort) :
    Sym2.map Prod.fst (parafermionicCoverPortEdge c).val = c.1.bond.toSym2 := by
  rw [parafermionicCoverPortEdge_val]
  simp [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target]

/-- The primal projection of a lifted port is its original port endpoint. -/
@[simp] theorem parafermionicCoverPortVertex_fst (c : ParafermionicCoverPort) :
    (parafermionicCoverPortVertex c).1 = c.1.primalVertex := rfl

/-- Open pairing crosses the same lifted original edge to its other endpoint. -/
def parafermionicCoverOpenPair (c : ParafermionicCoverPort) : ParafermionicCoverPort :=
  (c.1.openPair, (parafermionicCoverPortOtherVertex c).2)

/-- Closed pairing stays at the same lifted primal endpoint. -/
def parafermionicCoverClosedPair (c : ParafermionicCoverPort) : ParafermionicCoverPort :=
  (c.1.closedPair, c.2)

/-- Corner pairing crosses to the other medial edge at the same lifted primal corner. -/
def parafermionicCoverCornerPair (c : ParafermionicCoverPort) : ParafermionicCoverPort :=
  (c.1.cornerPair, c.2)

@[simp] theorem parafermionicCoverOpenPair_projection (c : ParafermionicCoverPort) :
    (parafermionicCoverOpenPair c).1 = c.1.openPair := rfl

@[simp] theorem parafermionicCoverClosedPair_projection (c : ParafermionicCoverPort) :
    (parafermionicCoverClosedPair c).1 = c.1.closedPair := rfl

@[simp] theorem parafermionicCoverCornerPair_projection (c : ParafermionicCoverPort) :
    (parafermionicCoverCornerPair c).1 = c.1.cornerPair := rfl

theorem parafermionicCoverOpenPair_vertex (c : ParafermionicCoverPort) :
    parafermionicCoverPortVertex (parafermionicCoverOpenPair c) =
      parafermionicCoverPortOtherVertex c := by
  rcases c with ⟨p, k⟩
  rcases p with ⟨b, tip, side⟩
  cases tip <;>
    simp [parafermionicCoverOpenPair, parafermionicCoverPortVertex,
      parafermionicCoverPortOtherVertex, LatticePort.openPair,
      LatticePort.primalVertex, LatticeBond.endpoint]

theorem parafermionicCoverClosedPair_vertex (c : ParafermionicCoverPort) :
    parafermionicCoverPortVertex (parafermionicCoverClosedPair c) =
      parafermionicCoverPortVertex c := by
  rcases c with ⟨p, k⟩
  simp [parafermionicCoverClosedPair, parafermionicCoverPortVertex,
    LatticePort.closedPair, LatticePort.primalVertex]

theorem parafermionicCoverCornerPair_vertex (c : ParafermionicCoverPort) :
    parafermionicCoverPortVertex (parafermionicCoverCornerPair c) =
      parafermionicCoverPortVertex c := by
  rcases c with ⟨p, k⟩
  simp [parafermionicCoverCornerPair, parafermionicCoverPortVertex,
    LatticePort.cornerPair_primalVertex]

/-- A state on the actual infinite cover graph, with no descent assumption. -/
abbrev ParafermionicCoverConfiguration := parafermionicCoverGraph.edgeSet → Bool

theorem parafermionicCoverPortOtherVertex_openPair (c : ParafermionicCoverPort) :
    parafermionicCoverPortOtherVertex (parafermionicCoverOpenPair c) =
      parafermionicCoverPortVertex c := by
  rcases c with ⟨⟨b, tip, side⟩, k⟩
  cases tip <;>
    simp [parafermionicCoverPortOtherVertex, parafermionicCoverPortVertex,
      parafermionicCoverOpenPair, LatticePort.openPair, LatticePort.primalVertex,
      LatticeBond.endpoint, parafermionicCoverSheetShift]

theorem parafermionicCoverOpenPair_edge_val_eq (c : ParafermionicCoverPort) :
    (parafermionicCoverPortEdge (parafermionicCoverOpenPair c)).val =
      (parafermionicCoverPortEdge c).val := by
  rw [parafermionicCoverPortEdge_eq_incident_pair,
    parafermionicCoverPortEdge_eq_incident_pair,
    parafermionicCoverOpenPair_vertex,
    parafermionicCoverPortOtherVertex_openPair]
  exact Sym2.eq_swap

theorem parafermionicCoverClosedPair_edge_val_eq (c : ParafermionicCoverPort) :
    (parafermionicCoverPortEdge (parafermionicCoverClosedPair c)).val =
      (parafermionicCoverPortEdge c).val := by
  rcases c with ⟨⟨b, tip, side⟩, k⟩
  cases b with
  | mk base axis =>
    cases axis <;> cases tip <;>
      simp [parafermionicCoverPortEdge, parafermionicCoverClosedPair,
        parafermionicCoverPortSourceSheet,
        parafermionicCoverSheetShift, LatticePort.closedPair, LatticeBond.source,
        LatticeBond.target]

@[simp] theorem parafermionicCoverOpenPair_edge_projection (c : ParafermionicCoverPort) :
    Sym2.map Prod.fst (parafermionicCoverPortEdge (parafermionicCoverOpenPair c)).val =
      c.1.bond.toSym2 := by
  rw [parafermionicCoverPortEdge_projection]
  rfl

@[simp] theorem parafermionicCoverClosedPair_edge_projection (c : ParafermionicCoverPort) :
    Sym2.map Prod.fst (parafermionicCoverPortEdge (parafermionicCoverClosedPair c)).val =
      c.1.bond.toSym2 := by
  rw [parafermionicCoverPortEdge_projection]
  rfl

@[simp] theorem parafermionicCoverCornerPair_edge_projection (c : ParafermionicCoverPort) :
    Sym2.map Prod.fst (parafermionicCoverPortEdge (parafermionicCoverCornerPair c)).val =
      c.1.cornerPair.bond.toSym2 := by
  rw [parafermionicCoverPortEdge_projection]
  rfl

theorem parafermionicCoverOpenPair_involutive :
    Function.Involutive parafermionicCoverOpenPair := by
  intro c
  apply Prod.ext
  · exact openPair_involutive c.1
  · change (parafermionicCoverPortOtherVertex (parafermionicCoverOpenPair c)).2 = c.2
    rw [parafermionicCoverPortOtherVertex_openPair]
    rfl

theorem parafermionicCoverClosedPair_involutive :
    Function.Involutive parafermionicCoverClosedPair := by
  intro c
  exact Prod.ext (closedPair_involutive c.1) rfl

theorem parafermionicCoverCornerPair_involutive :
    Function.Involutive parafermionicCoverCornerPair := by
  intro c
  exact Prod.ext (cornerPair_involutive c.1) rfl

theorem parafermionicCoverOpenPair_ne (c : ParafermionicCoverPort) :
    parafermionicCoverOpenPair c ≠ c := by
  intro h
  exact openPair_ne c.1 (congrArg Prod.fst h)

theorem parafermionicCoverClosedPair_ne (c : ParafermionicCoverPort) :
    parafermionicCoverClosedPair c ≠ c := by
  intro h
  exact closedPair_ne c.1 (congrArg Prod.fst h)

theorem parafermionicCoverCornerPair_ne (c : ParafermionicCoverPort) :
    parafermionicCoverCornerPair c ≠ c := by
  intro h
  exact cornerPair_ne c.1 (congrArg Prod.fst h)

/-- State of the actual lifted primal bond incident to this port. -/
def parafermionicCoverPortBondState (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) : Bool := ω (parafermionicCoverPortEdge c)

/-- The actual state-selected lifted medial pairing. -/
def parafermionicCoverLocalPair (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) : ParafermionicCoverPort :=
  if parafermionicCoverPortBondState ω c then parafermionicCoverOpenPair c
  else parafermionicCoverClosedPair c

/-- A one-bond encoding of the state read at this lifted port. This is only a
pointwise projection for the local pairing; it does not assert that cover states
descend to a sheet-independent configuration on the base lattice. -/
def parafermionicCoverPortLocalBaseState (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) (b : LatticeBond) : Bool :=
  if b = c.1.bond then parafermionicCoverPortBondState ω c else false

@[simp] theorem parafermionicCoverPortLocalBaseState_at (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) :
    parafermionicCoverPortLocalBaseState ω c c.1.bond = parafermionicCoverPortBondState ω c := by
  simp [parafermionicCoverPortLocalBaseState]

theorem parafermionicCoverLocalPair_projection (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) :
    (parafermionicCoverLocalPair ω c).1 =
      localPair (parafermionicCoverPortLocalBaseState ω c) c.1 := by
  cases h : parafermionicCoverPortBondState ω c <;>
    simp [parafermionicCoverLocalPair, localPair, h,
      parafermionicCoverPortLocalBaseState]

theorem parafermionicCoverPortBondState_openPair (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) :
    parafermionicCoverPortBondState ω (parafermionicCoverOpenPair c) =
      parafermionicCoverPortBondState ω c := by
  unfold parafermionicCoverPortBondState
  apply congrArg ω
  apply Subtype.ext
  exact parafermionicCoverOpenPair_edge_val_eq c

theorem parafermionicCoverPortBondState_closedPair (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) :
    parafermionicCoverPortBondState ω (parafermionicCoverClosedPair c) =
      parafermionicCoverPortBondState ω c := by
  unfold parafermionicCoverPortBondState
  apply congrArg ω
  apply Subtype.ext
  exact parafermionicCoverClosedPair_edge_val_eq c

theorem parafermionicCoverLocalPair_involutive (ω : ParafermionicCoverConfiguration) :
    Function.Involutive (parafermionicCoverLocalPair ω) := by
  intro c
  cases h : parafermionicCoverPortBondState ω c with
  | false =>
      calc
        parafermionicCoverLocalPair ω (parafermionicCoverLocalPair ω c) =
            parafermionicCoverClosedPair (parafermionicCoverClosedPair c) := by
              simp [parafermionicCoverLocalPair, h,
                parafermionicCoverPortBondState_closedPair]
        _ = c := parafermionicCoverClosedPair_involutive c
  | true =>
      calc
        parafermionicCoverLocalPair ω (parafermionicCoverLocalPair ω c) =
            parafermionicCoverOpenPair (parafermionicCoverOpenPair c) := by
              simp [parafermionicCoverLocalPair, h,
                parafermionicCoverPortBondState_openPair]
        _ = c := parafermionicCoverOpenPair_involutive c

theorem parafermionicCoverLocalPair_edge_val_eq (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) :
    (parafermionicCoverPortEdge (parafermionicCoverLocalPair ω c)).val =
      (parafermionicCoverPortEdge c).val := by
  cases h : parafermionicCoverPortBondState ω c
  · rw [parafermionicCoverLocalPair, ite_eq_right (by simp [h])]
    exact parafermionicCoverClosedPair_edge_val_eq c
  · rw [parafermionicCoverLocalPair, ite_eq_left (by simp [h])]
    exact parafermionicCoverOpenPair_edge_val_eq c

theorem parafermionicCoverLocalPair_ne (ω : ParafermionicCoverConfiguration)
    (c : ParafermionicCoverPort) : parafermionicCoverLocalPair ω c ≠ c := by
  by_cases h : parafermionicCoverPortBondState ω c
  · rw [parafermionicCoverLocalPair, ite_eq_left h]
    exact parafermionicCoverOpenPair_ne c
  · rw [parafermionicCoverLocalPair, ite_eq_right h]
    exact parafermionicCoverClosedPair_ne c

end PottsContinuity.Thm4.Medial
