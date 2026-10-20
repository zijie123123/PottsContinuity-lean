/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutTerminalLabels.lean`.
Adaptation: namespace relocation; canonical unique incoming seed replaces arbitrary choice;
prove orbit uniqueness before selecting its three uniquely specified ports.
-/
module

public import PottsContinuity.Thm4.EdgeCutSourceSinkCount
public import PottsContinuity.Thm4.CanonicalSeed
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

/-- The canonical incoming source-tip port of the actual queried edge. -/
def parafermionicCoverFiniteEdgeCutSeedPort (n : ℕ) (_hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) : ParafermionicCoverFinitePort n :=
  canonicalIncomingPort n e

theorem parafermionicCoverFiniteEdgeCutSeedPort_spec (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSeedPort n hn e ∈
        parafermionicCoverFiniteEdgeCutQueriedPorts n e ∧
      parafermionicCoverIncomingPrimalLeft
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1 = true := by
  classical
  have h := canonicalIncomingPort_spec n e
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, h.2.2⟩

structure ParafermionicCoverFiniteEdgeCutSeedOrbit (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) where
  openPort : ParafermionicCoverFinitePort n
  closedPort : ParafermionicCoverFinitePort n
  openClosedPort : ParafermionicCoverFinitePort n
  open_eq : openPort.1 = parafermionicCoverOpenPair
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1
  closed_eq : closedPort.1 = parafermionicCoverClosedPair
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1
  openClosed_eq : openClosedPort.1 = parafermionicCoverOpenPair
    (parafermionicCoverClosedPair (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1)
  open_queried : openPort ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e
  closed_queried : closedPort ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e
  openClosed_queried : openClosedPort ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e
  open_incoming_false : parafermionicCoverIncomingPrimalLeft openPort.1 = false
  closed_incoming_false : parafermionicCoverIncomingPrimalLeft closedPort.1 = false
  openClosed_incoming_true : parafermionicCoverIncomingPrimalLeft openClosedPort.1 = true
  distinct_seed_open : parafermionicCoverFiniteEdgeCutSeedPort n hn e ≠ openPort
  distinct_seed_closed : parafermionicCoverFiniteEdgeCutSeedPort n hn e ≠ closedPort
  distinct_seed_openClosed : parafermionicCoverFiniteEdgeCutSeedPort n hn e ≠ openClosedPort
  distinct_open_closed : openPort ≠ closedPort
  distinct_open_openClosed : openPort ≠ openClosedPort
  distinct_closed_openClosed : closedPort ≠ openClosedPort

theorem parafermionicCoverFiniteEdgeCutSeedOrbit_nonempty (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Nonempty (ParafermionicCoverFiniteEdgeCutSeedOrbit n hn e) := by
  classical
  let seed := parafermionicCoverFiniteEdgeCutSeedPort n hn e
  have hseed := parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e
  have hseedEdge : parafermionicCoverPortEdge seed.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    simpa [seed, parafermionicCoverFiniteEdgeCutQueriedPorts] using hseed.1
  have hbox : ∀ v ∈ (parafermionicCoverPortEdge seed.1).1,
      v ∈ parafermionicCoverBoxVertices n := by
    intro v hv
    rw [hseedEdge] at hv
    exact parafermionicCoverFiniteEdgeEmbedding_endpoints_mem n e v hv
  obtain ⟨c₀, c₁, c₂, c₃, hc₀, hc₁, hc₂, hc₃⟩ :=
    parafermionicCoverPort_four_mem_finite n seed.1 hbox
  have hquery (d : ParafermionicCoverFinitePort n)
      (hd : parafermionicCoverPortEdge d.1 = parafermionicCoverFiniteEdgeEmbedding n e) :
      d ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e := by
    simp only [parafermionicCoverFiniteEdgeCutQueriedPorts, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hd
  have hc1edge : parafermionicCoverPortEdge c₁.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    apply Subtype.ext
    calc
      (parafermionicCoverPortEdge c₁.1).val = (parafermionicCoverPortEdge
          (parafermionicCoverOpenPair seed.1)).val := congrArg (fun d =>
            (parafermionicCoverPortEdge d).val) hc₁
      _ = (parafermionicCoverPortEdge seed.1).val := parafermionicCoverOpenPair_edge_val_eq _
      _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hseedEdge
  have hc2edge : parafermionicCoverPortEdge c₂.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    apply Subtype.ext
    calc
      (parafermionicCoverPortEdge c₂.1).val = (parafermionicCoverPortEdge
          (parafermionicCoverClosedPair seed.1)).val := congrArg (fun d =>
            (parafermionicCoverPortEdge d).val) hc₂
      _ = (parafermionicCoverPortEdge seed.1).val := parafermionicCoverClosedPair_edge_val_eq _
      _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hseedEdge
  have hc3edge : parafermionicCoverPortEdge c₃.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    apply Subtype.ext
    calc
      (parafermionicCoverPortEdge c₃.1).val = (parafermionicCoverPortEdge
          (parafermionicCoverOpenPair (parafermionicCoverClosedPair seed.1))).val :=
            congrArg (fun d => (parafermionicCoverPortEdge d).val) hc₃
      _ = (parafermionicCoverPortEdge (parafermionicCoverClosedPair seed.1)).val :=
            parafermionicCoverOpenPair_edge_val_eq _
      _ = (parafermionicCoverPortEdge seed.1).val := parafermionicCoverClosedPair_edge_val_eq _
      _ = (parafermionicCoverFiniteEdgeEmbedding n e).val := congrArg Subtype.val hseedEdge
  have hseedFlag : parafermionicCoverIncomingPrimalLeft seed.1 = true := by
    simpa [seed] using hseed.2
  have hflags1 : parafermionicCoverIncomingPrimalLeft c₁.1 = false := by
    rw [hc₁, parafermionicCoverIncomingPrimalLeft_openPair, hseedFlag]
    rfl
  have hflags2 : parafermionicCoverIncomingPrimalLeft c₂.1 = false := by
    rw [hc₂, parafermionicCoverIncomingPrimalLeft_closedPair, hseedFlag]
    rfl
  have hflags3 : parafermionicCoverIncomingPrimalLeft c₃.1 = true := by
    rw [hc₃, parafermionicCoverIncomingPrimalLeft_openPair,
      parafermionicCoverIncomingPrimalLeft_closedPair, hseedFlag]
    rfl
  have hpair := parafermionicCoverPort_four_pairwise_ne seed.1
  have hd01 : seed ≠ c₁ := by
    intro h
    have hr := congrArg Subtype.val h
    rw [hc₁] at hr
    exact hpair.1 hr.symm
  have hd02 : seed ≠ c₂ := by
    intro h
    have hr := congrArg Subtype.val h
    rw [hc₂] at hr
    exact hpair.2.1 hr.symm
  have hd03 : seed ≠ c₃ := by
    intro h
    have hr := congrArg Subtype.val h
    rw [hc₃] at hr
    exact hpair.2.2.1 hr.symm
  have hd12 : c₁ ≠ c₂ := by
    intro h
    have hr := congrArg Subtype.val h
    rw [hc₁, hc₂] at hr
    exact hpair.2.2.2.1 hr
  have hd13 : c₁ ≠ c₃ := by
    intro h
    have hr := congrArg Subtype.val h
    rw [hc₁, hc₃] at hr
    exact hpair.2.2.2.2.1 hr.symm
  have hd23 : c₂ ≠ c₃ := by
    intro h
    have hr := congrArg Subtype.val h
    rw [hc₂, hc₃] at hr
    exact hpair.2.2.2.2.2 hr.symm
  exact ⟨{
    openPort := c₁
    closedPort := c₂
    openClosedPort := c₃
    open_eq := hc₁
    closed_eq := hc₂
    openClosed_eq := hc₃
    open_queried := hquery c₁ hc1edge
    closed_queried := hquery c₂ hc2edge
    openClosed_queried := hquery c₃ hc3edge
    open_incoming_false := hflags1
    closed_incoming_false := hflags2
    openClosed_incoming_true := hflags3
    distinct_seed_open := hd01
    distinct_seed_closed := hd02
    distinct_seed_openClosed := hd03
    distinct_open_closed := hd12
    distinct_open_openClosed := hd13
    distinct_closed_openClosed := hd23
  }⟩

/-- The three orbit ports are uniquely specified by the seed and pairing maps. -/
theorem parafermionicCoverFiniteEdgeCutSeedOrbit_existsUnique (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ∃! _o : ParafermionicCoverFiniteEdgeCutSeedOrbit n hn e, True := by
  obtain ⟨o⟩ := parafermionicCoverFiniteEdgeCutSeedOrbit_nonempty n hn e
  refine ⟨o, trivial, ?_⟩
  intro p _
  have ho : p.openPort = o.openPort := Subtype.ext (p.open_eq.trans o.open_eq.symm)
  have hc : p.closedPort = o.closedPort := Subtype.ext (p.closed_eq.trans o.closed_eq.symm)
  have hoc : p.openClosedPort = o.openClosedPort :=
    Subtype.ext (p.openClosed_eq.trans o.openClosed_eq.symm)
  cases p
  cases o
  cases ho
  cases hc
  cases hoc
  rfl

def parafermionicCoverFiniteEdgeCutSeedOrbit (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSeedOrbit n hn e :=
  Classical.choose (parafermionicCoverFiniteEdgeCutSeedOrbit_existsUnique n hn e)

local instance edgeCutLabelSourcesFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutSources n hn e) := by
  classical exact Fintype.ofFinite _

local instance edgeCutLabelSinksFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutSinks n hn e) := by
  classical exact Fintype.ofFinite _

local instance edgeCutLabelTerminalsFintype (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fintype (ParafermionicCoverFiniteEdgeCutTerminal n hn e) := by
  classical exact Fintype.ofFinite _

def parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ parafermionicCoverFiniteEdgeCutQueriedPorts n e) :
    ParafermionicCoverFiniteEdgeCutTerminal n hn e :=
  ⟨(c, false), Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)⟩

def parafermionicCoverFiniteEdgeCutSourceCorner (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSources n hn e := by
  refine ⟨⟨(parafermionicCoverFiniteOriginCornerPort n hn, true), ?_⟩, ?_⟩
  · exact Finset.mem_union_right _ (by
      simp [parafermionicCoverFiniteEdgeCutCornerTerminals])
  · change true = parafermionicCoverIncomingPrimalLeft
      (parafermionicCoverFiniteOriginCornerPort n hn).1
    rw [parafermionicCoverFiniteOriginCornerPort_val]
    exact parafermionicCoverIncomingPrimalLeft_origin

def parafermionicCoverFiniteEdgeCutSourceClosedLabel (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSources n hn e := by
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  refine ⟨parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse n hn e
      o.closedPort o.closed_queried, ?_⟩
  change false = parafermionicCoverIncomingPrimalLeft o.closedPort.1
  exact o.closed_incoming_false.symm

def parafermionicCoverFiniteEdgeCutSourceOpenLabel (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSources n hn e := by
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  refine ⟨parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse n hn e
      o.openPort o.open_queried, ?_⟩
  change false = parafermionicCoverIncomingPrimalLeft o.openPort.1
  exact o.open_incoming_false.symm

def parafermionicCoverFiniteEdgeCutSinkCorner (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSinks n hn e := by
  refine ⟨⟨(parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn), true), ?_⟩, ?_⟩
  · exact Finset.mem_union_right _ (by
      simp [parafermionicCoverFiniteEdgeCutCornerTerminals])
  · change ¬ (true = parafermionicCoverIncomingPrimalLeft
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)).1)
    rw [parafermionicCoverFiniteCornerPairPerm_val,
      parafermionicCoverFiniteOriginCornerPort_val,
      parafermionicCoverIncomingPrimalLeft_cornerPair,
      parafermionicCoverIncomingPrimalLeft_origin]
    decide

def parafermionicCoverFiniteEdgeCutSinkSeedLabel (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSinks n hn e := by
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hseed := parafermionicCoverFiniteEdgeCutSeedPort_spec n hn e
  refine ⟨parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse n hn e
      (parafermionicCoverFiniteEdgeCutSeedPort n hn e) hseed.1, ?_⟩
  change ¬ (false = parafermionicCoverIncomingPrimalLeft
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e).1)
  rw [hseed.2]
  decide

def parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ParafermionicCoverFiniteEdgeCutSinks n hn e := by
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  refine ⟨parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse n hn e
      o.openClosedPort o.openClosed_queried, ?_⟩
  change ¬ (false = parafermionicCoverIncomingPrimalLeft o.openClosedPort.1)
  rw [o.openClosed_incoming_true]
  decide

def parafermionicCoverFiniteEdgeCutSourceLabels (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fin 3 → ParafermionicCoverFiniteEdgeCutSources n hn e := fun i =>
  if _h0 : i.val = 0 then parafermionicCoverFiniteEdgeCutSourceCorner n hn e
  else if _h1 : i.val = 1 then parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e
  else parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e

def parafermionicCoverFiniteEdgeCutSinkLabels (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fin 3 → ParafermionicCoverFiniteEdgeCutSinks n hn e := fun i =>
  if _h0 : i.val = 0 then parafermionicCoverFiniteEdgeCutSinkCorner n hn e
  else if _h1 : i.val = 1 then parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e
  else parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e

@[simp] theorem parafermionicCoverFiniteEdgeCutSourceLabels_zero (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceLabels n hn e 0 =
      parafermionicCoverFiniteEdgeCutSourceCorner n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSourceLabels]

@[simp] theorem parafermionicCoverFiniteEdgeCutSourceLabels_one (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceLabels n hn e 1 =
      parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSourceLabels]

@[simp] theorem parafermionicCoverFiniteEdgeCutSourceLabels_two (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceLabels n hn e 2 =
      parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSourceLabels]

@[simp] theorem parafermionicCoverFiniteEdgeCutSinkLabels_zero (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkLabels n hn e 0 =
      parafermionicCoverFiniteEdgeCutSinkCorner n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSinkLabels]

@[simp] theorem parafermionicCoverFiniteEdgeCutSinkLabels_one (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkLabels n hn e 1 =
      parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSinkLabels]

@[simp] theorem parafermionicCoverFiniteEdgeCutSinkLabels_two (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkLabels n hn e 2 =
      parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e := by
  simp [parafermionicCoverFiniteEdgeCutSinkLabels]

@[simp] private theorem edgeCutSourceCorner_ne_closed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceCorner n hn e ≠
      parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e := by
  intro h
  have hb := congrArg (fun s : ParafermionicCoverFiniteEdgeCutSources n hn e => s.1.1.2) h
  have hfalse : true = false := by
    simp [parafermionicCoverFiniteEdgeCutSourceCorner,
      parafermionicCoverFiniteEdgeCutSourceClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] at hb
  exact Bool.noConfusion hfalse

@[simp] private theorem edgeCutSourceCorner_ne_open (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceCorner n hn e ≠
      parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e := by
  intro h
  have hb := congrArg (fun s : ParafermionicCoverFiniteEdgeCutSources n hn e => s.1.1.2) h
  have hfalse : true = false := by
    simp [parafermionicCoverFiniteEdgeCutSourceCorner,
      parafermionicCoverFiniteEdgeCutSourceOpenLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] at hb
  exact Bool.noConfusion hfalse

@[simp] private theorem edgeCutSourceClosed_ne_open (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e := by
  intro h
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hp := congrArg (fun s : ParafermionicCoverFiniteEdgeCutSources n hn e => s.1.1.1) h
  have hp' : o.closedPort = o.openPort := by
    simpa [o, parafermionicCoverFiniteEdgeCutSourceClosedLabel,
      parafermionicCoverFiniteEdgeCutSourceOpenLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using hp
  exact o.distinct_open_closed hp'.symm

@[simp] private theorem edgeCutSourceClosed_ne_corner (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSourceCorner n hn e :=
  Ne.symm (edgeCutSourceCorner_ne_closed n hn e)

@[simp] private theorem edgeCutSourceOpen_ne_corner (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSourceCorner n hn e :=
  Ne.symm (edgeCutSourceCorner_ne_open n hn e)

@[simp] private theorem edgeCutSourceOpen_ne_closed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSourceOpenLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSourceClosedLabel n hn e :=
  Ne.symm (edgeCutSourceClosed_ne_open n hn e)

@[simp] private theorem edgeCutSinkCorner_ne_seed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkCorner n hn e ≠
      parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e := by
  intro h
  have hb := congrArg (fun s : ParafermionicCoverFiniteEdgeCutSinks n hn e => s.1.1.2) h
  have hfalse : true = false := by
    simp [parafermionicCoverFiniteEdgeCutSinkCorner,
      parafermionicCoverFiniteEdgeCutSinkSeedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] at hb
  exact Bool.noConfusion hfalse

@[simp] private theorem edgeCutSinkCorner_ne_openClosed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkCorner n hn e ≠
      parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e := by
  intro h
  have hb := congrArg (fun s : ParafermionicCoverFiniteEdgeCutSinks n hn e => s.1.1.2) h
  have hfalse : true = false := by
    simp [parafermionicCoverFiniteEdgeCutSinkCorner,
      parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] at hb
  exact Bool.noConfusion hfalse

@[simp] private theorem edgeCutSinkSeed_ne_openClosed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e := by
  intro h
  let o := parafermionicCoverFiniteEdgeCutSeedOrbit n hn e
  have hp := congrArg (fun s : ParafermionicCoverFiniteEdgeCutSinks n hn e => s.1.1.1) h
  have hp' : parafermionicCoverFiniteEdgeCutSeedPort n hn e = o.openClosedPort := by
    simpa [o, parafermionicCoverFiniteEdgeCutSinkSeedLabel,
      parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel,
      parafermionicCoverFiniteEdgeCutTerminalOfQueriedFalse] using hp
  exact o.distinct_seed_openClosed hp'

@[simp] private theorem edgeCutSinkSeed_ne_corner (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSinkCorner n hn e :=
  Ne.symm (edgeCutSinkCorner_ne_seed n hn e)

@[simp] private theorem edgeCutSinkOpenClosed_ne_corner (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSinkCorner n hn e :=
  Ne.symm (edgeCutSinkCorner_ne_openClosed n hn e)

@[simp] private theorem edgeCutSinkOpenClosed_ne_seed (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutSinkOpenClosedLabel n hn e ≠
      parafermionicCoverFiniteEdgeCutSinkSeedLabel n hn e :=
  Ne.symm (edgeCutSinkSeed_ne_openClosed n hn e)

theorem parafermionicCoverFiniteEdgeCutSourceLabels_injective (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Function.Injective (parafermionicCoverFiniteEdgeCutSourceLabels n hn e) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [parafermionicCoverFiniteEdgeCutSourceLabels]

theorem parafermionicCoverFiniteEdgeCutSinkLabels_injective (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    Function.Injective (parafermionicCoverFiniteEdgeCutSinkLabels n hn e) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [parafermionicCoverFiniteEdgeCutSinkLabels]

def parafermionicCoverFiniteEdgeCutSourceLabelsEquiv (n : ℕ)
    (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fin 3 ≃ ParafermionicCoverFiniteEdgeCutSources n hn e := by
  apply Equiv.ofBijective (parafermionicCoverFiniteEdgeCutSourceLabels n hn e)
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨parafermionicCoverFiniteEdgeCutSourceLabels_injective n hn e, ?_⟩
  rw [Fintype.card_fin,
    parafermionicCoverFiniteEdgeCutSources_card n hn
      (∅ : Configuration (ParafermionicAmbientGraph n)) e]

def parafermionicCoverFiniteEdgeCutSinkLabelsEquiv (n : ℕ)
    (hn : 1 ≤ n) (e : (ParafermionicAmbientGraph n).edgeSet) :
    Fin 3 ≃ ParafermionicCoverFiniteEdgeCutSinks n hn e := by
  apply Equiv.ofBijective (parafermionicCoverFiniteEdgeCutSinkLabels n hn e)
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨parafermionicCoverFiniteEdgeCutSinkLabels_injective n hn e, ?_⟩
  rw [Fintype.card_fin,
    parafermionicCoverFiniteEdgeCutSinks_card n hn
      (∅ : Configuration (ParafermionicAmbientGraph n)) e]

end
end PottsContinuity.Thm4
