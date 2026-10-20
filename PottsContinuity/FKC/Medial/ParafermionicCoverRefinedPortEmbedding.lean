-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedPortEmbedding.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverPorts
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open LatticeAxis

/-- A small signed offset for the primal direction from the port endpoint toward
its other endpoint. -/
def refinedPortEdgeDirection (p : LatticePort) : LatticeVertex :=
  match p.bond.axis, p.tip with
  | horizontal, false => (1, 0)
  | horizontal, true => (-1, 0)
  | vertical, false => (0, 1)
  | vertical, true => (0, -1)

/-- A small signed offset toward the cell adjacent to the port. -/
def refinedPortCellNormal (p : LatticePort) : LatticeVertex :=
  match p.bond.axis, p.side with
  | horizontal, false => (0, -1)
  | horizontal, true => (0, 1)
  | vertical, false => (-1, 0)
  | vertical, true => (1, 0)

def refinedPortLayerRadius (layer : Bool) : ℤ :=
  if layer then 3 else 4

def refinedPortPosition (p : LatticePort) (layer : Bool) : LatticeVertex :=
  let v := p.primalVertex
  let e := refinedPortEdgeDirection p
  let n := refinedPortCellNormal p
  (9 * v.1 - 4 + refinedPortLayerRadius layer * e.1 + n.1,
   9 * v.2 + 4 + refinedPortLayerRadius layer * e.2 + n.2)

/-- A fine-grid encoding retaining the complete lifted port and layer identity.
The second output coordinate retains the sheet unchanged. -/
def parafermionicCoverRefinedPortEmbedding
    (c : ParafermionicCoverPort × Bool) : LatticeVertex × ℤ :=
  (refinedPortPosition c.1.1 c.2, c.1.2)

@[simp] theorem parafermionicCoverRefinedPortEmbedding_sheet
    (c : ParafermionicCoverPort × Bool) :
    (parafermionicCoverRefinedPortEmbedding c).2 = c.1.2 := rfl

theorem parafermionicCoverRefinedPortEmbedding_injective :
    Function.Injective parafermionicCoverRefinedPortEmbedding := by
  rintro ⟨⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩, layer⟩
    ⟨⟨⟨⟨⟨x', y'⟩, ax'⟩, tip', side'⟩, k'⟩, layer'⟩ h
  have hpos := congrArg Prod.fst h
  have hsheet := congrArg Prod.snd h
  simp [parafermionicCoverRefinedPortEmbedding] at hsheet
  subst k'
  simp only [parafermionicCoverRefinedPortEmbedding, refinedPortPosition,
    refinedPortEdgeDirection, refinedPortCellNormal, refinedPortLayerRadius,
    LatticePort.primalVertex, LatticeBond.endpoint, LatticeBond.source,
    LatticeBond.target, Prod.mk.injEq] at hpos
  rcases hpos with ⟨hx, hy⟩
  simp only [Prod.mk.injEq]
  cases ax <;> cases ax' <;> cases tip <;> cases tip' <;>
    cases side <;> cases side' <;> cases layer <;> cases layer' <;>
    simp at hx hy ⊢ <;> omega

theorem parafermionicCoverRefinedPortEmbedding_horizontal
    (x y : ℤ) (tip side layer : Bool) (k : ℤ) :
    parafermionicCoverRefinedPortEmbedding
      (((⟨⟨(x, y), horizontal⟩, tip, side⟩ : LatticePort), k), layer) =
      ((9 * x - 4 +
          (if tip then 9 - (if layer then (3 : ℤ) else 4)
            else if layer then 3 else 4),
        9 * y + 4 + (if side then (1 : ℤ) else -1)), k) := by
  cases tip <;> cases side <;> cases layer <;>
    simp [parafermionicCoverRefinedPortEmbedding, refinedPortPosition,
      refinedPortEdgeDirection, refinedPortCellNormal, refinedPortLayerRadius,
      LatticePort.primalVertex, LatticeBond.endpoint, LatticeBond.source,
      LatticeBond.target] <;> ring

theorem parafermionicCoverRefinedPortEmbedding_vertical
    (x y : ℤ) (tip side layer : Bool) (k : ℤ) :
    parafermionicCoverRefinedPortEmbedding
      (((⟨⟨(x, y), vertical⟩, tip, side⟩ : LatticePort), k), layer) =
      ((9 * x - 4 + (if side then (1 : ℤ) else -1),
        9 * y + 4 +
          (if tip then 9 - (if layer then (3 : ℤ) else 4)
            else if layer then 3 else 4)), k) := by
  cases tip <;> cases side <;> cases layer <;>
    simp [parafermionicCoverRefinedPortEmbedding, refinedPortPosition,
      refinedPortEdgeDirection, refinedPortCellNormal, refinedPortLayerRadius,
      LatticePort.primalVertex, LatticeBond.endpoint, LatticeBond.source,
      LatticeBond.target] <;> ring

end PottsContinuity.FKC.Medial
