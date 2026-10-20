module

public import PottsContinuity.BD12.BoxRadiusData
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Prod.Lex
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Canonical endpoint ordering of original box edges, by lexicographic order
of the actual integer coordinates. No orientation witness is selected. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section

local instance radiusBoxLexOrder (c : LatticeVertex) (n : ℕ) :
    LinearOrder (latticeBox c n : Set LatticeVertex) :=
  LinearOrder.lift' (fun v : (latticeBox c n : Set LatticeVertex) => toLex v.val) (by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : Lex LatticeVertex => ofLex z) h)

/-- Lexicographically first endpoint of the actual unordered edge. -/
def radiusBoxEdgeFirst (c : LatticeVertex) (n : ℕ)
    (e : (finiteLatticeGraph (latticeBox c n)).edgeSet) : (latticeBox c n : Set LatticeVertex) :=
  (Sym2.sortEquiv e.val).val.1

/-- Lexicographically last endpoint of the actual unordered edge. -/
def radiusBoxEdgeSecond (c : LatticeVertex) (n : ℕ)
    (e : (finiteLatticeGraph (latticeBox c n)).edgeSet) : (latticeBox c n : Set LatticeVertex) :=
  (Sym2.sortEquiv e.val).val.2

theorem radiusBoxEdge_endpoints (c : LatticeVertex) (n : ℕ)
    (e : (finiteLatticeGraph (latticeBox c n)).edgeSet) :
    e.val = s(radiusBoxEdgeFirst c n e, radiusBoxEdgeSecond c n e) :=
  (Sym2.sortEquiv.symm_apply_apply e.val).symm

end
end PottsContinuity.BD12
