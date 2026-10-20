module

public import PottsContinuity.DualityExt.PositiveAnnulusDualShell
public import PottsContinuity.DualityExt.PositiveConnectedBoundaryPartition
public import PottsContinuity.DualityExt.PositiveEndpointDualSubgraphLaw
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.PD.RCInfinite.OpeningPaths
public import PottsContinuity.PD.RCInfinite.BoxConnector
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial

noncomputable section

/-- Vertices in the hole and vertices joined to the hole by one lattice edge. -/
def annulusHostPrimalInnerClass (N : ℕ) :
    Set (RectangleVertex (annulusHostAnchor N) (4 * N) (4 * N)) :=
  {v | v.1 ∈ latticeBox (0, 0) (N - 1) ∨
    ∃ u, u ∈ latticeBox (0, 0) (N - 1) ∧
      PottsContinuity.PD.FK.squareLattice.Adj u v.1}

/-- The outer class is the host rectangle's vertex boundary. -/
def annulusHostPrimalOuterClass (N : ℕ) :
    Set (RectangleVertex (annulusHostAnchor N) (4 * N) (4 * N)) :=
  {v | v.1 ∈ vertexBoundary
    (latticeRectangle (annulusHostAnchor N) (4 * N) (4 * N))}

theorem annulusHostPrimalInnerOuter_disjoint (N : ℕ) (hN : 1 ≤ N) :
    Disjoint (annulusHostPrimalInnerClass N) (annulusHostPrimalOuterClass N) := by
  rw [Set.disjoint_left]
  intro z hzInner hzOuter
  have hzSmall : z.1 ∈ latticeBox (0, 0) N := by
    rcases hzInner with hzbox | ⟨u, hu, hadj⟩
    · exact PottsContinuity.PD.FK.latticeBox_mono (0, 0)
        (Nat.sub_le N 1) hzbox
    · have hu' := (PottsContinuity.PD.FK.mem_latticeBox
        (0, 0) u (N - 1)).mp hu
      have hadj' :=
        (PottsContinuity.PD.FK.squareLattice_adj_iff u z.1).mp hadj
      rw [mem_latticeBox]
      rcases hu' with ⟨⟨hux₁, hux₂⟩, ⟨huy₁, huy₂⟩⟩
      rcases hadj' with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
        constructor <;> constructor <;> omega
  have hboundary := hzOuter
  change z.1 ∈ vertexBoundary
    (latticeRectangle (annulusHostAnchor N) (4 * N) (4 * N)) at hboundary
  rw [PottsContinuity.PD.vertexBoundary] at hboundary
  rcases hboundary with ⟨_, y, hadj, hyout⟩
  have hz' := (PottsContinuity.PD.FK.mem_latticeBox
    (0, 0) z.1 N).mp hzSmall
  have hyRect : y ∈ latticeRectangle
      (annulusHostAnchor N) (4 * N) (4 * N) := by
    rw [mem_latticeRectangle]
    simp only [annulusHostAnchor]
    have hadj' :=
      (PottsContinuity.PD.FK.squareLattice_adj_iff z.1 y).mp hadj
    rcases hz' with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
    rcases hadj' with ⟨h | h, hyz⟩ | ⟨hxz, h | h⟩ <;>
      constructor <;> constructor <;> omega
  exact hyout hyRect

end
end PottsContinuity.DualityExt
