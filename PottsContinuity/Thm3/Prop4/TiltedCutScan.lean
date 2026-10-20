module

public import PottsContinuity.Thm3.Prop4.TiltedCutSeparation
public import PottsContinuity.FKC.FiniteFK.FirstClosedBlockScan
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

/-!
# A genuine stopping exploration of tilted cuts

The scan algorithm is reused from FKC's parameter-independent combinatorics.
Its FK record law is the stopping-set DMP of `Exploration.FiniteStoppingSetDMP`
at arbitrary interior p
and every q≥1. There is no selector-stability premise left in this instance.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK

noncomputable section

local instance tiltedScanEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance tiltedScanEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Scan the specified finite ordered list of actual column cuts, stopping at
the first completely closed cut and retaining every tested original edge. -/
def tiltedCutScan (n M : ℕ) (t : ℝ) (c : ℕ → ℤ) (K : ℕ)
    (A : Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))) :
    Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) × Option ℕ :=
  FKC.FiniteFK.firstClosedBlockScan (fun i => tiltedWindowCutEdges n M t (c i)) A (List.range K)

/-- Agreement on the actual tested states fixes the entire scan result. -/
theorem tiltedCutScan_eq_of_agree (n M : ℕ) (t : ℝ) (c : ℕ → ℤ) (K : ℕ)
    (A B : Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (h : B ∩ (tiltedCutScan n M t c K A).1 = A ∩ (tiltedCutScan n M t c K A).1) :
    tiltedCutScan n M t c K B = tiltedCutScan n M t c K A :=
  FKC.FiniteFK.firstClosedBlockScan_eq_of_agree _ A B _ h

/-- A successful scan supplies an actual closed cut at a tested column. -/
theorem tiltedCutScan_hit (n M : ℕ) (t : ℝ) (c : ℕ → ℤ) (K : ℕ)
    (A : Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (i : ℕ) (hi : (tiltedCutScan n M t c K A).2 = some i) :
    i < K ∧ Disjoint A (tiltedWindowCutEdges n M t (c i)) := by
  have h := FKC.FiniteFK.firstClosedBlockScan_hit
    (fun j => tiltedWindowCutEdges n M t (c j)) A (List.range K) i hi
  exact ⟨List.mem_range.mp h.1,h.2⟩

/-- The literal failed scan event is the previously bounded all-cuts-fail event. -/
theorem tiltedCutScan_none_event (n M : ℕ) (t : ℝ) (c : ℕ → ℤ) (K : ℕ) :
    {A | (tiltedCutScan n M t c K A).2 = none} =
      closedCutFailure _ (fun i => tiltedWindowCutEdges n M t (c i)) K := by
  ext A
  exact (FKC.FiniteFK.firstClosedBlockScan_none_iff _ A (List.range K)).trans
    (by simp only [List.mem_range]; rfl)

end

end PottsContinuity.Thm3.Prop4
