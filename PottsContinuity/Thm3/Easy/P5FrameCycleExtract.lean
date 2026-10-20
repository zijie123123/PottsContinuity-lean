module

public import PottsContinuity.Thm3.Easy.P5FrameClosedWalk
public import PottsContinuity.Thm3.Easy.P5ClosedWalkCycle

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

/-- The four frame crossings contain a simple closed open walk whose image
has nonzero signed ray index at the origin. -/
theorem p5_frame_crossings_yield_simpleClosedWalk_rayIndex_ne_zero
    (n m : ℕ) (hnm : n + 2 ≤ 6 * m)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (hTop : p5FrameCrossing n m 0 ω)
    (hBottom : p5FrameCrossing n m 1 ω)
    (hRight : p5FrameCrossing n m 2 ω)
    (hLeft : p5FrameCrossing n m 3 ω) :
    ∃ z : (p5aAnnulusVertexSet n : Set (ℤ × ℤ)),
      ∃ q : (rcOpenGraph (p5aAnnulusVertexSet n) ω).Walk z z,
        q.IsCycle ∧
          rayIndex (0, 0)
            (q.map (p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω)) ≠ 0 := by
  obtain ⟨z, p, hpos, hidx⟩ :=
    p5_frame_crossings_yield_closedWalk_rayIndex_eq_neg_one n m hnm ω
      hTop hBottom hRight hLeft
  have hidxne : rayIndex (0, 0)
      (p.map (p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω)) ≠ 0 := by
    rw [hidx]
    norm_num
  obtain ⟨z, q, hcycle, hqidx, _⟩ :=
    closedWalk_exists_simpleNonzeroRayIndex
      (p5ClosedWalkToSquareLattice (p5aAnnulusVertexSet n) ω) (0, 0) p hidxne
  exact ⟨z, q, hcycle, hqidx⟩

end PottsContinuity.Thm3.Easy
