-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/LatticeWalkInterpolation.lean`, with
-- module and namespace relocated and declarations not used here removed.
/- That file was itself adapted from FKconvergence, an earlier formalization by the same author that is not publicly accessible, file `Curves/LatticeWalkInterpolation.lean`.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsContinuity.PD.Duality.LatticeEmbedding
public import Mathlib.Topology.Path
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace PottsContinuity.PD.FK.Curves

open Set

noncomputable section

/-- Straight-segment interpolation of an actual nearest-neighbor lattice walk.
The recursive concatenation retains the walk order and all repeated visits. -/
def latticeWalkPath (δ : PositiveMesh) : {u v : LatticeVertex} →
    squareLattice.Walk u v → Path (latticeEmbed δ u) (latticeEmbed δ v)
  | _, _, .nil => Path.refl _
  | u, _, .cons (v := v) _h p =>
      (Path.segment (latticeEmbed δ u) (latticeEmbed δ v)).trans
        (latticeWalkPath δ p)

/-- Every point of the interpolated path belongs to a segment joining two
vertices visited by the original walk. -/
theorem latticeWalkPath_range_subset_segments (δ : PositiveMesh)
    {u v : LatticeVertex} (p : squareLattice.Walk u v) :
    Set.range (latticeWalkPath δ p) ⊆
      {z | ∃ x y : LatticeVertex, x ∈ p.support ∧ y ∈ p.support ∧
        (x = y ∨ squareLattice.Adj x y) ∧
        z ∈ Set.range (Path.segment (latticeEmbed δ x) (latticeEmbed δ y))} := by
  induction p with
  | @nil u0 =>
      intro z hz
      rcases hz with ⟨t, rfl⟩
      refine ⟨u0, u0, by simp, by simp, Or.inl rfl, ?_⟩
      rw [Path.range_segment]
      exact left_mem_segment ℝ _ _
  | @cons u v w h p ih =>
      intro z hz
      change z ∈ Set.range
        ((Path.segment (latticeEmbed δ u) (latticeEmbed δ v)).trans
          (latticeWalkPath δ p)) at hz
      rw [Path.trans_range] at hz
      rcases hz with hfirst | htail
      · exact ⟨u, v, by simp, by
          exact List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support p)),
          Or.inr h, hfirst⟩
      · obtain ⟨x, y, hx, hy, hxy, hseg⟩ := ih htail
        exact ⟨x, y, by simp [hx], by simp [hy], hxy, hseg⟩

end
end PottsContinuity.PD.FK.Curves
