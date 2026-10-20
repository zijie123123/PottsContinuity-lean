-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Frozen/Defs/PottsHamiltonian.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.Defs.VertexBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# `pottsHamiltonian` from the PottsDiscontinuity formalization

A definition of the formalization of arXiv:1611.09877v2 that is reused here by the adapted
modules of `PottsContinuity/PD/`. It is not part of the statement surface of this repository.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsContinuity.PD

open Classical in
/-- The Potts Hamiltonian `Hⁱ_G(σ) = -∑_{{x,y} ∈ E} 1[σₓ = σ_y] - ∑_{x ∈ ∂V} 1[σₓ = i]`
on the subgraph induced by `V`, spins in `{1, …, q}`, boundary condition `i ∈ {0, …, q}`. -/
noncomputable def pottsHamiltonian (q : ℕ) (V : Finset (ℤ × ℤ)) (i : Fin (q + 1))
    (σ : ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q) : ℝ :=
  -(∑ e : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet,
      if ∀ x ∈ e.1, ∀ y ∈ e.1, σ x = σ y then (1 : ℝ) else 0) -
    ∑ x : ↥(V : Set (ℤ × ℤ)),
      if x.1 ∈ vertexBoundary V ∧ (σ x : ℕ) = (i : ℕ) then (1 : ℝ) else 0

end PottsContinuity.PD
