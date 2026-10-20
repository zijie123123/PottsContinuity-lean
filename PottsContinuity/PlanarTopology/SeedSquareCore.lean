module

public import PottsContinuity.PD.Duality.Rectangle
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK

/-- Every seed square based within one in each coordinate contains the same
centered inner box. The marked square has side 2r+2 and the core has radius r. -/
theorem latticeBox_core_subset_nearby_seed (r : ℕ) (a b : LatticeVertex)
    (hx : b.1 ≤ a.1+1 ∧ a.1 ≤ b.1+1) (hy : b.2 ≤ a.2+1 ∧ a.2 ≤ b.2+1) :
    (latticeBox (a.1+(r:ℤ)+1,a.2+(r:ℤ)+1) r : Set LatticeVertex) ⊆
      latticeRectangle b (2*r+2) (2*r+2) := by
  intro z hz
  have hz := (mem_latticeBox (a.1+(r:ℤ)+1,a.2+(r:ℤ)+1) z r).mp hz
  apply (mem_latticeRectangle b z (2*r+2) (2*r+2)).mpr
  dsimp only [Prod.fst,Prod.snd] at hz
  omega

/-- The core is contained in its own square as well, at every nonnegative radius. -/
theorem latticeBox_core_subset_seed (r : ℕ) (a : LatticeVertex) :
    (latticeBox (a.1+(r:ℤ)+1,a.2+(r:ℤ)+1) r : Set LatticeVertex) ⊆
      latticeRectangle a (2*r+2) (2*r+2) :=
  latticeBox_core_subset_nearby_seed r a a ⟨by omega,by omega⟩ ⟨by omega,by omega⟩

end PottsContinuity.PlanarTopology
