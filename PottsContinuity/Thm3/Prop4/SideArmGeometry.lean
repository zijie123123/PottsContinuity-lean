module

public import PottsContinuity.Thm3.RSW.ArmOpen
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.PD.CorrLength.ConnectionEvents

/-!
# Four side arms and outward extension

This implements the actual events used for an adjacent-radius finite-energy
bound. The four sides cover the frozen boundary, including radius zero.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- The four outward unit lattice directions, in cyclic pairs. -/
def sideDirection : Fin 4 → ℤ × ℤ := ![(1,0),(-1,0),(0,1),(0,-1)]

/-- A genuine open arm ending on one prescribed face of the frozen box. -/
def sideArmEvent (n : ℕ) (d : Fin 4) : Set (squareLattice.edgeSet → Bool) :=
  {ω | ∃ z ∈ vertexBoundary (box n),
    z.1*(sideDirection d).1+z.2*(sideDirection d).2 = (n : ℤ) ∧
    (rcInfiniteOpenGraph ω).Reachable (0,0) z}

/-- The same actual arm translated by one outward unit step. -/
def shiftedSideArmEvent (n : ℕ) (d : Fin 4) : Set (squareLattice.edgeSet → Bool) :=
  {ω | ∃ z ∈ vertexBoundary (box n),
    z.1*(sideDirection d).1+z.2*(sideDirection d).2 = (n : ℤ) ∧
    (rcInfiniteOpenGraph ω).Reachable (sideDirection d) (z+sideDirection d)}

/-- Every frozen-boundary arm ends on at least one of the four faces. -/
theorem infiniteArmEvent_subset_sideArms (n : ℕ) :
    RSW.infiniteArmEvent n ⊆ ⋃ d : Fin 4, sideArmEvent n d := by
  rintro ω ⟨z,hz,hconn⟩
  have hb := hz
  rw [Foundations.vertexBoundary_box_eq] at hb
  change max |z.1| |z.2| = (n : ℤ) at hb
  have hs : z.1 = n ∨ z.1 = -(n : ℤ) ∨ z.2 = n ∨ z.2 = -(n : ℤ) := by
    simp only [abs_eq_max_neg] at hb
    omega
  rcases hs with h | h | h | h
  · exact Set.mem_iUnion.mpr ⟨0,z,hz,by simpa [sideDirection] using h,hconn⟩
  · exact Set.mem_iUnion.mpr ⟨1,z,hz,by simp [sideDirection,h],hconn⟩
  · exact Set.mem_iUnion.mpr ⟨2,z,hz,by simpa [sideDirection] using h,hconn⟩
  · exact Set.mem_iUnion.mpr ⟨3,z,hz,by simp [sideDirection,h],hconn⟩

/-- A point on the selected face moves to the next frozen boundary. -/
theorem shiftedSide_mem_nextBoundary (n : ℕ) (d : Fin 4) (z : ℤ × ℤ)
    (hz : z ∈ vertexBoundary (box n))
    (hdot : z.1*(sideDirection d).1+z.2*(sideDirection d).2 = (n : ℤ)) :
    z+sideDirection d ∈ vertexBoundary (box (n+1)) := by
  rw [Foundations.vertexBoundary_box_eq] at hz ⊢
  change max |z.1| |z.2| = (n : ℤ) at hz
  fin_cases d <;> simp [sideDirection] at hdot ⊢ <;>
    simp only [abs_eq_max_neg] at hz ⊢ <;> omega

/-- Translated side-arm events are open as well. -/
theorem shiftedSideArmEvent_isOpen (n : ℕ) (d : Fin 4) : IsOpen (shiftedSideArmEvent n d) := by
  have heq : shiftedSideArmEvent n d = ⋃ z ∈ vertexBoundary (box n),
      ⋃ (_h : z.1*(sideDirection d).1+z.2*(sideDirection d).2 = (n : ℤ)),
      {ω | (rcInfiniteOpenGraph ω).Reachable (sideDirection d) (z+sideDirection d)} := by
    ext ω; simp [shiftedSideArmEvent, and_left_comm]
  rw [heq]
  exact isOpen_iUnion fun z => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    RSW.infinite_connection_isOpen _ _

end PottsContinuity.Thm3.Prop4
