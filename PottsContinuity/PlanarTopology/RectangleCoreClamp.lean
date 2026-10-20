module

public import PottsContinuity.PlanarTopology.IntegerCoreClamp
public import PottsContinuity.PlanarTopology.RectangleDualGraphBridge
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial

/-- Project integer face bases onto the nonempty interior face box of a
positive-sided primal rectangle. No missing-side case is filled by a default. -/
def rectangleCoreClamp (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (z : LatticeVertex) : LatticeVertex :=
  (integerIntervalClamp a.1 (a.1+(w : ℤ)-1) (by omega) z.1,
    integerIntervalClamp a.2 (a.2+(h : ℤ)-1) (by omega) z.2)

theorem rectangleCoreClamp_bounds (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (z : LatticeVertex) :
    a.1 ≤ (rectangleCoreClamp a w h hw hh z).1 ∧
    (rectangleCoreClamp a w h hw hh z).1 < a.1+(w : ℤ) ∧
    a.2 ≤ (rectangleCoreClamp a w h hw hh z).2 ∧
    (rectangleCoreClamp a w h hw hh z).2 < a.2+(h : ℤ) := by
  have hx := integerIntervalClamp_mem a.1 (a.1+(w : ℤ)-1) (by omega) z.1
  have hy := integerIntervalClamp_mem a.2 (a.2+(h : ℤ)-1) (by omega) z.2
  dsimp only [rectangleCoreClamp,Prod.fst,Prod.snd]
  exact ⟨hx.1,by omega,hy.1,by omega⟩

/-- On the true dual bond of an original rectangle bond, projection either
contracts that bond or fixes both of its original face-base endpoints. -/
theorem rectangleCoreClamp_face_pair (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) :
    rectangleCoreClamp a w h hw hh (b.faceBase false) =
        rectangleCoreClamp a w h hw hh (b.faceBase true) ∨
      (rectangleCoreClamp a w h hw hh (b.faceBase false) = b.faceBase false ∧
        rectangleCoreClamp a w h hw hh (b.faceBase true) = b.faceBase true) := by
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis
  · have hS := (mem_latticeRectangle a (x,y) w h).mp hs
    have hT := (mem_latticeRectangle a (x+1,y) w h).mp ht
    have hcx := integerIntervalClamp_fixed a.1 (a.1+(w : ℤ)-1) (by omega) x (by omega)
    have hcy := integerIntervalClamp_consecutive a.2 (a.2+(h : ℤ)-1) (by omega) y (by omega)
    rcases hcy with hcy | ⟨hcy0,hcy1⟩
    · left
      apply Prod.ext
      · rfl
      · exact hcy
    · right
      constructor <;> apply Prod.ext
      · exact hcx
      · exact hcy0
      · exact hcx
      · exact hcy1
  · have hS := (mem_latticeRectangle a (x,y) w h).mp hs
    have hT := (mem_latticeRectangle a (x,y+1) w h).mp ht
    have hcy := integerIntervalClamp_fixed a.2 (a.2+(h : ℤ)-1) (by omega) y (by omega)
    have hcx := integerIntervalClamp_consecutive a.1 (a.1+(w : ℤ)-1) (by omega) x (by omega)
    rcases hcx with hcx | ⟨hcx0,hcx1⟩
    · left
      apply Prod.ext
      · exact hcx
      · rfl
    · right
      constructor <;> apply Prod.ext
      · exact hcx0
      · exact hcy
      · exact hcx1
      · exact hcy

end PottsContinuity.PlanarTopology
