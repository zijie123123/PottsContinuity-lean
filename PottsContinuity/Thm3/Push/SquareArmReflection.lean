module

public import PottsContinuity.Thm3.Push.IntervalArmRecord
public import PottsContinuity.PD.FK.Isomorphism

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- Reflection of the actual square vertex carrier across its vertical
midline. The formula is meaningful for every square, including N=0. -/
def squareArmReflectionVertex (N : ℕ) (v : RectangleVertex (0,0) N N) :
    RectangleVertex (0,0) N N :=
  ⟨((N : ℤ)-v.val.1,v.val.2),by
    have hv := (mem_latticeRectangle (0,0) v.val N N).mp v.property
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> dsimp at * <;> omega⟩

@[simp] theorem squareArmReflectionVertex_involutive (N : ℕ)
    (v : RectangleVertex (0,0) N N) :
    squareArmReflectionVertex N (squareArmReflectionVertex N v) = v := by
  apply Subtype.ext
  simp [squareArmReflectionVertex]

/-- Original sampled bonds, rather than a dual or shifted carrier, are
transported by this graph isomorphism. -/
def squareArmReflectionIso (N : ℕ) :
    rectangleGraph (0,0) N N ≃g rectangleGraph (0,0) N N where
  toFun := squareArmReflectionVertex N
  invFun := squareArmReflectionVertex N
  left_inv := squareArmReflectionVertex_involutive N
  right_inv := squareArmReflectionVertex_involutive N
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj (squareArmReflectionVertex N u).val
      (squareArmReflectionVertex N v).val ↔ squareLattice.Adj u.val v.val
    change |((N : ℤ)-u.val.1)-((N : ℤ)-v.val.1)| + |u.val.2-v.val.2| = 1 ↔
      |u.val.1-v.val.1| + |u.val.2-v.val.2| = 1
    simp only [abs_eq_max_neg]
    omega

/-- Reflection sends the full source interval and top side to their exact
reflected coordinates; no narrower full-side crossing is substituted. -/
theorem intervalArmEvent_reflection_iff (N : ℕ) (l r : ℤ)
    (A : Configuration (rectangleGraph (0,0) N N)) :
    configurationIso (squareArmReflectionIso N) A ∈
        intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l) ↔
      A ∈ intervalArmEvent N l r := by
  constructor
  · rintro ⟨u,hu,v,hv,huv⟩
    let u' := squareArmReflectionVertex N u
    let v' := squareArmReflectionVertex N v
    refine ⟨u',?_,v',?_,?_⟩
    · change u.val.2=0 ∧ l ≤ (N : ℤ)-u.val.1 ∧ (N : ℤ)-u.val.1 ≤ r
      change u.val.2=0 ∧ (N : ℤ)-r ≤ u.val.1 ∧ u.val.1 ≤ (N : ℤ)-l at hu
      omega
    · exact hv
    · apply (actualConnected_configurationIso (squareArmReflectionIso N) A u' v').mp
      change ActualConnected _ _ (squareArmReflectionVertex N (squareArmReflectionVertex N u))
        (squareArmReflectionVertex N (squareArmReflectionVertex N v))
      simpa only [squareArmReflectionVertex_involutive] using huv
  · rintro ⟨u,hu,v,hv,huv⟩
    refine ⟨squareArmReflectionVertex N u,?_,squareArmReflectionVertex N v,?_,?_⟩
    · change u.val.2=0 ∧ (N : ℤ)-r ≤ (N : ℤ)-u.val.1 ∧
        (N : ℤ)-u.val.1 ≤ (N : ℤ)-l
      change u.val.2=0 ∧ l ≤ u.val.1 ∧ u.val.1 ≤ r at hu
      omega
    · exact hv
    · exact (actualConnected_configurationIso (squareArmReflectionIso N) A u v).mpr huv

end PottsContinuity.Push
