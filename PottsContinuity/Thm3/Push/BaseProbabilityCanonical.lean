module

public import PottsContinuity.Thm3.Push.FiniteRectangleEventBridge
public import PottsContinuity.Thm3.Push.TopWiredCanonicalRectangle

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- The EXACT base crossing probability `RSW.selfDualTopWiredCrossingProbability` at n=3*s is
the canonical reference
probability used by the proved geometric product. Both domain and shorter
crossing target, including every lattice floor, are identified. -/
theorem selfDual_base_probability_eq_canonical (q : Set.Ici (1 : ℝ))
    (k : ℝ) (s : ℕ) (hk : 0 ≤ k) :
    let a : LatticeVertex := (-⌊k*(3*s : ℕ)⌋,0)
    let w := (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat
    RSW.selfDualTopWiredCrossingProbability q k (4/3) (3*s) =
    (measure (rectangleGraph a w (4*s)) (RSW.selfDualParameters q)
      (BoundaryCondition.wired {v : RectangleVertex a w (4*s) |
        v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(4*s : ℕ)})
      (DualityExt.rectangleInnerHorizontalCrossingEvent
        (rectangle_height_subset a w (3*s) (4*s) (by omega)))).toReal := by
  let a : LatticeVertex := (-⌊k*(3*s : ℕ)⌋,0)
  let w := (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat
  let P (V : Finset LatticeVertex) : ℝ :=
    RSW.finiteBoundaryEventProbability V (RSW.selfDualParameters q)
      (BoundaryCondition.wired {v | v.val.1= -⌊k*(3*s : ℕ)⌋ ∨
        v.val.1=⌊k*(3*s : ℕ)⌋ ∨ v.val.2=((4*s : ℕ) : ℤ)})
      (PottsContinuity.horizontalCrossing V (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s))
  have hprob : P (PD.FK.latticeRectangle a w (4*s))=P (RSW.topWiredRectangle k (4/3) (3*s)) :=
    congrArg P (topWiredRectangle_base_three_eq_canonical k s hk)
  have hsource : RSW.selfDualTopWiredCrossingProbability q k (4/3) (3*s) =
      P (RSW.topWiredRectangle k (4/3) (3*s)) := by
    unfold RSW.selfDualTopWiredCrossingProbability RSW.topWiredRectangleBoundary
    rw [floor_four_thirds_mul_three]
    rfl
  have hcanonical := canonical_rectangle_crossing_probability a w (4*s) (3*s) (by omega)
    (RSW.selfDualParameters q)
  have hright : a.1+(w : ℤ)=⌊k*(3*s : ℕ)⌋ := topWired_canonical_right_coordinate k (3*s) hk
  have hright' : -⌊k*(3*s : ℕ)⌋+(w : ℤ)=⌊k*(3*s : ℕ)⌋ := hright
  have hP : P (PD.FK.latticeRectangle a w (4*s)) =
      (measure (rectangleGraph a w (4*s)) (RSW.selfDualParameters q)
        (BoundaryCondition.wired {v : RectangleVertex a w (4*s) |
          v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ) ∨ v.val.2=a.2+(4*s : ℕ)})
        (DualityExt.rectangleInnerHorizontalCrossingEvent
          (rectangle_height_subset a w (3*s) (4*s) (by omega)))).toReal := by
    convert hcanonical using 1
    simp only [P,a,zero_add,hright']
    push_cast
    rfl
  exact hsource.trans (hprob.symm.trans hP)

end
end PottsContinuity.Push
