module

public import PottsContinuity.Thm3.RSW.SquareSymmetry
public import PottsContinuity.Thm3.RSW.FiniteIso

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Center the original even square by an integral translation, preserving
all endpoint heights and every original sampled bond. -/
def evenSquareToBoxIso (n : ℕ) :
    (squareLattice.induce (latticeRectangle 0 (2*n) 0 (2*n) : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (box n : Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun z => ⟨(z.val.1-(n : ℤ),z.val.2-(n : ℤ)),by
        have hz := z.property
        simp only [latticeRectangle,box,Finset.mem_coe,Finset.mem_product,Finset.mem_Icc] at hz ⊢
        constructor <;> constructor <;> omega⟩
      invFun := fun z => ⟨(z.val.1+(n : ℤ),z.val.2+(n : ℤ)),by
        have hz := z.property
        simp only [latticeRectangle,box,Finset.mem_coe,Finset.mem_product,Finset.mem_Icc] at hz ⊢
        constructor <;> constructor <;> omega⟩
      left_inv := by intro z; apply Subtype.ext; ext <;> dsimp <;> omega
      right_inv := by intro z; apply Subtype.ext; ext <;> dsimp <;> omega }
  map_rel_iff' := by
    intro u v
    change |(u.val.1-(n : ℤ))-(v.val.1-(n : ℤ))|+
      |(u.val.2-(n : ℤ))-(v.val.2-(n : ℤ))|=1 ↔
      |u.val.1-v.val.1|+|u.val.2-v.val.2|=1
    have hx : (u.val.1-(n : ℤ))-(v.val.1-(n : ℤ)) = u.val.1-v.val.1 := by ring
    have hy : (u.val.2-(n : ℤ))-(v.val.2-(n : ℤ)) = u.val.2-v.val.2 := by ring
    rw [hx,hy]

/-- Each exact even-square pair probability is a centered-box pair with the
original heights translated integrally; no endpoint or parity is omitted. -/
theorem squarePairProbability_even_centered (θ : Parameters) (n : ℕ)
    (i j : Fin (2*n+1)) :
    ∃ u v : (box n : Set LatticeVertex), u.val.1 = -(n : ℤ) ∧ v.val.1 = n ∧
      RSW.squarePairProbability θ (2*n) i j =
        (measure _ θ (BoundaryCondition.free ∅)
          (connectivityEvent (squareLattice.induce (box n : Set LatticeVertex)) u v)).toReal := by
  classical
  let V := latticeRectangle 0 (2*n) 0 (2*n)
  have hx : ((0 : ℤ),(i.val : ℤ)) ∈ V := by
    simp only [V,latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    have hi := i.isLt
    constructor <;> constructor <;> omega
  have hy : (((2*n : ℕ) : ℤ),(j.val : ℤ)) ∈ V := by
    simp only [V,latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    have hj := j.isLt
    constructor <;> constructor <;> omega
  let x : (V : Set LatticeVertex) := ⟨(0,i.val),hx⟩
  let y : (V : Set LatticeVertex) := ⟨((2*n : ℕ),j.val),hy⟩
  let e := evenSquareToBoxIso n
  refine ⟨e x,e y,?_,?_,?_⟩
  · change (0 : ℤ)-(n : ℤ) = -(n : ℤ)
    ring
  · change ((2*n : ℕ) : ℤ)-(n : ℤ) = n
    push_cast
    ring
  · have hsmall : RSW.squarePairProbability θ (2*n) i j =
        (measure _ θ (BoundaryCondition.free ∅) (connectivityEvent _ x y)).toReal :=
      RSW.finite_free_connection_probability_eq θ V _ _ hx hy
    have hlarge := RSW.free_probability_iso θ e (connectivityEvent _ (e x) (e y))
    calc
      _ = (measure _ θ (BoundaryCondition.free ∅) (connectivityEvent _ x y)).toReal := hsmall
      _ = (measure _ θ (BoundaryCondition.free ∅)
          {A | configurationIso e A ∈ connectivityEvent _ (e x) (e y)}).toReal := by
        congr 2
        ext A
        exact (actualConnected_configurationIso e A x y).symm
      _ = _ := hlarge.symm

end
end PottsContinuity.Thm3.Prop4
