module

public import PottsContinuity.Thm3.Prop4.EndpointInsertion
public import PottsContinuity.Thm3.RSW.SquareSymmetry
public import PottsContinuity.Thm3.RSW.EmbeddedFreeConnection

/-!
# The genuine odd-square comparison in the remark after Lemma 7

DCST, TeX lines 1761–1767. Include the smaller square in the larger one,
then extend its right endpoint by one original edge. The left endpoint
already belongs to the larger square's left side, so one edge suffices.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- The actual maximum square-pair probability on side M is at most the
next-side maximum divided by the uniform one-edge insertion fraction. -/
theorem maxSquarePairProbability_le_next (θ : PD.FK.Parameters) (M : ℕ) :
    RSW.maxSquarePairProbability θ M ≤
      RSW.maxSquarePairProbability θ (M+1)/PD.RCInfinite.openEnergy θ := by
  classical
  let V := latticeRectangle 0 M 0 M
  let W := latticeRectangle 0 (M+1) 0 (M+1)
  have hVW : V ⊆ W := by
    intro z hz
    simp only [V,W,latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hz ⊢
    constructor <;> constructor <;> omega
  let f : (V : Set (ℤ × ℤ)) ↪ (W : Set (ℤ × ℤ)) :=
    ⟨fun z => ⟨z.1,hVW z.2⟩,fun _ _ h =>
      Subtype.ext (congrArg (fun z : (W : Set (ℤ × ℤ)) => z.val) h)⟩
  have hmap : (squareLattice.induce (V : Set (ℤ × ℤ))).map f ≤
      squareLattice.induce (W : Set (ℤ × ℤ)) := by
    rw [SimpleGraph.map_le_iff_le_comap]
    intro x y hxy
    exact hxy
  apply RSW.maxSquarePairProbability_le
  intro i j
  have hx : ((0 : ℤ),(i.1 : ℤ)) ∈ V := by
    simp only [V,latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    have := i.2
    constructor <;> constructor <;> omega
  have hy : ((M : ℤ),(j.1 : ℤ)) ∈ V := by
    simp only [V,latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    have := j.2
    constructor <;> constructor <;> omega
  let x : (V : Set (ℤ × ℤ)) := ⟨(0,i.1),hx⟩
  let y : (V : Set (ℤ × ℤ)) := ⟨(M,j.1),hy⟩
  have hw : (((M+1 : ℕ) : ℤ),(j.1 : ℤ)) ∈ W := by
    simp only [W,latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    have := j.2
    constructor <;> constructor <;> omega
  let w : (W : Set (ℤ × ℤ)) := ⟨(((M+1 : ℕ) : ℤ),j.1),hw⟩
  have hyw : (squareLattice.induce (W : Set (ℤ × ℤ))).Adj (f y) w := by
    change |(M : ℤ)-((M+1 : ℕ) : ℤ)|+|(j.1 : ℤ)-j.1|=1
    simp
  let i' : Fin (M+1+1) := ⟨i.1,by have := i.2; omega⟩
  let j' : Fin (M+1+1) := ⟨j.1,by have := j.2; omega⟩
  have hsmall : RSW.squarePairProbability θ M i j =
      (PD.FK.measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ (PD.FK.BoundaryCondition.free ∅)
        (PD.FK.connectivityEvent _ x y)).toReal :=
    RSW.finite_free_connection_probability_eq θ V _ _ hx hy
  have hlarge : RSW.squarePairProbability θ (M+1) i' j' =
      (PD.FK.measure (squareLattice.induce (W : Set (ℤ × ℤ))) θ (PD.FK.BoundaryCondition.free ∅)
        (PD.FK.connectivityEvent _ (f x) w)).toReal :=
    RSW.finite_free_connection_probability_eq θ W _ _ (hVW hx) hw
  have hincl := RSW.embedded_free_connection_probability_le_allq f hmap θ x y
  have hext := finite_connection_endpoint_insertion (squareLattice.induce (W : Set (ℤ × ℤ))) θ
    (PD.FK.BoundaryCondition.free ∅) (f x) (f y) w hyw
  have hbound : PD.RCInfinite.openEnergy θ*RSW.squarePairProbability θ M i j ≤
      RSW.squarePairProbability θ (M+1) i' j' := by
    rw [hsmall,hlarge]
    exact (mul_le_mul_of_nonneg_left hincl (PD.RCInfinite.openEnergy_pos θ).le).trans hext
  apply (le_div_iff₀ (PD.RCInfinite.openEnergy_pos θ)).mpr
  have hbound' : RSW.squarePairProbability θ M i j*PD.RCInfinite.openEnergy θ ≤
      RSW.squarePairProbability θ (M+1) i' j' := by
    rw [mul_comm]
    exact hbound
  exact hbound'.trans (RSW.squarePairProbability_le_max θ (M+1) i' j')

end PottsContinuity.Thm3.Prop4
