module

public import PottsContinuity.PlanarMixed.FiniteSlit.ArcConnectivity

/-! Literal horizontal and vertical auxiliary paths in the finite outer arcs.
All intermediate points are checked against the balanced box and the slit. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12
noncomputable section

/-- The bottom-left row and each of the two top half-rows have actual open
paths after arc prewiring. No top path crosses the deleted slit bond. -/
theorem horizontal_internal_connected (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y)
    (u v : Vertex M x) (hrow : u.val.2 = v.val.2)
    (hside : (u.val.2 = 0 ∧ u.val.1 ≤ x ∧ v.val.1 ≤ x) ∨
      (u.val.2 = (M : ℤ) ∧ u.val.1 ≤ x-1 ∧ v.val.1 ≤ x-1) ∨
      (u.val.2 = (M : ℤ) ∧ x ≤ u.val.1 ∧ x ≤ v.val.1)) :
    ActualConnected (graph M x y) (internalEdges M x y) u v := by
  let l := min u.val.1 v.val.1
  let r := max u.val.1 v.val.1
  let a : LatticeVertex := (l,u.val.2)
  have hw : ((r-l).toNat : ℤ) = r-l := Int.toNat_of_nonneg (by dsimp [l,r]; omega)
  have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hv := (mem_rectangle_iff M x (by omega) v.val).mp v.property
  have hz (z : RectangleVertex a (r-l).toNat 0) :
      l ≤ z.val.1 ∧ z.val.1 ≤ r ∧ z.val.2 = u.val.2 := by
    have h := (PD.FK.mem_latticeRectangle _ _ _ _).mp z.property
    dsimp [a] at h
    simp only [add_zero] at h
    omega
  have hs : PD.FK.latticeRectangle a (r-l).toNat 0 ⊆
      PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
    intro z h
    have hb := hz ⟨z,h⟩
    apply (mem_rectangle_iff M x (by omega) z).mpr
    dsimp [l,r] at hb
    omega
  have hmem (z : Vertex M x) (hcol : l ≤ z.val.1 ∧ z.val.1 ≤ r)
      (hheight : z.val.2 = u.val.2) : z.val ∈ PD.FK.latticeRectangle a (r-l).toNat 0 := by
    rw [PD.FK.mem_latticeRectangle]
    dsimp [a]
    simp only [add_zero]
    omega
  apply internalEdges_connected_of_rectangle M x y a (r-l).toNat 0 hs
    (u := ⟨u.val,hmem u (by dsimp [l,r]; omega) rfl⟩)
    (v := ⟨v.val,hmem v (by dsimp [l,r]; omega) hrow.symm⟩)
  · intro z t _
    have hz' := hz z
    have ht' := hz t
    dsimp [l,r] at hz' ht'
    rcases hside with hb | ht | ht <;> omega
  · rcases hside with hb | ht | ht
    · apply Or.inl
      intro z
      dsimp only [alpha,beta,Set.mem_ofPred_eq]
      have hz' := hz z
      dsimp [l,r] at hz'
      apply Or.inl
      constructor <;> omega
    · apply Or.inl
      intro z
      dsimp only [alpha,beta,Set.mem_ofPred_eq]
      have hz' := hz z
      dsimp [l,r] at hz'
      apply Or.inr ∘ Or.inr
      constructor <;> omega
    · apply Or.inr
      intro z
      dsimp only [alpha,beta,Set.mem_ofPred_eq]
      have hz' := hz z
      dsimp [l,r] at hz'
      apply Or.inr ∘ Or.inl
      constructor <;> omega

/-- Both outer columns and the retained K ray have actual auxiliary vertical
paths. A fixed column never crosses a deleted horizontal slit bond. -/
theorem vertical_internal_connected (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (u v : Vertex M x) (hcol : u.val.1 = v.val.1)
    (hside : u.val.1 = x-(M : ℤ) ∨ u.val.1 = x+(M : ℤ)-1 ∨
      (u.val.1 = x ∧ y ≤ u.val.2 ∧ y ≤ v.val.2)) :
    ActualConnected (graph M x y) (internalEdges M x y) u v := by
  let l := min u.val.2 v.val.2
  let r := max u.val.2 v.val.2
  let a : LatticeVertex := (u.val.1,l)
  have hw : ((r-l).toNat : ℤ) = r-l := Int.toNat_of_nonneg (by dsimp [l,r]; omega)
  have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hv := (mem_rectangle_iff M x (by omega) v.val).mp v.property
  have hz (z : RectangleVertex a 0 (r-l).toNat) :
      z.val.1 = u.val.1 ∧ l ≤ z.val.2 ∧ z.val.2 ≤ r := by
    have h := (PD.FK.mem_latticeRectangle _ _ _ _).mp z.property
    dsimp [a] at h
    simp only [add_zero] at h
    omega
  have hs : PD.FK.latticeRectangle a 0 (r-l).toNat ⊆
      PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
    intro z h
    have hb := hz ⟨z,h⟩
    apply (mem_rectangle_iff M x (by omega) z).mpr
    dsimp [l,r] at hb
    omega
  have hmem (z : Vertex M x) (hheight : l ≤ z.val.2 ∧ z.val.2 ≤ r)
      (hcolumn : z.val.1 = u.val.1) : z.val ∈ PD.FK.latticeRectangle a 0 (r-l).toNat := by
    rw [PD.FK.mem_latticeRectangle]
    dsimp [a]
    simp only [add_zero]
    omega
  apply internalEdges_connected_of_rectangle M x y a 0 (r-l).toNat hs
    (u := ⟨u.val,hmem u (by dsimp [l,r]; omega) rfl⟩)
    (v := ⟨v.val,hmem v (by dsimp [l,r]; omega) hcol.symm⟩)
  · intro z t _
    have := hz z
    have := hz t
    omega
  · rcases hside with hl | hr | hk
    · exact Or.inl (fun z => Or.inr (Or.inl ((hz z).1.trans hl)))
    · exact Or.inr (fun z => Or.inl ((hz z).1.trans hr))
    · apply Or.inr
      intro z
      dsimp only [alpha,beta,Set.mem_ofPred_eq]
      have hz' := hz z
      dsimp [l,r] at hz'
      apply Or.inr ∘ Or.inr
      constructor <;> omega

end
end PottsContinuity.PlanarMixed.FiniteSlit
