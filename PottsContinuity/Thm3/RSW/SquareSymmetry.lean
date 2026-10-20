module

public import PottsContinuity.Thm3.RSW.FiniteLocalization

/-!
# Moving an indexed square pair to the standard square

Translation and coordinate exchange preserve actual edges and the free law.
No infinite-volume symmetry or parameter-specific identity is needed.
-/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Free actual-connection probability is invariant under a graph isomorphism. -/
theorem free_connection_probability_eq_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (θ : Parameters) (e : G ≃g H) (x y : V) :
    (measure G θ (BoundaryCondition.free ∅) {A | ActualConnected G A x y}).toReal =
      (measure H θ (BoundaryCondition.free ∅) {A | ActualConnected H A (e x) (e y)}).toReal := by
  have hmap : G.map e.toEquiv.toEmbedding ≤ H := by
    intro a b hab
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj e.toEquiv.toEmbedding G a b).mp hab
    exact e.map_rel_iff.mpr huv
  have hback : H.map e.symm.toEquiv.toEmbedding ≤ G := by
    intro a b hab
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj e.symm.toEquiv.toEmbedding H a b).mp hab
    exact e.symm.map_rel_iff.mpr huv
  apply le_antisymm (embedded_free_connection_probability_le_allq e.toEquiv.toEmbedding hmap θ x y)
  have h := embedded_free_connection_probability_le_allq e.symm.toEquiv.toEmbedding hback θ (e x) (e y)
  change (measure H θ (BoundaryCondition.free ∅) {A | ActualConnected H A (e x) (e y)}).toReal ≤
    (measure G θ (BoundaryCondition.free ∅) {A | ActualConnected G A (e.symm (e x))
      (e.symm (e y))}).toReal at h
  rw [e.symm_apply_apply, e.symm_apply_apply] at h
  exact h

/-- An indexed square maps to [0,m]² by translation and, for a bottom-to-top
pair, exchanging coordinates. -/
def localizationSquareIso {m : ℕ} (t : SquareLocalizationIndex m) :
    (squareLattice.induce (localizationSquare t : Set (ℤ × ℤ))) ≃g
      squareLattice.induce (latticeRectangle 0 m 0 m : Set (ℤ × ℤ)) where
  toEquiv :=
    { toFun := fun z => ⟨if t.2.1 then
          (z.val.2 - (localizationCorner t).2, z.val.1 - (localizationCorner t).1)
        else (z.val.1 - (localizationCorner t).1, z.val.2 - (localizationCorner t).2), by
        have hz := z.property
        simp only [localizationSquare, latticeRectangle, Finset.mem_coe, Finset.mem_product,
          Finset.mem_Icc] at hz ⊢
        split <;> constructor <;> constructor <;> omega⟩
      invFun := fun z => ⟨if t.2.1 then
          (z.val.2 + (localizationCorner t).1, z.val.1 + (localizationCorner t).2)
        else (z.val.1 + (localizationCorner t).1, z.val.2 + (localizationCorner t).2), by
        have hz := z.property
        simp only [localizationSquare, latticeRectangle, Finset.mem_coe, Finset.mem_product,
          Finset.mem_Icc] at hz ⊢
        split <;> constructor <;> constructor <;> omega⟩
      left_inv := by
        intro z
        apply Subtype.ext
        obtain h | h := Bool.dichotomy t.2.1 <;> simp only [h, Bool.false_eq_true, ↓reduceIte,
          sub_add_cancel, Prod.eta]
      right_inv := by
        intro z
        apply Subtype.ext
        obtain h | h := Bool.dichotomy t.2.1 <;> simp only [h, Bool.false_eq_true, ↓reduceIte,
          add_sub_cancel_right, Prod.eta] }
  map_rel_iff' := by
    intro u v
    change squareLattice.Adj
      (if t.2.1 then (u.val.2 - (localizationCorner t).2, u.val.1 - (localizationCorner t).1)
        else (u.val.1 - (localizationCorner t).1, u.val.2 - (localizationCorner t).2))
      (if t.2.1 then (v.val.2 - (localizationCorner t).2, v.val.1 - (localizationCorner t).1)
        else (v.val.1 - (localizationCorner t).1, v.val.2 - (localizationCorner t).2)) ↔
      squareLattice.Adj u.val v.val
    obtain h | h := Bool.dichotomy t.2.1 <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
    · change |(u.val.1 - _) - (v.val.1 - _)| + |(u.val.2 - _) - (v.val.2 - _)| = 1 ↔ _
      have hx : (u.val.1 - (localizationCorner t).1) - (v.val.1 - (localizationCorner t).1) =
          u.val.1 - v.val.1 := by ring
      have hy : (u.val.2 - (localizationCorner t).2) - (v.val.2 - (localizationCorner t).2) =
          u.val.2 - v.val.2 := by ring
      rw [hx, hy]
      rfl
    · change |(u.val.2 - _) - (v.val.2 - _)| + |(u.val.1 - _) - (v.val.1 - _)| = 1 ↔ _
      have hx : (u.val.1 - (localizationCorner t).1) - (v.val.1 - (localizationCorner t).1) =
          u.val.1 - v.val.1 := by ring
      have hy : (u.val.2 - (localizationCorner t).2) - (v.val.2 - (localizationCorner t).2) =
          u.val.2 - v.val.2 := by ring
      rw [hx, hy, add_comm]
      rfl

/-- Frozen finite free pair probability is exactly its finite-edge FK law. -/
theorem finite_free_connection_probability_eq (θ : Parameters) (V : Finset (ℤ × ℤ))
    (x y : ℤ × ℤ) (hx : x ∈ V) (hy : y ∈ V) :
    finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
      (fun ω => ω ∈ finiteConnectionEvent V x y) =
    (measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ (BoundaryCondition.free ∅)
      {A | ActualConnected _ A ⟨x, hx⟩ ⟨y, hy⟩}).toReal := by
  have hevent : finiteBoolEvent V (fun ω => ω ∈ finiteConnectionEvent V x y) =
      {A | ActualConnected _ A ⟨x, hx⟩ ⟨y, hy⟩} := by
    ext A
    exact finiteConnectionEvent_bool_iff V x y hx hy A
  unfold finiteBoundaryEventProbability
  rw [hevent]
  unfold PD.FK.measure
  rw [law_eq_of_boundary_partition_eq θ (frozenBoundaryCondition V 0)
    (BoundaryCondition.free ∅) (by simp [frozenBoundaryCondition, BoundaryCondition.free])]

end
end PottsContinuity.RSW
