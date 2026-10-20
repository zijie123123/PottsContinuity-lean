module

public import PottsContinuity.Thm3.RSW.SelfDualSetup

/-!
# Finite-support actual path events in the strip

The support consists of literal strip edges whose two endpoints are in a finite
vertex set. Agreement on those states transfers the same confined open walk.
Thus no boundary connectivity or virtual wired path enters the event.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- Finite strip vertices in an integer rectangle, including rectangles that
extend beyond the strip. -/
noncomputable def stripRectangleVertices (n : ℕ) (a b c d : ℤ) : Finset (stripVertices n) :=
  (latticeRectangle a b c d).preimage Subtype.val Subtype.val_injective.injOn

/-- Literal strip edges with both endpoints in a prescribed finite vertex set. -/
noncomputable def stripInternalEdges (n : ℕ) (S : Finset (stripVertices n)) :
    Finset (stripGraph n).edgeSet :=
  S.sym2.preimage Subtype.val Subtype.val_injective.injOn

/-- An actual open connection between two vertex sets, confined to S. -/
def stripConfinedConnection (n : ℕ) (S : Finset (stripVertices n))
    (A B : Set (stripVertices n)) : Set (StripConfiguration n) :=
  {ω | ∃ (x y : stripVertices n) (w : (stripOpenGraph n ω).Walk x y),
    x ∈ A ∧ y ∈ B ∧ ∀ v ∈ w.support, v ∈ S}

/-- Opening extra states preserves actual strip open edges. -/
theorem stripOpenGraph_mono (n : ℕ) {ω η : StripConfiguration n} (h : ω ≤ η) :
    stripOpenGraph n ω ≤ stripOpenGraph n η := by
  apply SimpleGraph.fromEdgeSet_mono
  rintro e ⟨he, hω⟩
  exact ⟨he, (Bool.le_iff_imp.mp (h ⟨e, he⟩)) hω⟩

/-- Confined actual connection events are increasing. -/
theorem stripConfinedConnection_isUpperSet (n : ℕ) (S : Finset (stripVertices n))
    (A B : Set (stripVertices n)) : IsUpperSet (stripConfinedConnection n S A B) := by
  rintro ω η h ⟨x, y, w, hx, hy, hw⟩
  refine ⟨x, y, w.mapLe (stripOpenGraph_mono n h), hx, hy, ?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hw

/-- Only the states of the internal edges can affect a confined connection. -/
theorem stripConfinedConnection_mem_iff_of_agree (n : ℕ)
    (S : Finset (stripVertices n)) (A B : Set (stripVertices n))
    (ω η : StripConfiguration n)
    (h : ∀ e ∈ stripInternalEdges n S, ω e = η e) :
    ω ∈ stripConfinedConnection n S A B ↔ η ∈ stripConfinedConnection n S A B := by
  suffices hforward : ∀ (ω η : StripConfiguration n),
      (∀ e ∈ stripInternalEdges n S, ω e = η e) →
      ω ∈ stripConfinedConnection n S A B → η ∈ stripConfinedConnection n S A B from
    ⟨hforward ω η h, hforward η ω (fun e he => (h e he).symm)⟩
  rintro ω η hagree ⟨x, y, w, hx, hy, hw⟩
  have he : ∀ e ∈ w.edges, e ∈ (stripOpenGraph n η).edgeSet := by
    intro e he
    have hopen := w.edges_subset_edgeSet he
    have hmem : ∃ h : e ∈ (stripGraph n).edgeSet, ω ⟨e, h⟩ = true := by
      have := (SimpleGraph.edgeSet_fromEdgeSet _).subset hopen
      exact this.1
    obtain ⟨hbase, hstate⟩ := hmem
    have hF : (⟨e, hbase⟩ : (stripGraph n).edgeSet) ∈ stripInternalEdges n S := by
      rw [stripInternalEdges, Finset.mem_preimage, Finset.mem_sym2_iff]
      intro v hv
      exact hw v (SimpleGraph.Walk.mem_support_of_mem_edges he hv)
    apply (SimpleGraph.edgeSet_fromEdgeSet _).superset
    refine ⟨⟨hbase, ?_⟩, ?_⟩
    · exact (hagree _ hF) ▸ hstate
    · exact (SimpleGraph.edgeSet_fromEdgeSet _).subset hopen |>.2
  refine ⟨x, y, w.transfer _ he, hx, hy, ?_⟩
  simpa only [SimpleGraph.Walk.support_transfer] using hw

/-- Every event depending on finitely many strip coordinates is clopen. -/
theorem strip_isClopen_of_finite_support (n : ℕ) (F : Finset (stripGraph n).edgeSet)
    (E : Set (StripConfiguration n))
    (hE : ∀ ω η : StripConfiguration n,
      (∀ e ∈ F, ω e = η e) → (ω ∈ E ↔ η ∈ E)) : IsClopen E := by
  let r : StripConfiguration n → (F → Bool) := fun ω e => ω e.1
  have hr : Continuous r := continuous_pi fun _ => continuous_apply _
  have heq : E = r ⁻¹' (r '' E) := by
    ext ω
    constructor
    · intro hω
      exact ⟨ω, hω, rfl⟩
    · rintro ⟨η, hη, heq⟩
      apply (hE η ω _).mp hη
      intro e he
      exact congrFun heq ⟨e, he⟩
  rw [heq]
  exact (isClopen_discrete (r '' E)).preimage hr

/-- Confined connection events have finite edge support and are clopen. -/
theorem stripConfinedConnection_isClopen (n : ℕ) (S : Finset (stripVertices n))
    (A B : Set (stripVertices n)) : IsClopen (stripConfinedConnection n S A B) :=
  strip_isClopen_of_finite_support n (stripInternalEdges n S) _
    (stripConfinedConnection_mem_iff_of_agree n S A B)

/-- The literal rectangle crossing is precisely a finite-support path event. -/
theorem stripHorizontalCrossing_eq_confined (n : ℕ) (a b c d : ℤ) :
    stripHorizontalCrossing n a b c d =
      stripConfinedConnection n (stripRectangleVertices n a b c d)
        {x | x.1 ∈ ({a} : Set ℤ) ×ˢ Set.Icc c d}
        {y | y.1 ∈ ({b} : Set ℤ) ×ˢ Set.Icc c d} := by
  ext ω
  simp only [stripHorizontalCrossing, stripConfinedConnection, stripRectangleVertices,
    Finset.mem_preimage, latticeRectangle, Finset.mem_product, Finset.mem_Icc,
    Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]

/-- Actual strip crossings are clopen, at every integer rectangle and scale. -/
theorem stripHorizontalCrossing_isClopen (n : ℕ) (a b c d : ℤ) :
    IsClopen (stripHorizontalCrossing n a b c d) := by
  rw [stripHorizontalCrossing_eq_confined]
  exact stripConfinedConnection_isClopen _ _ _ _

end PottsContinuity.RSW
