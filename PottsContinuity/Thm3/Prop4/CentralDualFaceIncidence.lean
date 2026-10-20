module

public import PottsContinuity.Thm3.Prop4.TubeCentralRetainedBonds
public import PottsContinuity.PD.Duality.RectangleLabelCutIncidence

/-!
# Genuine sampled incidence of every central physical dual face

The central column contains no isolated expanded-box corner. Every physical
face on that column is incident to an actual original horizontal bond,
including the bottom exterior face. Nontrivial true dual walks also supply
actual incident labels at their endpoints.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- Every physical horizontal bond in the central column has the two exact
crossing dual face labels, with no exterior completion edge. -/
theorem central_horizontal_crossing_dual {n : ℕ} (hn : 1 ≤ n) (y : ℤ)
    (hy : -(n : ℤ) ≤ y ∧ y ≤ n) :
    ∃ d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n),
      d.crossingBond.source = (0,y-1) ∧ d.crossingBond.target = (0,y) := by
  have h0 : (0,y) ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega),Finset.mem_Icc.mpr hy⟩
  have h1 : (1,y) ∈ PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega),Finset.mem_Icc.mpr hy⟩
  let d := rectangleCutDualEdgeOfBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    ⟨(0,y),.horizontal⟩ h0 h1
  have hcross : d.crossingBond = dualBondOfPrimal ⟨(0,y),.horizontal⟩ :=
    rectangleCutDualEdgeOfBond_crossingBond _ _ _ _ h0 h1
  refine ⟨d,?_,?_⟩
  all_goals
    rw [hcross]
    simp [dualBondOfPrimal,LatticeBond.source,LatticeBond.target]

/-- Every central face in the entire physical expanded dual span is incident
to a genuine sampled crossing bond, including both physical exterior ends. -/
theorem central_dual_face_incident {n : ℕ} (hn : 1 ≤ n) (c : ℤ)
    (hc : -(n : ℤ)-1 ≤ c ∧ c ≤ n) :
    ∃ d : RectangleDualEdgeCarrier (-(n : ℤ),-(n : ℤ)) (2*n) (2*n),
      (0,c) = d.crossingBond.source ∨ (0,c) = d.crossingBond.target := by
  by_cases hbottom : c = -(n : ℤ)-1
  · obtain ⟨d,hd,_⟩ := central_horizontal_crossing_dual hn (-(n : ℤ)) (by omega)
    exact ⟨d,Or.inl (by rw [hd,hbottom])⟩
  · obtain ⟨d,_,hd⟩ := central_horizontal_crossing_dual hn c (by omega)
    exact ⟨d,Or.inr hd.symm⟩

/-- A nontrivial walk in any subgraph of the true finite dual has a genuine
sampled crossing-bond label incident to its terminal original face. -/
theorem rectangle_dual_walk_end_incident (a : LatticeVertex) (w h : ℕ)
    {G : SimpleGraph (RectangleDualVertex a w h)} (hG : G ≤ rectangleDualGraph a w h)
    {x y : RectangleDualVertex a w h} (p : G.Walk x y) (hxy : x ≠ y) :
    ∃ d : RectangleDualEdgeCarrier a w h,
      y.val = d.crossingBond.source ∨ y.val = d.crossingBond.target := by
  cases p.reverse with
  | nil => exact False.elim (hxy rfl)
  | @cons y z x hyz q =>
    obtain ⟨d,hpair⟩ := (rectangleDualGraph_adj_iff a w h y z).mp (hG hyz)
    have hy : y ∈ rectangleDualCarrierPair a w h d := by
      rw [← hpair]
      exact Sym2.mem_iff'.mpr (Or.inl rfl)
    rcases Sym2.mem_iff'.mp hy with hy | hy
    · exact ⟨d,Or.inl (congrArg Subtype.val hy)⟩
    · exact ⟨d,Or.inr (congrArg Subtype.val hy)⟩

end
end PottsContinuity.Thm3.Prop4
