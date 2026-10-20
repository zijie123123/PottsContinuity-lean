module

public import PottsContinuity.Thm3.Prop4.SplitBoundaryArms
public import PottsContinuity.Thm3.Prop4.ClosingImage

/-!
# The genuine four-edge split surgery

The geometric tube margin gives the exact real cutoff after rounding. Every
lower event, in particular an event defined by closed-dual paths, survives
the closing operation. Separation of the endpoint clusters is a further step.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section

open PD.FK
attribute [local instance] configurationMeasurableSpace

local instance splitSurgeryEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Actual split arms at the real source cutoff; the ceiling retains all endpoint cases. -/
theorem split_star_surviving_boundary_arms (n : ℕ) (r : ℝ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (A : Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))
    (a b z : (box n : Set (ℤ × ℤ)))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = (n : ℤ))
    (hfar : 4*r ≤ tubeDistance a.val b.val z.val)
    (haz : ActualConnected _ A a z) (hbz : ActualConnected _ A b z) :
    ∃ k l : ℕ, k+l=2*n-2 ∧ r ≤ k ∧ r ≤ l ∧
      (A \ vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) ∈
        finiteEndpointArmEvent n a k ∧
      (A \ vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) ∈
        finiteEndpointArmEvent n b l := by
  have hceil := Nat.ceil_lt_add_one (by linarith only [hr] : 0 ≤ r)
  obtain ⟨k,l,hkl,hk,hl,hak,hbl⟩ := split_star_surviving_boundary_arms_realCutoff
    n ⌈r⌉₊ r hn hr (by linarith only [hceil]) hrn A a b z ha hb hfar haz hbz
  exact ⟨k,l,hkl,(Nat.le_ceil r).trans (by exact_mod_cast hk),
    (Nat.le_ceil r).trans (by exact_mod_cast hl),hak,hbl⟩

/-- Closing an original lattice vertex star costs at most four closed-edge factors. -/
theorem vertexStar_closing_image_lower (θ : Parameters) (n : ℕ)
    (ξ : BoundaryCondition (box n : Set (ℤ × ℤ))) (z : (box n : Set (ℤ × ℤ)))
    (B : Set (Configuration (squareLattice.induce (box n : Set (ℤ × ℤ))))) :
    (1-edgeParameter θ)^4 *
      (measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ B).toReal ≤
    (measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ
      ((fun A => A \ vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) '' B)).toReal := by
  have hpow : (1-edgeParameter θ)^4 ≤
      (1-edgeParameter θ)^(vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z).card :=
    pow_le_pow_of_le_one (one_sub_edgeParameter_pos θ).le
      (by linarith only [edgeParameter_pos θ]) (lattice_vertexStar_card_le_four n z)
  exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans
    (finite_closing_image_energy _ θ ξ _ B)

/-- The complete primal surgery and retention of any actual lower dual-screen event. -/
theorem split_star_arms_lower_of_lowerScreen (θ : Parameters) (n : ℕ) (r : ℝ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : 2*⌈r⌉₊ ≤ 2*n-2)
    (ξ : BoundaryCondition (box n : Set (ℤ × ℤ)))
    (a b z : (box n : Set (ℤ × ℤ)))
    (ha : a.val.1 = -(n : ℤ)) (hb : b.val.1 = (n : ℤ))
    (hfar : 4*r ≤ tubeDistance a.val b.val z.val)
    (B S : Set (Configuration (squareLattice.induce (box n : Set (ℤ × ℤ)))))
    (hS : IsLowerSet S)
    (hB : ∀ A ∈ B, A ∈ S ∧ ActualConnected _ A a z ∧ ActualConnected _ A b z) :
    (1-edgeParameter θ)^4 *
      (measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ B).toReal ≤
    (measure (squareLattice.induce (box n : Set (ℤ × ℤ))) θ ξ
      {C | C ∈ S ∧ Disjoint C (vertexStarEdges (squareLattice.induce (box n : Set (ℤ × ℤ))) z) ∧
        ∃ k l : ℕ, k+l=2*n-2 ∧ r ≤ k ∧ r ≤ l ∧
          C ∈ finiteEndpointArmEvent n a k ∧ C ∈ finiteEndpointArmEvent n b l}).toReal := by
  apply (vertexStar_closing_image_lower θ n ξ z B).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  rintro C ⟨A,hA,rfl⟩
  obtain ⟨hAS,haz,hbz⟩ := hB A hA
  refine ⟨hS (Finset.sdiff_subset) hAS,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_sdiff.mp he).2 hf
  · exact split_star_surviving_boundary_arms n r hn hr hrn A a b z ha hb hfar haz hbz

end
end PottsContinuity.Thm3.Prop4
