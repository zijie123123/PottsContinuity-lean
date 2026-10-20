module

public import PottsContinuity.Thm3.RSW.BoundingSquare

/-!
# Deterministic cluster cover in Lemma 5

DCST, proof of Lemma 5 (the box of a maximal pair), TeX lines 1493–1508.
The actual root cluster is finite in box N. Its coordinate extrema give the
indexed bounding square, both connected endpoints, and the scale m ≥ k.
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- The actual root cluster as a finite subset of the ambient lattice domain.
Endpoint membership is part of finiteConnectionEvent, including for an origin
outside V. -/
noncomputable def finiteRootCluster (V : Finset (ℤ × ℤ))
    (ω : (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) : Finset (ℤ × ℤ) := by
  classical
  exact V.filter (fun z => ω ∈ finiteConnectionEvent V (0, 0) z)

/-- Every finite arm is covered by a confined connection between a maximal
opposite-side pair. The orientation and both endpoint offsets are explicit,
and the scale is at least the arm radius. -/
theorem finiteArmEvent_boundingSquare (N k : ℕ)
    (ω : (squareLattice.induce (box N : Set (ℤ × ℤ))).edgeSet → Bool)
    (hω : ω ∈ finiteArmEvent N k) :
    ∃ m : ℕ, k ≤ m ∧ ∃ t : SquareLocalizationIndex m,
      ω ∈ finiteConnectionEvent (box N) t.1.val (localizationPartner t) ∧
      (∀ z, ω ∈ finiteConnectionEvent (box N) t.1.val z → z ∈ localizationSquare t) ∧
      max |t.1.val.1 - (localizationPartner t).1|
        |t.1.val.2 - (localizationPartner t).2| = (m : ℤ) := by
  classical
  obtain ⟨y, hybd, hroot, hy, hconn⟩ := hω
  let C := finiteRootCluster (box N) ω
  have hC (z : ℤ × ℤ) : z ∈ C ↔
      z ∈ box N ∧ ω ∈ finiteConnectionEvent (box N) (0, 0) z := by
    simp only [C, finiteRootCluster, Finset.mem_filter]
  have h0 : (0, 0) ∈ C := (hC _).mpr
    ⟨hroot, hroot, hroot, SimpleGraph.Reachable.refl _⟩
  have hyC : y ∈ C := (hC _).mpr ⟨hy, hroot, hy, hconn⟩
  obtain ⟨m, t, haC, hbC, hsubset⟩ := finiteCloud_boundingSquare C h0
  have h0square := hsubset h0
  have hysquare := hsubset hyC
  have hk : k ≤ m := by
    have hbd : max |y.1| |y.2| = (k : ℤ) := by
      simpa only [Foundations.vertexBoundary_box_eq, Set.mem_ofPred_eq] using hybd
    simp only [localizationSquare, latticeRectangle, Finset.mem_product, Finset.mem_Icc]
      at h0square hysquare
    have hx : |y.1| ≤ (m : ℤ) := by rw [abs_le]; constructor <;> omega
    have hy' : |y.2| ≤ (m : ℤ) := by rw [abs_le]; constructor <;> omega
    have := max_le hx hy'
    omega
  obtain ⟨haV, _, _, hroota⟩ := (hC _).mp haC
  obtain ⟨hbV, _, _, hrootb⟩ := (hC _).mp hbC
  refine ⟨m, hk, t, ⟨haV, hbV, hroota.symm.trans hrootb⟩, ?_,
    localization_endpoints_distance t⟩
  intro z hz
  obtain ⟨_, hzV, haz⟩ := hz
  exact hsubset ((hC z).mpr ⟨hzV, hroot, hzV, hroota.trans haz⟩)

end PottsContinuity.RSW
