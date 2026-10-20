-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightClopenApproximation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleClopenEvents
public import PottsContinuity.FKC.FiniteFK.HorizontalStripTopBoundary
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeight
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance horizontalStripHeightApproxEdgeFintype (M n : ℕ) :
    Fintype (horizontalStripCutRectangle M n).edgeSet := Fintype.ofFinite _
local instance horizontalStripHeightApproxEdgeDecidableEq (M n : ℕ) :
    DecidableEq (horizontalStripCutRectangle M n).edgeSet := Classical.decEq _
local instance horizontalStripHeightApproxConfigFintype (M n : ℕ) :
    Fintype (Configuration (horizontalStripCutRectangle M n)) := Fintype.ofFinite _

/-- The finite-rectangle approximation to the event that column zero reaches
the strip top from height at most n. The connectivity is in the actual
restricted finite FK graph. -/
def horizontalStripHeightFiniteRectangleEvent (M n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n),
    u.val.1 = 0 ∧ u.val.2 ≤ (n : ℤ) ∧ v.val.2 = (2 * n : ℤ) ∧
      ActualConnected (horizontalStripCutRectangle M n)
        (horizontalStripRectangleRestriction M n ω) u v}

private theorem horizontalStripHeightApproxRestrictionFiber_eq
    (M n : ℕ) (A : Configuration (horizontalStripCutRectangle M n)) :
    {ω : LatticeConfiguration | horizontalStripRectangleRestriction M n ω = A} =
      ⋂ e ∈ (Finset.univ : Finset (horizontalStripCutRectangle M n).edgeSet),
        {ω | ω (horizontalStripRectangleOriginalEdge M n e) = decide (e ∈ A)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ, true_implies]
  constructor
  · intro h e
    have hm : (ω (horizontalStripRectangleOriginalEdge M n e) = true) ↔ e ∈ A := by
      have hm := congrArg (fun B : Configuration (horizontalStripCutRectangle M n) => e ∈ B) h
      simpa [horizontalStripRectangleRestriction] using hm
    by_cases hA : e ∈ A
    · have hs := hm.mpr hA
      simp [hA, hs]
    · have hs : ω (horizontalStripRectangleOriginalEdge M n e) ≠ true :=
        fun ht => hA (hm.mp ht)
      cases hb : ω (horizontalStripRectangleOriginalEdge M n e) <;>
        simp [hb, hA] at hs ⊢
  · intro h
    apply Finset.ext
    intro e
    have he := h e
    simp [horizontalStripRectangleRestriction, he]

private theorem horizontalStripHeightApproxCoordinate_isClopen
    (M n : ℕ) (A : Configuration (horizontalStripCutRectangle M n))
    (e : (horizontalStripCutRectangle M n).edgeSet) :
    IsClopen {ω : LatticeConfiguration |
      ω (horizontalStripRectangleOriginalEdge M n e) = decide (e ∈ A)} := by
  by_cases hA : e ∈ A
  · have hcont : Continuous (fun ω : LatticeConfiguration =>
        ω (horizontalStripRectangleOriginalEdge M n e)) := continuous_apply _
    convert (isClopen_discrete ({true} : Set Bool)).preimage hcont using 1;
      ext ω; simp [hA]
  · have hcont : Continuous (fun ω : LatticeConfiguration =>
        ω (horizontalStripRectangleOriginalEdge M n e)) := continuous_apply _
    convert (isClopen_discrete ({false} : Set Bool)).preimage hcont using 1;
      ext ω; simp [hA]

private theorem horizontalStripHeightApproxRestrictionFiber_isClopen
    (M n : ℕ) (A : Configuration (horizontalStripCutRectangle M n)) :
    IsClopen {ω : LatticeConfiguration | horizontalStripRectangleRestriction M n ω = A} := by
  rw [horizontalStripHeightApproxRestrictionFiber_eq]
  apply isClopen_biInter_finset
  intro e he
  exact horizontalStripHeightApproxCoordinate_isClopen M n A e

theorem isClopen_horizontalStripHeightFiniteRectangleEvent (M n : ℕ) :
    IsClopen (horizontalStripHeightFiniteRectangleEvent M n) := by
  classical
  let T : Finset (Configuration (horizontalStripCutRectangle M n)) :=
    Finset.univ.filter (fun A => ∃ u v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n),
      u.val.1 = 0 ∧ u.val.2 ≤ (n : ℤ) ∧ v.val.2 = (2 * n : ℤ) ∧
        ActualConnected (horizontalStripCutRectangle M n) A u v)
  have hEq : horizontalStripHeightFiniteRectangleEvent M n =
      ⋃ A ∈ T, {ω : LatticeConfiguration | horizontalStripRectangleRestriction M n ω = A} := by
    ext ω
    simp only [horizontalStripHeightFiniteRectangleEvent, T, Set.mem_ofPred_eq,
      Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, v, hu, hy, hv, hconn⟩
      refine ⟨horizontalStripRectangleRestriction M n ω, ?_, rfl⟩
      exact ⟨u, v, hu, hy, hv, hconn⟩
    · rintro ⟨A, ⟨u, v, hu, hy, hv, hconn⟩, hω⟩
      refine ⟨u, v, hu, hy, hv, ?_⟩
      rw [hω]
      exact hconn
  rw [hEq]
  apply isClopen_biUnion_finset
  intro A hA
  exact horizontalStripHeightApproxRestrictionFiber_isClopen M n A

def horizontalStripHeightApproxRectangleToStripHom
    (M n : ℕ) (ω : LatticeConfiguration) :
    horizontalStripRectangleOpenGraph M n ω →g horizontalStripOpenGraph n ω where
  toFun v := ⟨v.val, by
    have hv := (mem_latticeRectangle (-(M : ℤ), 0) v.val (2 * M) (2 * n)).mp v.property
    exact ⟨hv.2.1, by simpa using hv.2.2⟩⟩
  map_rel' := by
    intro u v h
    exact h

theorem horizontalStripHeightFiniteRectangleEvent_subset_heightLE (M n : ℕ) :
    horizontalStripHeightFiniteRectangleEvent M n ⊆
    {ω | horizontalStripHeight n ω 0 ≤ n} := by
  classical
  intro ω hω
  rcases hω with ⟨u, v, hux, huy, hvtop, hconn⟩
  have hstripBounds (z : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :
      0 ≤ z.val.2 ∧ z.val.2 ≤ (2 * n : ℤ) := by
    have hz := (mem_latticeRectangle (-(M : ℤ), 0) z.val (2 * M) (2 * n)).mp z.property
    constructor
    · exact hz.2.1
    · simpa using hz.2.2
  have hgraph : horizontalStripRectangleOpenGraph M n ω =
      openGraph (horizontalStripCutRectangle M n)
        (horizontalStripRectangleRestriction M n ω) :=
    horizontalStripRectangleOpenGraph_eq_openGraph_restriction M n ω
  have hreachRect : (horizontalStripRectangleOpenGraph M n ω).Reachable u v := by
    rw [hgraph]
    exact hconn
  rcases hreachRect with ⟨p⟩
  have hreachStrip : (horizontalStripOpenGraph n ω).Reachable
      (horizontalStripHeightApproxRectangleToStripHom M n ω u)
      (horizontalStripHeightApproxRectangleToStripHom M n ω v) :=
    ⟨p.map (horizontalStripHeightApproxRectangleToStripHom M n ω)⟩
  let y : ℕ := u.val.2.toNat
  have hy : y ≤ 2 * n := by
    have hycast : (y : ℤ) ≤ (2 * (n : ℤ)) := by
      dsimp [y]
      rw [Int.toNat_of_nonneg (hstripBounds u).1]
      exact (hstripBounds u).2
    exact_mod_cast hycast
  have hstart : horizontalStripHeightApproxRectangleToStripHom M n ω u =
      horizontalStripVertexOfNat n 0 y hy := by
    apply Subtype.ext
    change (u.val.1, u.val.2) = ((0 : ℤ), (y : ℤ))
    exact Prod.ext hux (by
      dsimp [y]
      exact (Int.toNat_of_nonneg (hstripBounds u).1).symm)
  have hend : horizontalStripHeightApproxRectangleToStripHom M n ω v =
      horizontalStripVertexOfNat n v.val.1 (2 * n) le_rfl := by
    apply Subtype.ext
    change (v.val.1, v.val.2) = (v.val.1, (2 * (n : ℤ)))
    exact Prod.ext rfl hvtop
  have htop : horizontalStripTopReachable n ω
      (horizontalStripVertexOfNat n 0 y hy) := by
    refine ⟨v.val.1, ?_⟩
    simpa [hstart, hend] using hreachStrip
  have hmem : y ∈ horizontalStripTopHeights n ω 0 := ⟨hy, htop⟩
  have hmin : horizontalStripHeight n ω 0 ≤ y := by
    change Nat.find (horizontalStripTopHeights_nonempty n ω 0) ≤ y
    exact Nat.find_min' (horizontalStripTopHeights_nonempty n ω 0) hmem
  have hySmall : y ≤ n := by
    have hycast : (y : ℤ) ≤ (n : ℤ) := by
      dsimp [y]
      rw [Int.toNat_of_nonneg (hstripBounds u).1]
      exact huy
    exact_mod_cast hycast
  exact le_trans hmin hySmall

end
end PottsContinuity.FKC.Medial
