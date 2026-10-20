module

public import PottsContinuity.Thm4Plane.ScreenArchPath

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial

/-- A dual face center lies in the translated target box when its doubled
coordinates lie in the corresponding closed integer intervals. -/
def screenTargetFaceCenterInBox (m : ℕ) (z : LatticeVertex) : Prop :=
  -(2 * (m : ℤ)) ≤ 2 * z.1 + 1 ∧
    2 * z.1 + 1 ≤ 2 * (m : ℤ) ∧
    -(34 * (m : ℤ)) ≤ 2 * z.2 + 1 ∧
    2 * z.2 + 1 ≤ -(30 * (m : ℤ))

/-- The normalized primal bond has both endpoints in the translated target
box. -/
def screenTargetPrimalBondInBox (m : ℕ) (b : LatticeBond) : Prop :=
  -(m : ℤ) ≤ b.source.1 ∧ b.target.1 ≤ (m : ℤ) ∧
    -(17 * (m : ℤ)) ≤ b.source.2 ∧
    b.target.2 ≤ -(15 * (m : ℤ))

/-- One of the two face centers adjacent to a primal bond contained in the
target box lies in that box. -/
theorem dualBond_has_faceCenter_in_target_of_crossingBond_in_target
    (m : ℕ) (d : LatticeBond)
    (hbox : screenTargetPrimalBondInBox m (primalBondOfDual d)) :
    screenTargetFaceCenterInBox m d.source ∨
      screenTargetFaceCenterInBox m d.target := by
  rcases d with ⟨⟨x, y⟩, axis⟩
  cases axis with
  | horizontal =>
      have hb := hbox
      simp only [screenTargetPrimalBondInBox, primalBondOfDual,
        LatticeBond.source, LatticeBond.target] at hb
      change -(m : ℤ) ≤ x + 1 ∧ x + 1 ≤ (m : ℤ) ∧
        -(17 * (m : ℤ)) ≤ y ∧ y + 1 ≤ -(15 * (m : ℤ)) at hb
      by_cases hx : x + 1 = -(m : ℤ)
      · right
        dsimp [screenTargetFaceCenterInBox, LatticeBond.source,
          LatticeBond.target]
        omega
      · left
        dsimp [screenTargetFaceCenterInBox, LatticeBond.source,
          LatticeBond.target]
        omega
  | vertical =>
      have hb := hbox
      simp only [screenTargetPrimalBondInBox, primalBondOfDual,
        LatticeBond.source, LatticeBond.target] at hb
      change -(m : ℤ) ≤ x ∧ x + 1 ≤ (m : ℤ) ∧
        -(17 * (m : ℤ)) ≤ y + 1 ∧ y + 1 ≤ -(15 * (m : ℤ)) at hb
      by_cases hy : y + 1 = -(17 * (m : ℤ))
      · right
        dsimp [screenTargetFaceCenterInBox, LatticeBond.source,
          LatticeBond.target]
        omega
      · left
        dsimp [screenTargetFaceCenterInBox, LatticeBond.source,
          LatticeBond.target]
        omega

/-- When both adjacent face centers avoid the target box, the crossed primal
bond cannot have both endpoints in it. -/
theorem dualBond_crossingBond_not_in_target_of_faceCenters_outside
    (m : ℕ) (d : LatticeBond)
    (hsource :
      2 * d.source.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * d.source.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * d.source.2 + 1)
    (htarget :
      2 * d.target.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * d.target.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * d.target.2 + 1) :
    ¬ screenTargetPrimalBondInBox m (primalBondOfDual d) := by
  intro hbox
  rcases dualBond_has_faceCenter_in_target_of_crossingBond_in_target
      m d hbox with h | h
  · dsimp [screenTargetFaceCenterInBox] at h
    rcases hsource with hleft | hright | hup <;> omega
  · dsimp [screenTargetFaceCenterInBox] at h
    rcases htarget with hleft | hright | hup <;> omega

/-- Every edge in the finite source-screen closed-dual graph crosses a primal
bond that is not internal to the translated target box. -/
theorem generalScreenActualClosedDualGraph_adj_crossing_not_insideTargetBox
    (m : ℕ) (hm : 1 ≤ m)
    (A : PottsContinuity.FKC.FiniteFK.Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)))
    {u v : LatticeVertex}
    (hAdj : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Adj u v) :
    ∃ d : LatticeBond,
      ∃ e : (PottsContinuity.FKC.FiniteFK.slitBoxGraph
        (16 * m)).edgeSet,
        latticeBondEdge (primalBondOfDual d) =
          slitBoxEdgeEmbedding (16 * m) e ∧
        e ∉ A ∧ (u = d.source ∧ v = d.target ∨
          u = d.target ∧ v = d.source) ∧
        ¬ screenTargetPrimalBondInBox m (primalBondOfDual d) := by
  rcases hAdj with ⟨d, e, he, hclosed, hdir, huF, hvF⟩
  have hsource :
      2 * d.source.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * d.source.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * d.source.2 + 1 := by
    apply generalScreenArchFaceCenters_outside_translatedTargetBox m hm
    rcases hdir with h | h
    · rw [← h.1]
      exact huF
    · rw [← h.2]
      exact hvF
  have htarget :
      2 * d.target.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * d.target.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * d.target.2 + 1 := by
    apply generalScreenArchFaceCenters_outside_translatedTargetBox m hm
    rcases hdir with h | h
    · rw [← h.2]
      exact hvF
    · rw [← h.1]
      exact huF
  exact ⟨d, e, he, hclosed, hdir,
    dualBond_crossingBond_not_in_target_of_faceCenters_outside m d
      hsource htarget⟩

end PottsContinuity.Thm4Plane
