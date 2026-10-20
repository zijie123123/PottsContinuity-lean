module

public import PottsContinuity.Thm3.Easy.P5FrameCircuitOfLocation

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK

/-- The source P5 bounds imply the corrected P5a annulus bound once the
nonzero-index polygon point-location theorem is available. The conclusion
starts at n ≥ 2, where the corrected annulus is nonempty. -/
theorem p5_implies_p5a_of_rayIndexPolygonLocation
    (q : Set.Ici (1 : ℝ))
    (hP5 : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ rcEventProb
        (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
          (-(n : ℤ)) (2 * (n : ℤ)))
        (criticalParameters q).toP (criticalParameters q).toQ 0
        (horizontalCrossing
          (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
            (-(n : ℤ)) (2 * (n : ℤ)))
          0 ⌊α * (n : ℝ)⌋ 0 n))
    (hLocation : ∀ {z : LatticeVertex}
      {p : squareLattice.Walk z z} {k : ℕ}
      (P : FKC.LatticePolygon k),
      k + 3 = p.length →
      p.IsCycle →
      (∀ i : ZMod (k + 3), P.vertex i = p.getVert i.val) →
      PD.Duality.rayIndex (0, 0) p ≠ 0 →
      (∀ i : ZMod (k + 3), P.vertex i ≠ (0, 0)) →
      FKC.latticeEmbed ⟨1, by norm_num⟩ (0, 0) ∈
        P.domain ⟨1, by norm_num⟩) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ n : ℕ, 2 ≤ n →
      c₂ ≤ p5aAnnulusProbability (criticalParameters q) n := by
  obtain ⟨c, hc, hbound⟩ := hP5 16 (by norm_num)
  have hP5Aspect16 : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      c ≤ rcEventProb (p5BaseDomain m)
        (criticalParameters q).toP (criticalParameters q).toQ 0
        (p5BaseCrossing m) := by
    refine ⟨c, hc, ?_⟩
    intro m hm
    have h := hbound m hm
    have hright : ⌊(16 + 1 : ℝ) * (m : ℝ)⌋ = 17 * (m : ℤ) := by
      have hreal : (16 + 1 : ℝ) * (m : ℝ) = ((17 * m : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hreal, Int.floor_natCast]
      norm_cast
    have hcross : ⌊(16 : ℝ) * (m : ℝ)⌋ = 16 * (m : ℤ) := by
      have hreal : (16 : ℝ) * (m : ℝ) = ((16 * m : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hreal, Int.floor_natCast]
      norm_cast
    rw [hright, hcross] at h
    change c ≤ rcEventProb (p5BaseDomain m)
      (criticalParameters q).toP (criticalParameters q).toQ 0
      (p5BaseCrossing m) at h
    exact h
  exact p5a_uniform_lower_bound_of_p5Aspect16_and_rayIndexPolygonLocation
    (criticalParameters q) hP5Aspect16 hLocation

end PottsContinuity.Thm3.Easy
