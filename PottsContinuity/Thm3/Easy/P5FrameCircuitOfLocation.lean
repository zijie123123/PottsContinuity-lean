module

public import PottsContinuity.Thm3.Easy.P5FrameCyclePolygonData
public import PottsContinuity.Thm3.Easy.P5FrameComparison

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK

/-- Four P5 frame crossings give the source annulus circuit once the
corresponding polygon's nonzero ray index is known to put the center in its
bounded Jordan domain. -/
theorem p5aAnnulusCircuit_of_fourFrameCrossings_of_rayIndexPolygonLocation
    (n m : ℕ) (hnm : n + 2 ≤ 6 * m)
    (ω : (squareLattice.induce
      (p5aAnnulusVertexSet n : Set (ℤ × ℤ))).edgeSet → Bool)
    (hTop : p5FrameCrossing n m 0 ω)
    (hBottom : p5FrameCrossing n m 1 ω)
    (hRight : p5FrameCrossing n m 2 ω)
    (hLeft : p5FrameCrossing n m 3 ω)
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
    p5aAnnulusCircuitEvent n ω := by
  obtain ⟨z, p, hp, hindex, k, P, hlength, hwalk, hvertices,
      hradial, hopen⟩ :=
    p5_frame_crossings_yield_openSimplePolygon_rayIndex
      n m hnm ω hTop hBottom hRight hLeft
  have hcenterNotVertex : ∀ i : ZMod (k + 3), P.vertex i ≠ (0, 0) := by
    intro i heq
    have hv := hvertices i
    change P.vertex i ∈ PottsContinuity.box (2 * n) \
      PottsContinuity.box (n + 1) at hv
    rw [heq, Finset.mem_sdiff] at hv
    have hbox : (0, 0) ∈ PottsContinuity.box (n + 1) := by
      apply (PottsContinuity.Foundations.mem_box_iff_abs_le
        (n + 1) (0, 0)).mpr
      simp
      omega
    exact hv.2 hbox
  have hradial' : ∀ i : ZMod (k + 3),
      (n : ℤ) < max |(P.vertex i).1 - (0, 0).1| |(P.vertex i).2 - (0, 0).2| ∧
        max |(P.vertex i).1 - (0, 0).1| |(P.vertex i).2 - (0, 0).2| ≤ 2 * (n : ℤ) := by
    simpa using hradial
  refine ⟨k, P, hLocation P hlength hp hwalk hindex hcenterNotVertex,
    hradial', ?_⟩
  intro i
  exact hopen i

/-- The P5 aspect-16 bound yields the uniform corrected annulus probability
as soon as the ray-index point-location theorem for the extracted polygon is
available. -/
theorem p5a_uniform_lower_bound_of_p5Aspect16_and_rayIndexPolygonLocation
    (θ : Parameters)
    (hP5Aspect16 : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      c ≤ rcEventProb (p5BaseDomain m) θ.toP θ.toQ 0 (p5BaseCrossing m))
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
      c₂ ≤ p5aAnnulusProbability θ n := by
  apply p5a_uniform_lower_bound_of_p5Aspect16_and_frameGeometry
    θ hP5Aspect16
  intro n m hn hm hnm hfit houter ω hcross
  rcases hcross with ⟨hTop, hBottom, hRight, hLeft⟩
  exact p5aAnnulusCircuit_of_fourFrameCrossings_of_rayIndexPolygonLocation
    n m hnm ω hTop hBottom hRight hLeft hLocation

end PottsContinuity.Thm3.Easy
