module

public import PottsContinuity.Thm3.RSW.LatticePathIntersection
public import PottsContinuity.Thm3.RSW.StripPlanarGluing

/-!
# Actual interlaced strip paths and unconditional deterministic gluing

Continuous interlacing and the unit-bond endpoint lemma discharge the planar
primitive. The source translated connections therefore glue without a geometric
hypothesis. The probabilistic bound for the local connection events is proved
separately, in `Thm3.Push.DirectPrefixRoundedLocal`
(`directPrefixSystem_rounded_local_of_small_horizontal`), and the two are combined
in the proof of Lemma 2 (`Push.selfDual_stripRSW_of_directPrefixSystems`).
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- Alternating bottom endpoints force a common vertex for arbitrary actual
nearest-neighbour walks in the upper half-plane. -/
theorem lattice_interlaced_walks_intersect (a b c d : ℤ × ℤ)
    (p : squareLattice.Walk a c) (r : squareLattice.Walk b d)
    (ha : a.2 = 0) (hb : b.2 = 0) (hc : c.2 = 0) (hd : d.2 = 0)
    (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1) (hcd : c.1 ≤ d.1)
    (hp : ∀ z ∈ p.support, 0 ≤ z.2) (hr : ∀ z ∈ r.support, 0 ≤ z.2) :
    ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  classical
  rcases a with ⟨a, ya⟩
  rcases b with ⟨b, yb⟩
  rcases c with ⟨c, yc⟩
  rcases d with ⟨d, yd⟩
  dsimp at ha hb hc hd hab hbc hcd
  subst ya; subst yb; subst yc; subst yd
  by_cases he : a = b
  · subst b
    exact ⟨(a, 0), p.start_mem_support, r.start_mem_support⟩
  have hab' : a < b := lt_of_le_of_ne hab he
  by_cases he : b = c
  · subst c
    exact ⟨(b, 0), p.end_mem_support, r.start_mem_support⟩
  have hbc' : b < c := lt_of_le_of_ne hbc he
  by_cases he : c = d
  · subst d
    exact ⟨(c, 0), p.end_mem_support, r.end_mem_support⟩
  have hcd' : c < d := lt_of_le_of_ne hcd he
  let F := p.support.toFinset ∪ r.support.toFinset
  let M := F.sup fun z => max z.1.natAbs z.2.natAbs
  have hbound (z : ℤ × ℤ) (hz : z ∈ F) :
      |z.1| ≤ (M : ℤ) ∧ |z.2| ≤ (M : ℤ) := by
    have hs : max z.1.natAbs z.2.natAbs ≤ M :=
      Finset.le_sup (f := fun z : ℤ × ℤ => max z.1.natAbs z.2.natAbs) hz
    constructor
    · rw [← Int.natCast_natAbs]
      exact_mod_cast le_trans (le_max_left _ _) hs
    · rw [← Int.natCast_natAbs]
      exact_mod_cast le_trans (le_max_right _ _) hs
  have hpsupp (z : ℤ × ℤ) (hz : z ∈ p.support) :
      -(M : ℝ) ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ M ∧ 0 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ M := by
    have hb := hbound z (Finset.mem_union_left _ (List.mem_toFinset.mpr hz))
    exact ⟨by exact_mod_cast (abs_le.mp hb.1).1,
      by exact_mod_cast (abs_le.mp hb.1).2, by exact_mod_cast hp z hz,
      by exact_mod_cast (abs_le.mp hb.2).2⟩
  have hrsupp (z : ℤ × ℤ) (hz : z ∈ r.support) :
      -(M : ℝ) ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ M ∧ 0 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ M := by
    have hb := hbound z (Finset.mem_union_right _ (List.mem_toFinset.mpr hz))
    exact ⟨by exact_mod_cast (abs_le.mp hb.1).1,
      by exact_mod_cast (abs_le.mp hb.1).2, by exact_mod_cast hr z hz,
      by exact_mod_cast (abs_le.mp hb.2).2⟩
  obtain ⟨z, hzp, hzr⟩ := path_intersection_of_strict_interlacing
    (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (-(M : ℝ)) M M
    (by exact_mod_cast hab') (by exact_mod_cast hbc') (by exact_mod_cast hcd')
    (hpsupp _ p.start_mem_support).1 (hrsupp _ r.end_mem_support).2.1
    (Nat.cast_nonneg M)
    ((latticePairWalkPath p).cast (by simp [latticePairEmbed]) (by simp [latticePairEmbed]))
    ((latticePairWalkPath r).cast (by simp [latticePairEmbed]) (by simp [latticePairEmbed]))
    (latticePairWalkPath_bounds p _ _ _ _ hpsupp)
    (latticePairWalkPath_bounds r _ _ _ _ hrsupp)
  exact latticePairWalkPath_common_vertex p r z hzp hzr

/-- Interlaced strip walks intersect: the exact planar strip statement, proved with
non-strict endpoint ordering and without assuming simple walks. -/
theorem strip_interlaced_walks_intersect
    (n : ℕ) (ω : StripConfiguration n)
    (a b c d : stripVertices n)
    (p : (stripOpenGraph n ω).Walk a c)
    (r : (stripOpenGraph n ω).Walk b d)
    (ha : a.1.2 = 0) (hb : b.1.2 = 0) (hc : c.1.2 = 0) (hd : d.1.2 = 0)
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (hcd : c.1.1 ≤ d.1.1)
    (hp : ∀ z ∈ p.support, 0 ≤ z.1.2)
    (hr : ∀ z ∈ r.support, 0 ≤ z.1.2) :
    ∃ z, z ∈ p.support ∧ z ∈ r.support := by
  let f : stripOpenGraph n ω →g squareLattice :=
    ⟨Subtype.val, fun h => stripOpenGraph_le n ω h⟩
  have hp' : ∀ z ∈ (p.map f).support, 0 ≤ z.2 := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    exact hp v hv
  have hr' : ∀ z ∈ (r.map f).support, 0 ≤ z.2 := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    exact hr v hv
  obtain ⟨z, hz, hz'⟩ := lattice_interlaced_walks_intersect a.1 b.1 c.1 d.1
    (p.map f) (r.map f) ha hb hc hd hab hbc hcd hp' hr'
  rw [SimpleGraph.Walk.support_map] at hz hz'
  obtain ⟨u, hu, huz⟩ := List.mem_map.mp hz
  obtain ⟨v, hv, hvz⟩ := List.mem_map.mp hz'
  have huv : u = v := Subtype.ext (huz.trans hvz.symm)
  exact ⟨u, hu, huv ▸ hv⟩

end PottsContinuity.RSW
