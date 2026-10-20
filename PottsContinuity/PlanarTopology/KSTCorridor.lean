module

public import PottsContinuity.PlanarTopology.KSTCurveIntersection
public import PottsContinuity.PlanarTopology.ContinuousWallBarrier
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Curves PD.FK.Medial BD12
noncomputable section

/-- A confined lattice walk has a confined continuous interpolation, with
integer endpoint bounds transported exactly to real coordinates. -/
theorem latticePairCurve_of_pathIn {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (l r b t : ℤ) (hp : kstPathIn p l r b t) :
    ∀ z ∈ Set.range (latticePairCurve p),
      (l : ℝ) ≤ z.1 ∧ z.1 ≤ (r : ℝ) ∧ (b : ℝ) ≤ z.2 ∧ z.2 ≤ (t : ℝ) := by
  apply latticePairCurve_bounds
  intro z hz
  obtain ⟨h1,h2,h3,h4⟩ := hp z hz
  exact ⟨by exact_mod_cast h1,by exact_mod_cast h2,
    by exact_mod_cast h3,by exact_mod_cast h4⟩

/-- KST Lemma 2 (corridor construction), in the exact integral-scale corridor form used by
`kst_corridor_bridge_inclusion`.
The first alternative is an actual CONTIGUOUS subpath in either orientation;
the second uses a vertex of the four original walks. The avoidance connector
is constructed by medial duality and is never assumed to be a lattice path. -/
theorem kst_corridor (k : ℕ) (hk : 1 ≤ k)
    (left right bottom top : ℤ)
    (hleft : left ≤ -13 * (k : ℤ)) (hright : 13 * (k : ℤ) ≤ right)
    (hbottom : bottom ≤ -12 * (k : ℤ)) (htop : 12 * (k : ℤ) ≤ top)
    {a b c d s t x y : LatticeVertex}
    (gamma : PD.squareLattice.Walk a b) (gamma' : PD.squareLattice.Walk c d)
    (L : PD.squareLattice.Walk s a) (R : PD.squareLattice.Walk t c)
    (pi : PD.squareLattice.Walk x y)
    (hg : kstMPath (12 * k) gamma) (hg' : kstMPath (12 * k) gamma')
    (hL : kstPathIn L left right bottom top)
    (hR : kstPathIn R left right bottom top)
    (hs : s.1 = left) (ht : t.1 = right)
    (hpi : pi.IsPath) (hpiIn : kstPathIn pi left right bottom top)
    (hx : x.2 = top) (hy : y.2 = bottom) :
    (∃ (u v : LatticeVertex) (q : PD.squareLattice.Walk u v),
      kstMPath (12 * k) q ∧ (q.IsSubwalk pi ∨ q.reverse.IsSubwalk pi)) ∨
    (∃ z ∈ pi.support,
      z ∈ gamma.support ∨ z ∈ gamma'.support ∨ z ∈ L.support ∨ z ∈ R.support) := by
  classical
  by_cases hno : ∃ (u v : LatticeVertex) (q : PD.squareLattice.Walk u v),
      kstMPath (12*k) q ∧ (q.IsSubwalk pi ∨ q.reverse.IsSubwalk pi)
  · exact Or.inl hno
  right
  obtain ⟨B,D,hB,hD,Q,hQ,hQpi⟩ := kst_clamped_connector_of_no_mpath k hk pi hpi hno
  have hl : (left : ℝ) ≤ -13*(k : ℝ) := by exact_mod_cast hleft
  have hr : 13*(k : ℝ) ≤ (right : ℝ) := by exact_mod_cast hright
  have hb : (bottom : ℝ) ≤ -12*(k : ℝ) := by exact_mod_cast hbottom
  have htR : 12*(k : ℝ) ≤ (top : ℝ) := by exact_mod_cast htop
  have box_mono (z : ℝ × ℝ)
      (hz : -13*(k : ℝ) ≤ z.1 ∧ z.1 ≤ 13*(k : ℝ) ∧
        -12*(k : ℝ) ≤ z.2 ∧ z.2 ≤ 12*(k : ℝ)) :
      (left : ℝ) ≤ z.1 ∧ z.1 ≤ (right : ℝ) ∧
        (bottom : ℝ) ≤ z.2 ∧ z.2 ≤ (top : ℝ) :=
    ⟨hl.trans hz.1,hz.2.1.trans hr,hb.trans hz.2.2.1,hz.2.2.2.trans htR⟩
  have hG := kst_mpath_meets_connector k hk gamma hg hB hD Q hQ
  have hG' := kst_mpath_meets_connector k hk gamma' hg' hB hD Q hQ
  obtain ⟨z,hzpi,hzw⟩ := continuous_wall_barrier left right bottom top
    (latticePairCurve gamma) (latticePairCurve gamma')
    (latticePairCurve L) (latticePairCurve R) (latticePairCurve pi)
    (Q.map continuous_complexCoordinates)
    (fun z hz => box_mono z (kst_mpath_pairCurve_bounds k gamma hg z hz))
    (fun z hz => box_mono z (kst_mpath_pairCurve_bounds k gamma' hg' z hz))
    (latticePairCurve_of_pathIn L _ _ _ _ hL)
    (latticePairCurve_of_pathIn R _ _ _ _ hR)
    (latticePairCurve_of_pathIn pi _ _ _ _ hpiIn)
    (by rintro z ⟨θ,rfl⟩; exact box_mono _ (hQ θ))
    (by change (s.1 : ℝ) = (left : ℝ); exact_mod_cast hs)
    (by change (t.1 : ℝ) = (right : ℝ); exact_mod_cast ht)
    (by change (x.2 : ℝ) = (top : ℝ); exact_mod_cast hx)
    (by change (y.2 : ℝ) = (bottom : ℝ); exact_mod_cast hy)
    hG hG' (latticePairCurve_disjoint pi Q hQpi)
  obtain ⟨α,hα⟩ := hzpi
  rcases hzw with hz | hz | hz | hz
  · obtain ⟨β,hβ⟩ := hz
    obtain ⟨v,hv,hvg⟩ := latticePairCurves_common_vertex pi gamma (hα.trans hβ.symm)
    exact ⟨v,hv,Or.inl hvg⟩
  · obtain ⟨β,hβ⟩ := hz
    obtain ⟨v,hv,hvg⟩ := latticePairCurves_common_vertex pi gamma' (hα.trans hβ.symm)
    exact ⟨v,hv,Or.inr (Or.inl hvg)⟩
  · obtain ⟨β,hβ⟩ := hz
    obtain ⟨v,hv,hvg⟩ := latticePairCurves_common_vertex pi L (hα.trans hβ.symm)
    exact ⟨v,hv,Or.inr (Or.inr (Or.inl hvg))⟩
  · obtain ⟨β,hβ⟩ := hz
    obtain ⟨v,hv,hvg⟩ := latticePairCurves_common_vertex pi R (hα.trans hβ.symm)
    exact ⟨v,hv,Or.inr (Or.inr (Or.inr hvg))⟩

end
end PottsContinuity.PlanarTopology
