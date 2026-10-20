module

public import PottsContinuity.PlanarTopology.DualPairCurve
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves BD12
noncomputable section

/-- A short primal crossing and a complementary dual crossing of the expanded
face strip cannot coexist. No assumption about finite-dual pendant edges is needed. -/
theorem wholePlane_rectangle_crossings_exclusive
    (a : LatticeVertex) (w h : ℕ) (hw : 1 ≤ w) (ω : LatticeConfiguration)
    {u v x y : LatticeVertex} (p : PD.squareLattice.Walk u v) (q : PD.squareLattice.Walk x y)
    (hp : kstPathOpen ω p) (hq : kstPathOpen (wholePlaneDualConfigurationHomeomorph ω) q)
    (hpB : kstPathIn p a.1 (a.1+w) a.2 (a.2+h))
    (hqB : kstPathIn q a.1 (a.1+w-1) (a.2-1) (a.2+h))
    (hu : u.1 = a.1) (hv : v.1 = a.1+w)
    (hx : x.2 = a.2-1) (hy : y.2 = a.2+h) : False := by
  have hpne : 0 < p.length := by
    by_contra hn
    have he := congrArg Prod.fst (SimpleGraph.Walk.eq_of_length_eq_zero (p := p) (by omega))
    omega
  have hqne : 0 < q.length := by
    by_contra hn
    have he := congrArg Prod.snd (SimpleGraph.Walk.eq_of_length_eq_zero (p := q) (by omega))
    omega
  let P := latticePairCurve p
  let Q := dualPairCurve q
  have hPB : ∀ θ, (a.1 : ℝ) ≤ (P θ).1 ∧ (P θ).1 ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ)-1/2 ≤ (P θ).2 ∧ (P θ).2 ≤ (a.2 : ℝ)+h+1/2 := by
    intro θ
    apply latticePairCurve_bounds p _ _ ⟨θ,rfl⟩
    intro z hz
    have hh := hpB z hz
    have h1 : (a.1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast hh.1
    have h2 : (z.1 : ℝ) ≤ (a.1 : ℝ)+w := by exact_mod_cast hh.2.1
    have h3 : (a.2 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast hh.2.2.1
    have h4 : (z.2 : ℝ) ≤ (a.2 : ℝ)+h := by exact_mod_cast hh.2.2.2
    exact ⟨h1,h2,by linarith,by linarith⟩
  have hQB : ∀ θ, (a.1 : ℝ) ≤ (Q θ).1 ∧ (Q θ).1 ≤ (a.1 : ℝ)+w ∧
      (a.2 : ℝ)-1/2 ≤ (Q θ).2 ∧ (Q θ).2 ≤ (a.2 : ℝ)+h+1/2 := by
    apply dualPairCurve_bounds q hqne
    intro z hz
    have hh := hqB z hz
    have h1 : (a.1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast hh.1
    have h2 : (z.1 : ℝ) ≤ (a.1 : ℝ)+w-1 := by exact_mod_cast hh.2.1
    have h3 : (a.2 : ℝ)-1 ≤ (z.2 : ℝ) := by exact_mod_cast hh.2.2.1
    have h4 : (z.2 : ℝ) ≤ (a.2 : ℝ)+h := by exact_mod_cast hh.2.2.2
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hQ0 : (Q 0).2 = (a.2 : ℝ)-1/2 := by
    have hh : (x.2 : ℝ) = (a.2 : ℝ)-1 := by exact_mod_cast hx
    have he := congrArg Prod.snd Q.source'
    dsimp at he
    linarith
  have hQ1 : (Q 1).2 = (a.2 : ℝ)+h+1/2 := by
    have hh : (y.2 : ℝ) = (a.2 : ℝ)+h := by exact_mod_cast hy
    have he := congrArg Prod.snd Q.target'
    dsimp at he
    linarith
  obtain ⟨s,t,hst⟩ := pathRectangle_crossing_intersection
    (a := ((a.1 : ℝ),(a.2 : ℝ)-1/2)) (b := ((a.1 : ℝ)+w,(a.2 : ℝ)+h+1/2)) P Q
    (by dsimp; have := Nat.cast_nonneg (α := ℝ) w; linarith) (by dsimp; have := Nat.cast_nonneg (α := ℝ) h; linarith)
    hPB hQB (by simp [hu])
    (by simp [hv]) hQ0 hQ1
  exact Set.disjoint_left.mp (latticePairCurve_dualPairCurve_disjoint ω p q hp hq hpne hqne)
    ⟨s,rfl⟩ ⟨t,hst.symm⟩

end
end PottsContinuity.PlanarTopology
