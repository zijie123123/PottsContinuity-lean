module

public import PottsContinuity.PlanarTopology.KSTSideBridge
public import PottsContinuity.PlanarTopology.KSTCorridor
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- A contact with an attached wall gives an actual open connection from the
attachment's side vertex to the original crossing's initial vertex. -/
theorem kst_wall_contact_connection (ω : LatticeConfiguration)
    (left right bottom top : ℤ) {a b s u v z : LatticeVertex}
    (g : PD.squareLattice.Walk a b) (L : PD.squareLattice.Walk s a)
    (p : PD.squareLattice.Walk u v)
    (hgO : kstPathOpen ω g) (hLO : kstPathOpen ω L) (hpO : kstPathOpen ω p)
    (hg : kstPathIn g left right bottom top) (hL : kstPathIn L left right bottom top)
    (hp : kstPathIn p left right bottom top)
    (hzp : z ∈ p.support) (hz : z ∈ g.support ∨ z ∈ L.support) :
    ∃ W : PD.squareLattice.Walk s u,
      kstPathOpen ω W ∧ kstPathIn W left right bottom top := by
  let P := p.takeUntil z hzp
  have hPs := p.isSubwalk_takeUntil hzp
  have hPO := kstPathOpen_of_subwalk hPs hpO
  rcases hz with hzg | hzL
  · let G := g.takeUntil z hzg
    have hGs := g.isSubwalk_takeUntil hzg
    refine ⟨L.append (G.append P.reverse),?_,?_⟩
    · exact kstPathOpen_append L _ hLO (kstPathOpen_append G _
        (kstPathOpen_of_subwalk hGs hgO) ((kstPathOpen_reverse_iff ω P).mpr hPO))
    · intro x hx
      simp only [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse,List.mem_reverse] at hx
      rcases hx with hx | hx | hx
      · exact hL x hx
      · exact hg x (hGs.support_subset hx)
      · exact hp x (hPs.support_subset hx)
  · let T := L.takeUntil z hzL
    have hTs := L.isSubwalk_takeUntil hzL
    refine ⟨T.append P.reverse,?_,?_⟩
    · exact kstPathOpen_append T _ (kstPathOpen_of_subwalk hTs hLO)
        ((kstPathOpen_reverse_iff ω P).mpr hPO)
    · intro x hx
      simp only [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse,List.mem_reverse] at hx
      exact hx.elim (fun h => hL x (hTs.support_subset h))
        (fun h => hp x (hPs.support_subset h))

/-- Exact left translate of a bridge forced by a side-to-central-top connection.
All integer fractions are justified by 12 | m, not silently rounded. -/
theorem kst_left_connection_translated_bridge (m : ℕ) (hm : 12 ∣ m) (hm0 : 1 ≤ m)
    (ω : LatticeConfiguration) {s u : LatticeVertex} (p : PD.squareLattice.Walk s u)
    (hp : kstPathOpen ω p) (hs : s.1 = -((5*m/4 : ℕ) : ℤ))
    (hu : u.2 = (m : ℤ) ∧ 12*|u.1| ≤ (m : ℤ))
    (hbox : kstPathIn p (-((5*m/4 : ℕ) : ℤ)) ((5*m/4 : ℕ) : ℤ) (-(m : ℤ)) m) :
    latticeConfigurationTranslate (((m/6 : ℕ) : ℤ),0) ω ∈ kstBridge m := by
  have hm12 : m % 12 = 0 := Nat.mod_eq_zero_of_dvd hm
  have huX := abs_le.mp (show |u.1| ≤ ((m/12 : ℕ) : ℤ) by omega)
  let a : LatticeVertex := (((m/6 : ℕ) : ℤ),0)
  let q := p.map (latticeTranslationIso a).toHom
  have hs' : (latticeTranslationIso a s).1 = -((13*m/12 : ℕ) : ℤ) := by
    change s.1+((m/6 : ℕ) : ℤ) = _
    rw [hs]
    omega
  have hu' : kstBridgeRight m (latticeTranslationIso a u) := by
    have hax : |u.1+((m/6 : ℕ) : ℤ)| ≤ ((13*m/12 : ℕ) : ℤ) := by
      rw [abs_le]; constructor <;> omega
    change 12*|u.1+((m/6 : ℕ) : ℤ)| ≤ 13*(m : ℤ) ∧ |u.2+0| ≤ (m : ℤ) ∧
      (m : ℤ) ≤ 12*(u.1+((m/6 : ℕ) : ℤ)) ∧
      (|u.2+0| = (m : ℤ) ∨ u.1+((m/6 : ℕ) : ℤ) = ((13*m/12 : ℕ) : ℤ))
    rw [hu.1,add_zero,abs_of_nonneg (Int.natCast_nonneg m)]
    exact ⟨by omega,le_rfl,by omega,Or.inl (by trivial)⟩
  apply kst_bridge_of_left_side_to_target m hm0 _ q (kstPathOpen_translate a ω p hp) hs' hu'
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  have hb := hbox w hw
  change -((13*m/12 : ℕ) : ℤ) ≤ w.1+((m/6 : ℕ) : ℤ) ∧ |w.2+0| ≤ (m : ℤ)
  exact ⟨by omega,by simpa only [add_zero] using abs_le.mpr hb.2.2⟩

/-- The corresponding right translate, with an actual right-side connection. -/
theorem kst_right_connection_translated_bridge (m : ℕ) (hm : 12 ∣ m) (hm0 : 1 ≤ m)
    (ω : LatticeConfiguration) {s u : LatticeVertex} (p : PD.squareLattice.Walk s u)
    (hp : kstPathOpen ω p) (hs : s.1 = ((5*m/4 : ℕ) : ℤ))
    (hu : u.2 = (m : ℤ) ∧ 12*|u.1| ≤ (m : ℤ))
    (hbox : kstPathIn p (-((5*m/4 : ℕ) : ℤ)) ((5*m/4 : ℕ) : ℤ) (-(m : ℤ)) m) :
    latticeConfigurationTranslate (-((m/6 : ℕ) : ℤ),0) ω ∈ kstBridge m := by
  have hm12 : m % 12 = 0 := Nat.mod_eq_zero_of_dvd hm
  have huX := abs_le.mp (show |u.1| ≤ ((m/12 : ℕ) : ℤ) by omega)
  let a : LatticeVertex := (-((m/6 : ℕ) : ℤ),0)
  let q := p.map (latticeTranslationIso a).toHom
  have hs' : (latticeTranslationIso a s).1 = ((13*m/12 : ℕ) : ℤ) := by
    change s.1+ -((m/6 : ℕ) : ℤ) = _
    rw [hs]
    omega
  have hu' : kstBridgeLeft m (latticeTranslationIso a u) := by
    have hax : |u.1-((m/6 : ℕ) : ℤ)| ≤ ((13*m/12 : ℕ) : ℤ) := by
      rw [abs_le]; constructor <;> omega
    change 12*|u.1+ -((m/6 : ℕ) : ℤ)| ≤ 13*(m : ℤ) ∧ |u.2+0| ≤ (m : ℤ) ∧
      12*(u.1+ -((m/6 : ℕ) : ℤ)) ≤ -(m : ℤ) ∧
      (|u.2+0| = (m : ℤ) ∨ u.1+ -((m/6 : ℕ) : ℤ) = -((13*m/12 : ℕ) : ℤ))
    rw [hu.1,add_zero,abs_of_nonneg (Int.natCast_nonneg m)]
    simp only [← sub_eq_add_neg]
    exact ⟨by omega,le_rfl,by omega,Or.inl (by trivial)⟩
  apply kst_bridge_of_right_side_to_target m hm0 _ q (kstPathOpen_translate a ω p hp) hs' hu'
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  have hb := hbox w hw
  change w.1+ -((m/6 : ℕ) : ℤ) ≤ ((13*m/12 : ℕ) : ℤ) ∧ |w.2+0| ≤ (m : ℤ)
  exact ⟨by omega,by simpa only [add_zero] using abs_le.mpr hb.2.2⟩

end
end PottsContinuity.PlanarTopology
