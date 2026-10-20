module

public import PottsContinuity.PlanarTopology.KSTCascadeConnections
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The exact deterministic cascade inclusion of KST §4.4, used in `BD12.wired_kst_cascade`.
The two preimages are image translations by (-l/6,0) and (l/6,0), respectively.
No corridor or bridge-extraction premise remains. -/
theorem kst_corridor_bridge_inclusion (l k : ℕ)
    (hl : 12 ∣ l) (hk : 12 ∣ k) (hkl : k ≤ l) (hk0 : 1 ≤ k) :
    kstAvoidingPath l k ∩ kstQuasiCrossing l k ⊆
      (latticeConfigurationTranslate (-(-((l/6 : ℕ) : ℤ),0))) ⁻¹' kstBridge l ∪
      (latticeConfigurationTranslate (-(((l/6 : ℕ) : ℤ),0))) ⁻¹' kstBridge l := by
  classical
  rintro ω ⟨⟨u,v,pi,hpi,hpiO,hno⟩,hleft,hright⟩
  obtain ⟨a,b,s,g,L,hg,hgO,hLO,hs,_,hLb,hgb⟩ := hleft
  obtain ⟨c,d,t,g',R,hg',hgO',hRO,ht,_,hRb,hgb'⟩ := hright
  have hl0 : 1 ≤ l := hk0.trans hkl
  have hk12 : 12*(k/12) = k := Nat.mul_div_cancel' hk
  have hlmod : l % 12 = 0 := Nat.mod_eq_zero_of_dvd hl
  have hkmod : k % 12 = 0 := Nat.mod_eq_zero_of_dvd hk
  have hk' : 1 ≤ k/12 := by omega
  have box_of_abs {z : LatticeVertex}
      (hz : 4*|z.1| ≤ 5*(l : ℤ) ∧ |z.2| ≤ (l : ℤ)) :
      -((5*l/4 : ℕ) : ℤ) ≤ z.1 ∧ z.1 ≤ ((5*l/4 : ℕ) : ℤ) ∧
      -(l : ℤ) ≤ z.2 ∧ z.2 ≤ (l : ℤ) := by
    have hx : |z.1| ≤ ((5*l/4 : ℕ) : ℤ) := by omega
    exact ⟨(abs_le.mp hx).1,(abs_le.mp hx).2,(abs_le.mp hz.2).1,(abs_le.mp hz.2).2⟩
  have hLS : kstPathIn L (-((5*l/4 : ℕ) : ℤ)) ((5*l/4 : ℕ) : ℤ) (-(l : ℤ)) l :=
    fun z hz => box_of_abs (hLb z hz)
  have hRS : kstPathIn R (-((5*l/4 : ℕ) : ℤ)) ((5*l/4 : ℕ) : ℤ) (-(l : ℤ)) l :=
    fun z hz => box_of_abs (hRb z hz)
  have hgS : kstPathIn g (-((5*l/4 : ℕ) : ℤ)) ((5*l/4 : ℕ) : ℤ) (-(l : ℤ)) l :=
    fun z hz => box_of_abs (hgb z hz)
  have hgS' : kstPathIn g' (-((5*l/4 : ℕ) : ℤ)) ((5*l/4 : ℕ) : ℤ) (-(l : ℤ)) l :=
    fun z hz => box_of_abs (hgb' z hz)
  have hpS : kstPathIn pi (-((5*l/4 : ℕ) : ℤ)) ((5*l/4 : ℕ) : ℤ) (-(l : ℤ)) l := by
    intro z hz
    have hh := hpi.2.2.2.2.2 z hz
    apply box_of_abs
    exact ⟨by omega,hh.2⟩
  have hg12 : kstMPath (12*(k/12)) g := by rwa [hk12]
  have hg12' : kstMPath (12*(k/12)) g' := by rwa [hk12]
  have hcorr := kst_corridor (k/12) hk'
    (-((5*l/4 : ℕ) : ℤ)) ((5*l/4 : ℕ) : ℤ) (-(l : ℤ)) l
    (by omega) (by omega) (by omega) (by omega)
    g g' L R pi hg12 hg12' hLS hRS hs ht hpi.1 hpS hpi.2.1 hpi.2.2.1
  rcases hcorr with ⟨x,y,q,hq,hsub⟩ | ⟨z,hzp,hz⟩
  · exact False.elim (hno ⟨x,y,q,by rwa [hk12] at hq,hsub⟩)
  · have hu : u.2 = (l : ℤ) ∧ 12*|u.1| ≤ (l : ℤ) := ⟨hpi.2.1,hpi.2.2.2.1⟩
    have left_bridge (hz : z ∈ g.support ∨ z ∈ L.support) :
        latticeConfigurationTranslate (((l/6 : ℕ) : ℤ),0) ω ∈ kstBridge l := by
      obtain ⟨W,hWO,hWS⟩ := kst_wall_contact_connection ω _ _ _ _ g L pi
        hgO hLO hpiO hgS hLS hpS hzp hz
      exact kst_left_connection_translated_bridge l hl hl0 ω W hWO hs hu hWS
    have right_bridge (hz : z ∈ g'.support ∨ z ∈ R.support) :
        latticeConfigurationTranslate (-((l/6 : ℕ) : ℤ),0) ω ∈ kstBridge l := by
      obtain ⟨W,hWO,hWS⟩ := kst_wall_contact_connection ω _ _ _ _ g' R pi
        hgO' hRO hpiO hgS' hRS hpS hzp hz
      exact kst_right_connection_translated_bridge l hl hl0 ω W hWO ht hu hWS
    rcases hz with hz | hz | hz | hz
    · left
      simpa only [Set.mem_preimage,Prod.neg_mk,neg_neg,neg_zero] using left_bridge (Or.inl hz)
    · right
      simpa only [Set.mem_preimage,Prod.neg_mk,neg_zero] using right_bridge (Or.inl hz)
    · left
      simpa only [Set.mem_preimage,Prod.neg_mk,neg_neg,neg_zero] using left_bridge (Or.inr hz)
    · right
      simpa only [Set.mem_preimage,Prod.neg_mk,neg_zero] using right_bridge (Or.inr hz)

end
end PottsContinuity.PlanarTopology
