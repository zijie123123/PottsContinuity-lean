module

public import PottsContinuity.PlanarTopology.KSTArmTranslation
public import PottsContinuity.PlanarTopology.KSTFunnelAttachment
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Int.Star

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The two short shifted arms and the long upper arm of KST §4.3 construct an
actual open m-path attached to the top of V. Here m=192n; every translation and
target width is checked by integer inequalities, including the long arm's
half-integer nominal width. The connector uses only the three original arms. -/
theorem kst_three_arms_top_attachment (n : ℕ) (hn : 1 ≤ n) (ω : LatticeConfiguration)
    (hleft : ω ∈ (latticeConfigurationTranslate (-(-12*(n : ℤ),0))) ⁻¹' kstArm (192*n))
    (hright : ω ∈ (latticeConfigurationTranslate (-(12*(n : ℤ),0))) ⁻¹' kstArm (192*n))
    (hupper : ω ∈ (latticeConfigurationTranslate (-(0,288*(n : ℤ)))) ⁻¹' kstArm (480*n)) :
    ∃ (x y z : LatticeVertex) (g : PD.squareLattice.Walk x y) (C : PD.squareLattice.Walk z x),
      kstMPath (192*n) g ∧ kstPathOpen ω g ∧ kstPathOpen ω C ∧
      z.2 = 768*(n : ℤ) ∧
      ∀ w ∈ C.support, |w.1| ≤ 528*(n : ℤ) ∧
        -192*(n : ℤ) ≤ w.2 ∧ w.2 ≤ 768*(n : ℤ) := by
  obtain ⟨l₁,l₂,L,hL,hLO,hLx,hLx',_⟩ := kst_translated_arm_mpath (192*n)
    (-12*(n : ℤ)) (by rw [neg_mul,abs_neg,abs_of_nonneg (by positivity)]; push_cast; omega) ω hleft
  obtain ⟨r₁,r₂,R,hR,hRO,hRx,hRx',_⟩ := kst_translated_arm_mpath (192*n)
    (12*(n : ℤ)) (by rw [abs_of_nonneg (by positivity)]; push_cast; omega) ω hright
  obtain ⟨u,v,p,hp,hpO,hu,hv,_,hvx,hbox⟩ := kst_translated_arm_witness (480*n)
    (0,288*(n : ℤ)) ω hupper
  simp only [sub_zero,Nat.cast_mul,Nat.cast_ofNat] at hLx hLx' hRx hRx' hu hv hvx hbox
  have hscale : 12*(16*n) = 192*n := by omega
  have small_bounds (g₁ : LatticeVertex) (hh : 64*|g₁.1+12*(n : ℤ)| ≤ 192*(n : ℤ)) :
      -16*(n : ℤ) ≤ g₁.1 ∧ g₁.1 ≤ -9*(n : ℤ) := by
    have ha : |g₁.1+12*(n : ℤ)| ≤ 3*(n : ℤ) := by omega
    have hb := abs_le.mp ha
    omega
  have small_bounds' (g₁ : LatticeVertex) (hh : 64*|g₁.1-12*(n : ℤ)| ≤ 192*(n : ℤ)) :
      9*(n : ℤ) ≤ g₁.1 ∧ g₁.1 ≤ 16*(n : ℤ) := by
    have ha : |g₁.1-12*(n : ℤ)| ≤ 3*(n : ℤ) := by omega
    have hb := abs_le.mp ha
    omega
  have hLeft : kstMPath (12*(16*n)) L := by rwa [hscale]
  have hRight : kstMPath (12*(16*n)) R := by rwa [hscale]
  have hv' : v.2 = -12*((16*n : ℕ) : ℤ) ∧
      -(9*(n : ℤ)) ≤ v.1 ∧ v.1 ≤ 9*(n : ℤ) := by
    have hh : |v.1| ≤ 9*(n : ℤ) := by omega
    have hb := abs_le.mp hh
    push_cast
    exact ⟨by omega,hb⟩
  have hlow : ∀ w ∈ p.support, -12*((16*n : ℕ) : ℤ) ≤ w.2 := by
    intro w hw
    have hh := abs_le.mp (hbox w hw).2
    push_cast
    omega
  obtain ⟨x,y,g,C,hg,hgO,hCO,_,hCS⟩ := kst_mpath_attached_of_funnel (16*n) (by omega)
    (9*(n : ℤ)) (by push_cast; constructor <;> omega) ω L R p hLeft hRight hLO hRO hpO
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul,sub_neg_eq_add] using small_bounds l₁ (by simpa only [neg_mul,sub_neg_eq_add] using hLx))
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat,neg_mul,sub_neg_eq_add] using small_bounds l₂ (by simpa only [neg_mul,sub_neg_eq_add] using hLx'))
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using small_bounds' r₁ hRx)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using small_bounds' r₂ hRx')
    hp hv' (by push_cast; omega) hlow
  refine ⟨x,y,u,g,C,by rwa [hscale] at hg,hgO,hCO,by omega,?_⟩
  have short_bounds {a b : LatticeVertex} (q : PD.squareLattice.Walk a b)
      (hq : kstMPath (192*n) q) (w : LatticeVertex) (hw : w ∈ q.support) :
      |w.1| ≤ 528*(n : ℤ) ∧ -192*(n : ℤ) ≤ w.2 ∧ w.2 ≤ 768*(n : ℤ) := by
    have hh := hq.2.2.2.2.2 w hw
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
    have hy := abs_le.mp hh.2
    omega
  intro w hw
  rcases hCS w hw with hw | hw | hw
  · have hh := hbox w hw
    have hy := abs_le.mp hh.2
    omega
  · exact short_bounds L hL w hw
  · exact short_bounds R hR w hw

end
end PottsContinuity.PlanarTopology
