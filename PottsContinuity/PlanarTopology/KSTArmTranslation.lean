module

public import PottsContinuity.PlanarTopology.KSTSideBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- An open walk in the inverse-translated configuration becomes a walk open
in the ORIGINAL configuration after translating its vertices forward. -/
theorem kstPathOpen_translate_from_preimage (a : LatticeVertex) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen (latticeConfigurationTranslate (-a) ω) p) :
    kstPathOpen ω (p.map (latticeTranslationIso a).toHom) := by
  intro e he
  rw [SimpleGraph.Walk.edges_map] at he
  obtain ⟨f,hf,hfe⟩ := List.mem_map.mp he
  let f' : PD.squareLattice.edgeSet := ⟨f,p.edges_subset_edgeSet hf⟩
  have he' : e = (latticeTranslationIso a).mapEdgeSet f' := Subtype.ext hfe.symm
  rw [he']
  have hh := hp f' hf
  rw [latticeConfigurationTranslate_apply] at hh
  simpa only [neg_neg] using hh

/-- Exact actual-walk witnesses for the image translate of a KST arm event.
The endpoint targets and every support coordinate are translated literally. -/
theorem kst_translated_arm_witness (m : ℕ) (a : LatticeVertex) (ω : LatticeConfiguration)
    (hω : ω ∈ (latticeConfigurationTranslate (-a)) ⁻¹' kstArm m) :
    ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
      p.IsPath ∧ kstPathOpen ω p ∧
      u.2 = a.2+(m : ℤ) ∧ v.2 = a.2-(m : ℤ) ∧
      64*|u.1-a.1| ≤ (m : ℤ) ∧ 64*|v.1-a.1| ≤ (m : ℤ) ∧
      ∀ z ∈ p.support, 64*|z.1-a.1| ≤ 65*(m : ℤ) ∧ |z.2-a.2| ≤ (m : ℤ) := by
  obtain ⟨u,v,p,hp,hpO,hu,hv,hux,hvx,hbox⟩ := hω
  refine ⟨latticeTranslationIso a u,latticeTranslationIso a v,
    p.map (latticeTranslationIso a).toHom,
    hp.map (latticeTranslationIso a).injective,
    kstPathOpen_translate_from_preimage a ω p hpO,?_,?_,?_,?_,?_⟩
  · change u.2+a.2 = a.2+(m : ℤ)
    omega
  · change v.2+a.2 = a.2-(m : ℤ)
    omega
  · change 64*|u.1+a.1-a.1| ≤ (m : ℤ)
    simpa only [add_sub_cancel_right] using hux
  · change 64*|v.1+a.1-a.1| ≤ (m : ℤ)
    simpa only [add_sub_cancel_right] using hvx
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change 64*|w.1+a.1-a.1| ≤ 65*(m : ℤ) ∧ |w.2+a.2-a.2| ≤ (m : ℤ)
    simpa only [add_sub_cancel_right] using hbox w hw

/-- An arm shifted horizontally by at most m/16 is still an m-path. The
original narrow shifted target bounds are retained for the funnel construction.
This is the source's 5α ≤ β check, with exact integer inequalities. -/
theorem kst_translated_arm_mpath (m : ℕ) (a : ℤ) (ha : 16*|a| ≤ (m : ℤ))
    (ω : LatticeConfiguration)
    (hω : ω ∈ (latticeConfigurationTranslate (-(a,0))) ⁻¹' kstArm m) :
    ∃ (u v : LatticeVertex) (p : PD.squareLattice.Walk u v),
      kstMPath m p ∧ kstPathOpen ω p ∧
      64*|u.1-a| ≤ (m : ℤ) ∧ 64*|v.1-a| ≤ (m : ℤ) ∧
      ∀ z ∈ p.support, 64*|z.1-a| ≤ 65*(m : ℤ) ∧ |z.2| ≤ (m : ℤ) := by
  obtain ⟨u,v,p,hp,hpO,hu,hv,hux,hvx,hbox⟩ := kst_translated_arm_witness m (a,0) ω hω
  simp only [zero_add,zero_sub,sub_zero] at hu hv hux hvx hbox
  have triangle (x : ℤ) : |x| ≤ |x-a|+|a| := by
    simpa only [sub_add_cancel] using abs_add_le (x-a) a
  have huBound := triangle u.1
  have hvBound := triangle v.1
  refine ⟨u,v,p,⟨hp,hu,hv,by omega,by omega,?_⟩,hpO,hux,hvx,hbox⟩
  intro z hz
  have hh := hbox z hz
  have hzBound := triangle z.1
  exact ⟨by omega,hh.2⟩

end
end PottsContinuity.PlanarTopology
