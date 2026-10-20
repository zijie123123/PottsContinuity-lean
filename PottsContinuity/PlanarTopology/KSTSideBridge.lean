module

public import PottsContinuity.PlanarTopology.KSTClosing
public import PottsContinuity.PD.Duality.BoxDihedral
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- An original open walk remains open after transporting both its vertices
and the entire configuration by a lattice graph isomorphism. -/
theorem kstPathOpen_map_iso (e : PD.squareLattice ≃g PD.squareLattice)
    (ω : LatticeConfiguration) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen ω p) :
    kstPathOpen (latticeConfigurationIsoHomeomorph e ω) (p.map e.toHom) := by
  intro f hf
  rw [SimpleGraph.Walk.edges_map] at hf
  obtain ⟨g,hg,hgf⟩ := List.mem_map.mp hf
  let g' : PD.squareLattice.edgeSet := ⟨g,p.edges_subset_edgeSet hg⟩
  have hf' : f = e.mapEdgeSet g' := Subtype.ext hgf.symm
  rw [hf']
  have hi : e.symm.mapEdgeSet (e.mapEdgeSet g') = g' := by
    apply Subtype.ext
    change Sym2.map e.symm (Sym2.map e g'.val) = g'.val
    rw [Sym2.map_map]
    have hf : (fun z => e.symm (e z)) = id := by funext z; exact e.symm_apply_apply z
    change Sym2.map (fun z => e.symm (e z)) g'.val = g'.val
    rw [hf,Sym2.map_id]
    rfl
  rw [latticeConfigurationIsoHomeomorph_apply,hi]
  exact hp g' hg

/-- The same transport in the exact translation convention of the KST events. -/
theorem kstPathOpen_translate (a : LatticeVertex) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v) (hp : kstPathOpen ω p) :
    kstPathOpen (latticeConfigurationTranslate a ω) (p.map (latticeTranslationIso a).toHom) :=
  kstPathOpen_map_iso (latticeTranslationIso a) ω p hp

/-- Loop erasure of an honest open target-to-target walk yields a KST bridge. -/
theorem kst_bridge_of_walk_bounds (m : ℕ) (ω : LatticeConfiguration)
    {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen ω p) (hu : kstBridgeLeft m u) (hv : kstBridgeRight m v)
    (hb : ∀ z ∈ p.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)) :
    ω ∈ kstBridge m := by
  refine ⟨u,v,p.toPath,p.toPath.property,?_,hu,hv,?_⟩
  · intro e he
    exact hp e (p.edges_toPath_subset_edges he)
  · intro z hz
    exact hb z (p.support_toPath_subset_support hz)

/-- A band-confined open walk from the true left side to a right bridge target
already forces a bridge. It may leave the bridge box to the RIGHT; the proof
clips at the first intervening right-side level. -/
theorem kst_bridge_of_left_side_to_target (m : ℕ) (hm : 1 ≤ m)
    (ω : LatticeConfiguration) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen ω p) (hu : u.1 = -((13*m/12 : ℕ) : ℤ))
    (hv : kstBridgeRight m v)
    (hb : ∀ z ∈ p.support, -((13*m/12 : ℕ) : ℤ) ≤ z.1 ∧ |z.2| ≤ (m : ℤ)) :
    ω ∈ kstBridge m := by
  classical
  have left_target : kstBridgeLeft m u := by
    have h := hb u p.start_mem_support
    refine ⟨?_,h.2,?_,Or.inr hu⟩
    · rw [hu,abs_neg,abs_of_nonneg (by positivity)]
      omega
    · rw [hu]; omega
  by_cases hupper : ∀ z ∈ p.support, z.1 ≤ ((13*m/12 : ℕ) : ℤ)
  · apply kst_bridge_of_walk_bounds m ω p hp left_target hv
    intro z hz
    have h := hb z hz
    have ha : |z.1| ≤ ((13*m/12 : ℕ) : ℤ) := abs_le.mpr ⟨h.1,hupper z hz⟩
    exact ⟨by omega,h.2⟩
  · push Not at hupper
    obtain ⟨z,hz,hzx⟩ := hupper
    let lead := p.takeUntil z hz
    have hlead : lead.IsSubwalk p :=
      SimpleGraph.Walk.isSubwalk_of_append_left (p.take_spec hz).symm
    have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
      intro x y hxy
      change |x.1-y.1|+|x.2-y.2| = 1 at hxy
      have := abs_nonneg (x.2-y.2)
      omega
    obtain ⟨w,r,s,hw,he,hr⟩ := walk_prefix_at_level
      (fun z : LatticeVertex => z.1) hstep lead ((13*m/12 : ℕ) : ℤ)
      (by rw [hu]; omega) (by omega)
    have hrp : r.IsSubwalk p := (SimpleGraph.Walk.isSubwalk_of_append_left he).trans hlead
    have hbound : ∀ z ∈ r.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ) := by
      intro z hz
      have hh := hb z (hrp.support_subset hz)
      have ha : |z.1| ≤ ((13*m/12 : ℕ) : ℤ) := abs_le.mpr ⟨hh.1,hr z hz⟩
      exact ⟨by omega,hh.2⟩
    apply kst_bridge_of_walk_bounds m ω r (kstPathOpen_of_subwalk hrp hp) left_target _ hbound
    have hh := hbound w r.end_mem_support
    exact ⟨hh.1,hh.2,by rw [hw]; omega,Or.inr hw⟩

/-- The reflected side-to-target extraction, with the resulting bridge oriented
from its left target to its right target. -/
theorem kst_bridge_of_right_side_to_target (m : ℕ) (hm : 1 ≤ m)
    (ω : LatticeConfiguration) {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : kstPathOpen ω p) (hu : u.1 = ((13*m/12 : ℕ) : ℤ))
    (hv : kstBridgeLeft m v)
    (hb : ∀ z ∈ p.support, z.1 ≤ ((13*m/12 : ℕ) : ℤ) ∧ |z.2| ≤ (m : ℤ)) :
    ω ∈ kstBridge m := by
  classical
  have right_target : kstBridgeRight m u := by
    have h := hb u p.start_mem_support
    refine ⟨?_,h.2,?_,Or.inr hu⟩
    · rw [hu,abs_of_nonneg (by positivity)]
      omega
    · rw [hu]; omega
  by_cases hlower : ∀ z ∈ p.support, -((13*m/12 : ℕ) : ℤ) ≤ z.1
  · apply kst_bridge_of_walk_bounds m ω p.reverse
      ((kstPathOpen_reverse_iff ω p).mpr hp) hv right_target
    intro z hz
    have hz' : z ∈ p.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
    have h := hb z hz'
    have ha : |z.1| ≤ ((13*m/12 : ℕ) : ℤ) := abs_le.mpr ⟨hlower z hz',h.1⟩
    exact ⟨by omega,h.2⟩
  · push Not at hlower
    obtain ⟨z,hz,hzx⟩ := hlower
    let lead := p.takeUntil z hz
    have hlead : lead.IsSubwalk p :=
      SimpleGraph.Walk.isSubwalk_of_append_left (p.take_spec hz).symm
    have hstep : ∀ x y, PD.squareLattice.Adj x y → |(-x.1)-(-y.1)| ≤ 1 := by
      intro x y hxy
      change |x.1-y.1|+|x.2-y.2| = 1 at hxy
      rw [neg_sub_neg,abs_sub_comm]
      have := abs_nonneg (x.2-y.2)
      omega
    obtain ⟨w,r,s,hw,he,hr⟩ := walk_prefix_at_level
      (fun z : LatticeVertex => -z.1) hstep lead ((13*m/12 : ℕ) : ℤ)
      (by rw [hu]; omega) (by omega)
    have hrp : r.IsSubwalk p := (SimpleGraph.Walk.isSubwalk_of_append_left he).trans hlead
    have hbound : ∀ z ∈ r.reverse.support,
        12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ) := by
      intro z hz
      have hz' : z ∈ r.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
      have hh := hb z (hrp.support_subset hz')
      have ha : |z.1| ≤ ((13*m/12 : ℕ) : ℤ) := abs_le.mpr ⟨by have := hr z hz'; omega,hh.1⟩
      exact ⟨by omega,hh.2⟩
    apply kst_bridge_of_walk_bounds m ω r.reverse
      ((kstPathOpen_reverse_iff ω r).mpr (kstPathOpen_of_subwalk hrp hp)) _ right_target hbound
    have hh := hbound w r.reverse.start_mem_support
    exact ⟨hh.1,hh.2,by dsimp at hw; omega,Or.inr (by dsimp at hw; omega)⟩

end
end PottsContinuity.PlanarTopology
