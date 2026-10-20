module

public import PottsContinuity.PlanarTopology.KSTBridgeIntersection
public import PottsContinuity.PlanarTopology.KSTPartition
public import PottsContinuity.PlanarTopology.SubpathExtraction
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12

private theorem takeUntil_subwalk {u v z : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (hz : z ∈ p.support) :
    (p.takeUntil z hz).IsSubwalk p :=
  SimpleGraph.Walk.isSubwalk_of_append_left (p.take_spec hz).symm

/-- Clip a band-confined open side-to-side walk to a simple KST bridge,
retaining actual open bonds. The larger side coordinate is the literal floor. -/
theorem kst_bridge_of_band_crossing (m : ℕ) (hm : 1 ≤ m)
    (ω : LatticeConfiguration) {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (hpO : kstPathOpen ω p)
    (hu : u.1 = -((5*m/4 : ℕ) : ℤ)) (hv : v.1 = ((5*m/4 : ℕ) : ℤ))
    (hpY : ∀ z ∈ p.support, |z.2| ≤ (m : ℤ)) : ω ∈ kstBridge m := by
  have hstep : ∀ x y, PD.squareLattice.Adj x y → |x.1-y.1| ≤ 1 := by
    intro x y h
    change |x.1-y.1| + |x.2-y.2| = 1 at h
    have := abs_nonneg (x.2-y.2)
    omega
  obtain ⟨x,y,r,hr,hx,hy,hbounds⟩ := walk_subwalk_between_levels
    (fun z : LatticeVertex => z.1) hstep p
    (a := -((13*m/12 : ℕ) : ℤ)) (b := ((13*m/12 : ℕ) : ℤ))
    (by omega) (by rw [hu]; omega) (by rw [hv]; omega)
  let q : PD.squareLattice.Walk x y := r.toPath
  have hqS : q.support ⊆ r.support := r.support_toPath_subset_support
  have hqE : q.edges ⊆ r.edges := r.edges_toPath_subset_edges
  have hqO : kstPathOpen ω q := by
    intro e he
    exact hpO e (hr.edges_subset (hqE he))
  have hqB : ∀ z ∈ q.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ) := by
    intro z hz
    have hb := hbounds z (hqS hz)
    have habs : |z.1| ≤ ((13*m/12 : ℕ) : ℤ) := abs_le.mpr hb
    exact ⟨by omega, hpY z (hr.support_subset (hqS hz))⟩
  refine ⟨x,y,q,r.toPath.property,hqO,?_,?_,hqB⟩
  · have hxy := hqB x q.start_mem_support
    refine ⟨hxy.1,hxy.2,?_,Or.inr hx⟩
    dsimp at hx
    omega
  · have hxy := hqB y q.end_mem_support
    refine ⟨hxy.1,hxy.2,?_,Or.inr hy⟩
    dsimp at hy
    omega

/-- The exact deterministic closing inclusion, used in `BD12.wired_kst_closing`. -/
theorem kst_quasi_closing (m l : ℕ) (hml : l ≤ m) (hl : 1 ≤ l) :
    kstQuasiCrossing m l ∩ kstBridge l ⊆ kstBridge m := by
  classical
  rintro ω ⟨⟨hleft,hright⟩,hbridge⟩
  obtain ⟨a,b,s,p,L,hpM,hpO,hLO,hs,hsY,hLY,hpY⟩ := hleft
  obtain ⟨c,d,t,p',R,hpM',hpO',hRO,ht,htY,hRY,hpY'⟩ := hright
  obtain ⟨u,v,q,hqPath,hqO,hu,hv,hqB⟩ := hbridge
  obtain ⟨zL,hzLp,hzLq⟩ := kst_mpath_bridge_intersect l p q hpM hu hv hqB
  obtain ⟨zR,hzRp,hzRq⟩ := kst_mpath_bridge_intersect l p' q hpM' hu hv hqB
  let pL := p.takeUntil zL hzLp
  let pR := p'.takeUntil zR hzRp
  let qL := q.takeUntil zL hzLq
  let qR := q.takeUntil zR hzRq
  have hpLs : pL.IsSubwalk p := takeUntil_subwalk p hzLp
  have hpRs : pR.IsSubwalk p' := takeUntil_subwalk p' hzRp
  have hqLs : qL.IsSubwalk q := takeUntil_subwalk q hzLq
  have hqRs : qR.IsSubwalk q := takeUntil_subwalk q hzRq
  let W := L.append (pL.append (qL.reverse.append (qR.append (pR.reverse.append R.reverse))))
  have hWO : kstPathOpen ω W := by
    apply kstPathOpen_append L _ hLO
    apply kstPathOpen_append pL _ (kstPathOpen_of_subwalk hpLs hpO)
    apply kstPathOpen_append qL.reverse _
      ((kstPathOpen_reverse_iff ω qL).mpr (kstPathOpen_of_subwalk hqLs hqO))
    apply kstPathOpen_append qR _ (kstPathOpen_of_subwalk hqRs hqO)
    exact kstPathOpen_append pR.reverse R.reverse
      ((kstPathOpen_reverse_iff ω pR).mpr (kstPathOpen_of_subwalk hpRs hpO'))
      ((kstPathOpen_reverse_iff ω R).mpr hRO)
  have hWY : ∀ z ∈ W.support, |z.2| ≤ (m : ℤ) := by
    intro z hz
    simp only [W, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    rcases hz with hz | hz | hz | hz | hz | hz
    · exact (hLY z hz).2
    · exact (hpY z (hpLs.support_subset hz)).2
    · have h := (hqB z (hqLs.support_subset hz)).2
      omega
    · have h := (hqB z (hqRs.support_subset hz)).2
      omega
    · exact (hpY' z (hpRs.support_subset hz)).2
    · exact (hRY z hz).2
  exact kst_bridge_of_band_crossing m (hl.trans hml) ω W hWO hs ht hWY

end PottsContinuity.PlanarTopology
