module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.TopErasure
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.OpenColumnGeometry
public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial
noncomputable section

/-- Union of the actual original clusters meeting the central lower segment. -/
def LowerStripHull (n : ℕ) (t : ℝ) (ω : TiltedConfiguration (2*n) t) :
    Set (tiltedStripVertices (2*n) t) :=
  {z | ∃ k : ℕ, k ≤ n ∧ ∃ u : tiltedStripVertices (2*n) t,
    u.val = (0,(k:ℤ)) ∧ (tiltedOpenGraph (2*n) t ω).Reachable u z}

theorem lowerStripHull_has_no_top (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration (2*n) t)
    (hno : ¬ lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n)
    (z : tiltedStripVertices (2*n) t) (hz : z ∈ LowerStripHull n t ω) :
    ¬ tiltedTop (2*n) t z.val := by
  intro htop
  obtain ⟨k,hk,u,hu,hpath⟩ := hz
  have hc : tiltedConnectedToTop (2*n) t ω (0,(k:ℤ)) := by
    have hmem : (0,(k:ℤ)) ∈ tiltedStripVertices (2*n) t := hu ▸ u.property
    refine ⟨hmem,z,htop,?_⟩
    have heq : (⟨(0,(k:ℤ)),hmem⟩ : tiltedStripVertices (2*n) t) = u := Subtype.ext hu.symm
    exact heq ▸ hpath
  apply hno
  have hf := lowestTopConnectedHeight_le_of_connected (2*n) (by omega) t ω (0,(k:ℤ)) hc
  have hkn : tiltedHeight t (0,(k:ℤ)) ≤ n := by
    simp only [tiltedHeight,Int.cast_natCast,Int.cast_zero,mul_zero,sub_zero]
    exact_mod_cast hk
  exact hf.trans hkn

/-- Such a hull cannot meet any fully open column: every vertex of that
column reaches the top by the original column path. -/
theorem lowerStripHull_avoids_openColumn (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration (2*n) t)
    (hno : ¬ lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n)
    (x : ℤ) (hfull : FullyOpenColumn (2*n) t x ω)
    (z : tiltedStripVertices (2*n) t) (hz : z ∈ LowerStripHull n t ω) : z.val.1 ≠ x := by
  intro hx
  obtain ⟨k,hk,u,hu,hpath⟩ := hz
  obtain ⟨_,v,hv,hzv⟩ := fullyOpenColumn_connectedToTop (2*n) (by omega) t x ω hfull z hx
  have hvh : v ∈ LowerStripHull n t ω := ⟨k,hk,u,hu,hpath.trans hzv⟩
  exact lowerStripHull_has_no_top n hn t ω hno v hvh hv

private theorem strip_open_horizontal_step (N : ℕ) (t : ℝ) (ω : TiltedConfiguration N t)
    (u v : tiltedStripVertices N t) (h : (tiltedOpenGraph N t ω).Adj u v) :
    |u.val.1-v.val.1| ≤ 1 := by
  have hbase := (tiltedOpenGraph_adj_iff N t ω u v).mp h |>.1
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at hbase
  have hnon := abs_nonneg (u.val.2-v.val.2)
  omega

/-- The full lower hull is strictly between any two fully open cutoff columns. -/
theorem lowerStripHull_between_columns (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration (2*n) t)
    (hno : ¬ lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n)
    (xm xp : ℤ) (hm : xm < 0) (hp : 0 < xp)
    (hfm : FullyOpenColumn (2*n) t xm ω) (hfp : FullyOpenColumn (2*n) t xp ω)
    (z : tiltedStripVertices (2*n) t) (hz : z ∈ LowerStripHull n t ω) :
    xm < z.val.1 ∧ z.val.1 < xp := by
  obtain ⟨k,hk,u,hu,⟨p⟩⟩ := hz
  constructor
  · by_contra hbad
    have hstep : ∀ a b, (tiltedOpenGraph (2*n) t ω).Adj a b →
        |(-a.val.1)-(-b.val.1)| ≤ 1 := by
      intro a b hab
      simpa only [neg_sub_neg,abs_sub_comm] using strip_open_horizontal_step (2*n) t ω a b hab
    obtain ⟨w,r,s,hw,_,_⟩ := PlanarTopology.walk_prefix_at_level
      (fun v : tiltedStripVertices (2*n) t => -v.val.1) hstep p (-xm)
      (by simp only [hu]; omega) (by omega)
    have hwh : w ∈ LowerStripHull n t ω := ⟨k,hk,u,hu,r.reachable⟩
    exact lowerStripHull_avoids_openColumn n hn t ω hno xm hfm w hwh (by omega)
  · by_contra hbad
    obtain ⟨w,r,s,hw,_,_⟩ := PlanarTopology.walk_prefix_at_level
      (fun v : tiltedStripVertices (2*n) t => v.val.1)
      (strip_open_horizontal_step (2*n) t ω) p xp
      (by simp only [hu]; omega) (by omega)
    have hwh : w ∈ LowerStripHull n t ω := ⟨k,hk,u,hu,r.reachable⟩
    exact lowerStripHull_avoids_openColumn n hn t ω hno xp hfp w hwh hw

/-- The actual lower hull is finite once open cutoff columns exist and the
half-height event fails. The column window is `Thm3.Touch.tiltedColumnWindow`. -/
theorem lowerStripHull_finite (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (ω : TiltedConfiguration (2*n) t)
    (hno : ¬ lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n)
    (xm xp : ℤ) (hm : xm < 0) (hp : 0 < xp)
    (hfm : FullyOpenColumn (2*n) t xm ω) (hfp : FullyOpenColumn (2*n) t xp ω) :
    (LowerStripHull n t ω).Finite := by
  let M := xm.natAbs+xp.natAbs
  have hxm : -(M:ℤ) ≤ xm := by
    dsimp [M]
    push_cast
    have h := neg_abs_le xm
    have h' := abs_nonneg xp
    omega
  have hxp : xp ≤ (M:ℤ) := by
    dsimp [M]
    push_cast
    have h := le_abs_self xp
    have h' := abs_nonneg xm
    omega
  have hf := (Finset.finite_toSet (Thm3.Touch.tiltedColumnWindow (2*n) M t)).preimage
    (show Set.InjOn (fun z : tiltedStripVertices (2*n) t => z.val) _ from
      Subtype.val_injective.injOn)
  apply hf.subset
  intro z hz
  have hbounds := lowerStripHull_between_columns n hn t ω hno xm xp hm hp hfm hfp z hz
  apply (Thm3.Touch.mem_tiltedColumnWindow_iff (2*n) M t ht z.val).mpr
  exact ⟨z.property,abs_le.mpr ⟨by omega,by omega⟩⟩

theorem lowerStripHull_points_finite (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (ω : TiltedConfiguration (2*n) t)
    (hno : ¬ lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n)
    (xm xp : ℤ) (hm : xm < 0) (hp : 0 < xp)
    (hfm : FullyOpenColumn (2*n) t xm ω) (hfp : FullyOpenColumn (2*n) t xp ω) :
    (Subtype.val '' LowerStripHull n t ω : Set (ℤ × ℤ)).Finite :=
  (lowerStripHull_finite n hn t ht ω hno xm xp hm hp hfm hfp).image _

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
