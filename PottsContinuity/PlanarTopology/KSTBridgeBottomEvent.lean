module

public import PottsContinuity.PlanarTopology.KSTBetaBottomEvent
public import PottsContinuity.PlanarTopology.OpposedBottomPaths
public import PottsContinuity.Infinite.Symmetry

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- Reuse the shared infinite-library's actual horizontal-coordinate reflection. -/
abbrev kstReflectionXIso : PD.squareLattice ≃g PD.squareLattice :=
  Infinite.latticeReflectionIso

/-- The beta-target source event E: left bridge boundary to bottom-right target. -/
def kstBridgeToBottom (m : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u v, ∃ p : PD.squareLattice.Walk u v,
    kstPathOpen ω p ∧ kstBridgeLeft m u ∧ kstBridgeRight m v ∧ v.2 = -(m : ℤ) ∧
    ∀ z ∈ p.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)}

theorem kstBridgeToBottom_isUpperSet (m : ℕ) : IsUpperSet (kstBridgeToBottom m) := by
  rintro ω η hωη ⟨u,v,p,hp,hrest⟩
  exact ⟨u,v,p,kstPathOpen_mono hωη p hp,hrest⟩

theorem kstBridgeToBottom_isCylinder (m : ℕ) : PD.RCInfinite.IsCylinder (kstBridgeToBottom m) := by
  classical
  let S := latticeBox (0,0) (13*m)
  let F : Finset PD.squareLattice.edgeSet := Finset.univ.map (frozenEdgeEmbedding S)
  have confined {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
      (hp : ∀ z ∈ p.support, 12*|z.1| ≤ 13*(m : ℤ) ∧ |z.2| ≤ (m : ℤ)) :
      ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hh := hp z hz
    have hax := abs_nonneg z.1
    have hbx := abs_le.mp (show |z.1| ≤ 13*(m : ℤ) by omega)
    have hby := abs_le.mp hh.2
    apply (mem_latticeBox (0,0) z (13*m)).mpr
    push_cast
    exact ⟨⟨by omega,by omega⟩,by omega,by omega⟩
  refine ⟨F,?_⟩
  intro ω η hωη
  have hagree : ∀ f : (PD.squareLattice.induce (S : Set LatticeVertex)).edgeSet,
      ω (frozenEdgeEmbedding S f) = η (frozenEdgeEmbedding S f) := by
    intro f
    exact hωη _ (Finset.mem_map.mpr ⟨f,Finset.mem_univ _,rfl⟩)
  constructor <;> rintro ⟨u,v,p,hp,hu,hv,hvy,hB⟩
  · exact ⟨u,v,p,(kstPathOpen_congr_on_domain S p (confined p hB) ω η hagree).mp hp,
      hu,hv,hvy,hB⟩
  · exact ⟨u,v,p,(kstPathOpen_congr_on_domain S p (confined p hB) ω η hagree).mpr hp,
      hu,hv,hvy,hB⟩

/-- Reflection exchanges the literal three-piece bridge targets. -/
theorem kstBridgeLeft_reflection_iff (m : ℕ) (u : LatticeVertex) :
    kstBridgeRight m (kstReflectionXIso.symm u) ↔ kstBridgeLeft m u := by
  change (12*|-u.1| ≤ 13*(m : ℤ) ∧ |u.2| ≤ (m : ℤ) ∧
    (m : ℤ) ≤ 12*(-u.1) ∧ (|u.2| = (m : ℤ) ∨ -u.1 = ((13*m/12 : ℕ) : ℤ))) ↔ _
  simp only [abs_neg,kstBridgeLeft]
  omega

theorem kstBridgeRight_reflection_iff (m : ℕ) (u : LatticeVertex) :
    kstBridgeLeft m (kstReflectionXIso.symm u) ↔ kstBridgeRight m u := by
  change (12*|-u.1| ≤ 13*(m : ℤ) ∧ |u.2| ≤ (m : ℤ) ∧
    12*(-u.1) ≤ -(m : ℤ) ∧ (|u.2| = (m : ℤ) ∨ -u.1 = -((13*m/12 : ℕ) : ℤ))) ↔ _
  simp only [abs_neg,kstBridgeRight]
  omega

/-- A source E connection and its reflected copy force the beta bottom-arc
connection. All contacts and all output bonds belong to the original walks. -/
theorem kst_bridge_to_bottom_reflected_glue (a : ℕ) (ha : 1 ≤ a) :
    kstBridgeToBottom (12*a) ∩
      latticeConfigurationIsoHomeomorph kstReflectionXIso ⁻¹' kstBridgeToBottom (12*a) ⊆
        kstBetaBottomArc (12*a) := by
  rintro ω ⟨⟨u,v,p,hp,hu,hv,hvy,hpB⟩,⟨s,t,r,hr,hs,ht,hty,hrB⟩⟩
  let R := r.map kstReflectionXIso.symm.toHom
  let q := R.reverse
  have hq : kstPathOpen ω q := (kstPathOpen_reverse_iff ω R).mpr
    (kstPathOpen_map_iso_inverse kstReflectionXIso ω r hr)
  have hx : kstBridgeLeft (12*a) (kstReflectionXIso.symm t) :=
    (kstBridgeRight_reflection_iff (12*a) t).mpr ht
  have hy : kstBridgeRight (12*a) (kstReflectionXIso.symm s) :=
    (kstBridgeLeft_reflection_iff (12*a) s).mpr hs
  have hxy : (kstReflectionXIso.symm t).2 = -((12*a : ℕ) : ℤ) := hty
  have hqB : ∀ z ∈ q.support, 12*|z.1| ≤ 13*((12*a : ℕ) : ℤ) ∧ |z.2| ≤ ((12*a : ℕ) : ℤ) := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse,SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    change 12*|-w.1| ≤ 13*((12*a : ℕ) : ℤ) ∧ |w.2| ≤ ((12*a : ℕ) : ℤ)
    simpa only [abs_neg] using hrB w hw
  by_cases huBottom : u.2 = -((12*a : ℕ) : ℤ)
  · exact ⟨u,v,p,hp,huBottom,hvy,hu.2.2.1,hv.2.2.1,hpB⟩
  by_cases hyBottom : (kstReflectionXIso.symm s).2 = -((12*a : ℕ) : ℤ)
  · exact ⟨_,_,q,hq,hxy,hyBottom,hx.2.2.1,hy.2.2.1,hqB⟩
  have box {x y : LatticeVertex} (P : PD.squareLattice.Walk x y)
      (hB : ∀ z ∈ P.support, 12*|z.1| ≤ 13*((12*a : ℕ) : ℤ) ∧ |z.2| ≤ ((12*a : ℕ) : ℤ)) :
      kstPathIn P (-13*(a : ℤ)) (13*(a : ℤ)) (-12*(a : ℤ)) (12*(a : ℤ)) := by
    intro z hz
    have hh := hB z hz
    push_cast at hh
    have hax := abs_nonneg z.1
    have hxb := abs_le.mp (show |z.1| ≤ 13*(a : ℤ) by omega)
    have hyb := abs_le.mp hh.2
    omega
  have hdiv : 13*(12*a)/12 = 13*a := by omega
  have left_target (z : LatticeVertex) (h : kstBridgeLeft (12*a) z) :
      z.1 ≤ -(a : ℤ) ∧ (z.1 = -13*(a : ℤ) ∨ z.2 = -12*(a : ℤ) ∨ z.2 = 12*(a : ℤ)) := by
    unfold kstBridgeLeft at h
    rw [hdiv] at h
    push_cast at h
    rcases h.2.2.2 with hy | hx
    · by_cases hz : 0 ≤ z.2
      · rw [abs_of_nonneg hz] at hy
        omega
      · rw [abs_of_neg (by omega : z.2 < 0)] at hy
        omega
    · omega
  have right_target (z : LatticeVertex) (h : kstBridgeRight (12*a) z) :
      (a : ℤ) ≤ z.1 ∧ (z.1 = 13*(a : ℤ) ∨ z.2 = -12*(a : ℤ) ∨ z.2 = 12*(a : ℤ)) := by
    unfold kstBridgeRight at h
    rw [hdiv] at h
    push_cast at h
    rcases h.2.2.2 with hy | hx
    · by_cases hz : 0 ≤ z.2
      · rw [abs_of_nonneg hz] at hy
        omega
      · rw [abs_of_neg (by omega : z.2 < 0)] at hy
        omega
    · omega
  obtain ⟨z,hzp,hzq⟩ := opposed_boundary_bottom_walks_intersect
    (-13*(a : ℤ)) (13*(a : ℤ)) (-12*(a : ℤ)) (12*(a : ℤ)) (-(a : ℤ)) (a : ℤ)
    (by omega) p q (box p hpB) (box q hqB) (left_target u hu) (right_target _ hy)
    (by push_cast at hvy; exact hvy) (by push_cast at hxy; exact hxy)
    (right_target v hv).1 (left_target _ hx).1
    (by push_cast at huBottom; exact huBottom) (by push_cast at hyBottom; exact hyBottom)
  let Q := q.takeUntil z hzq
  let P := p.dropUntil z hzp
  have hQ := q.isSubwalk_takeUntil hzq
  have hP := p.isSubwalk_dropUntil hzp
  refine ⟨_,_,Q.append P,kstPathOpen_append Q P
    (kstPathOpen_of_subwalk hQ hq) (kstPathOpen_of_subwalk hP hp),hxy,hvy,hx.2.2.1,hv.2.2.1,?_⟩
  intro w hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw | hw
  · exact hqB w (hQ.support_subset hw)
  · exact hpB w (hP.support_subset hw)

end
end PottsContinuity.PlanarTopology
