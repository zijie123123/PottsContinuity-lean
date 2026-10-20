module

public import PottsContinuity.PlanarTopology.AlphaCoreBottomEvent
public import PottsContinuity.PlanarTopology.AlphaCoreReflections

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- A connection from the exact left three-piece core target to bottom right. -/
def alphaCoreToBottom (k : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u v, ∃ p : PD.squareLattice.Walk u v,
    kstPathOpen ω p ∧ u ∈ alphaCoreLeftTargets k ∧ v ∈ alphaCoreRightTargets k ∧
    v.2 = -64*(k : ℤ) ∧
    kstPathIn p (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1)}

theorem alphaCoreToBottom_isUpperSet (k : ℕ) : IsUpperSet (alphaCoreToBottom k) := by
  rintro ω η hωη ⟨u,v,p,hp,hrest⟩
  exact ⟨u,v,p,kstPathOpen_mono hωη p hp,hrest⟩

theorem alphaCoreToBottom_isCylinder (k : ℕ) : PD.RCInfinite.IsCylinder (alphaCoreToBottom k) := by
  classical
  let S := PD.FK.latticeRectangle (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)
  let F : Finset PD.squareLattice.edgeSet := Finset.univ.map (frozenEdgeEmbedding S)
  have confined {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
      (hp : kstPathIn p (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1)) :
      ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hh := hp z hz
    apply (mem_latticeRectangle _ _ _ _).mpr
    push_cast
    exact ⟨⟨hh.1,by omega⟩,hh.2.2.1,by omega⟩
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

/-- Reflected side-to-bottom connections meet on their original supports. -/
theorem alpha_core_to_bottom_reflected_glue (k : ℕ) (hk : 1 ≤ k) :
    alphaCoreToBottom k ∩
      latticeConfigurationIsoHomeomorph alphaCoreReflectionXIso ⁻¹' alphaCoreToBottom k ⊆
        alphaCoreBottomArc k := by
  rintro ω ⟨⟨u,v,p,hp,hu,hv,hvy,hpB⟩,⟨s,t,r,hr,hs,ht,hty,hrB⟩⟩
  let R := r.map alphaCoreReflectionXIso.symm.toHom
  let q := R.reverse
  have hq : kstPathOpen ω q := (kstPathOpen_reverse_iff ω R).mpr
    (kstPathOpen_map_iso_inverse alphaCoreReflectionXIso ω r hr)
  have hx : alphaCoreReflectionXIso.symm t ∈ alphaCoreLeftTargets k :=
    (alphaCoreLeftTargets_x_reflection k t).mpr ht
  have hy : alphaCoreReflectionXIso.symm s ∈ alphaCoreRightTargets k :=
    (alphaCoreRightTargets_x_reflection k s).mpr hs
  have hxy : (alphaCoreReflectionXIso.symm t).2 = -64*(k : ℤ) := by
    change t.2-0 = _
    omega
  have hqB : kstPathIn q (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1) := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse,SimpleGraph.Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact (alphaCoreReflectionXIso_bounds k w).mpr (hrB w hw)
  by_cases huBottom : u.2 = -64*(k : ℤ)
  · exact ⟨u,v,p,hp,huBottom,hvy,hu.1.2,hv.1.1,hpB⟩
  by_cases hyBottom : (alphaCoreReflectionXIso.symm s).2 = -64*(k : ℤ)
  · exact ⟨_,_,q,hq,hxy,hyBottom,hx.1.2,hy.1.1,hqB⟩
  obtain ⟨z,hzp,hzq⟩ := opposed_boundary_bottom_walks_intersect
    (-65*(k : ℤ)) (65*(k : ℤ)-1) (-64*(k : ℤ)) (64*(k : ℤ)-1) (-(k : ℤ)-1) (k : ℤ)
    (by omega) p q hpB hqB ⟨hu.1.2,hu.2.2⟩ ⟨hy.1.1,hy.2.2⟩
    hvy hxy hv.1.1 hx.1.2 huBottom hyBottom
  let Q := q.takeUntil z hzq
  let P := p.dropUntil z hzp
  have hQ := q.isSubwalk_takeUntil hzq
  have hP := p.isSubwalk_dropUntil hzp
  refine ⟨_,_,Q.append P,kstPathOpen_append Q P
    (kstPathOpen_of_subwalk hQ hq) (kstPathOpen_of_subwalk hP hp),hxy,hvy,hx.1.2,hv.1.1,?_⟩
  intro w hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw | hw
  · exact hqB w (hQ.support_subset hw)
  · exact hpB w (hP.support_subset hw)

end
end PottsContinuity.PlanarTopology
