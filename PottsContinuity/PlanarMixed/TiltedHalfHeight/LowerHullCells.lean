module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.LowerHullConfinement
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial
noncomputable section

/-- Membership transfer between the finite planar hull and its original strip vertices. -/
theorem lowerHull_coe_mem_iff (n : ℕ) (t : ℝ) (ω : TiltedConfiguration (2*n) t)
    (C : Finset LatticeVertex) (hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω)
    (z : tiltedStripVertices (2*n) t) : z.val ∈ C ↔ z ∈ LowerStripHull n t ω := by
  change z.val ∈ (C : Set LatticeVertex) ↔ _
  rw [hC]
  constructor
  · rintro ⟨w,hw,he⟩
    have heq : w=z := Subtype.ext he
    exact heq ▸ hw
  · exact fun hz => ⟨z,hz,rfl⟩

theorem lowerHull_mem_strip (n : ℕ) (t : ℝ) (ω : TiltedConfiguration (2*n) t)
    (C : Finset LatticeVertex) (hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω)
    {z : LatticeVertex} (hz : z ∈ C) : z ∈ tiltedStripVertices (2*n) t := by
  have hz' : z ∈ (C : Set LatticeVertex) := hz
  rw [hC] at hz'
  obtain ⟨w,_,rfl⟩ := hz'
  exact w.property

theorem lowerHull_core_mem (n : ℕ) (t : ℝ) (ω : TiltedConfiguration (2*n) t)
    (C : Finset LatticeVertex) (hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω)
    (k : ℕ) (hk : k ≤ n) : (0,(k:ℤ)) ∈ C := by
  have hstrip : (0,(k:ℤ)) ∈ tiltedStripVertices (2*n) t := by
    simp only [tiltedStripVertices,Set.mem_ofPred_eq,tiltedHeight,Int.cast_zero,
      Int.cast_natCast,mul_zero,sub_zero]
    constructor
    · positivity
    · exact_mod_cast (show k ≤ 2*n by omega)
  apply (lowerHull_coe_mem_iff n t ω C hC ⟨(0,(k:ℤ)),hstrip⟩).mpr
  exact ⟨k,hk,⟨(0,(k:ℤ)),hstrip⟩,rfl,.refl _⟩

theorem lowerHull_points_not_top (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) (ω : TiltedConfiguration (2*n) t)
    (hno : ¬ lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n)
    (C : Finset LatticeVertex) (hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω) :
    ∀ z ∈ C, tiltedHeight t z ≤ (2*n : ℕ)-1 := by
  intro z hz
  let v : tiltedStripVertices (2*n) t := ⟨z,lowerHull_mem_strip n t ω C hC hz⟩
  have hv := (lowerHull_coe_mem_iff n t ω C hC v).mp hz
  have h := lowerStripHull_has_no_top n hn t ω hno v hv
  rw [tiltedTop_iff_height (2*n) ht,not_lt] at h
  change tiltedHeight t z + 1 ≤ ((2*n:ℕ):ℝ) at h
  linarith

/-- Actual open strip edges cannot cross the hull boundary. -/
theorem lowerHull_points_saturated (n : ℕ) (t : ℝ) (ω : TiltedConfiguration (2*n) t)
    (C : Finset LatticeVertex) (hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω)
    (b : TiltedBond (2*n) t) (hb : ω (tiltedBondEdge (2*n) t b) = true) :
    b.val.source ∈ C ↔ b.val.target ∈ C := by
  let u : tiltedStripVertices (2*n) t := ⟨b.val.source,b.property.1⟩
  let v : tiltedStripVertices (2*n) t := ⟨b.val.target,b.property.2⟩
  have ha : (tiltedOpenGraph (2*n) t ω).Adj u v :=
    (tiltedOpenGraph_adj_iff (2*n) t ω u v).mpr ⟨b.val.adjacent,hb⟩
  rw [show b.val.source=u.val from rfl,show b.val.target=v.val from rfl,
    lowerHull_coe_mem_iff n t ω C hC u,lowerHull_coe_mem_iff n t ω C hC v]
  constructor
  · rintro ⟨k,hk,w,hw,hwu⟩
    exact ⟨k,hk,w,hw,hwu.trans ha.reachable⟩
  · rintro ⟨k,hk,w,hw,hwv⟩
    exact ⟨k,hk,w,hw,hwv.trans ha.symm.reachable⟩

/-- The hull is geometrically connected: its lower central roots are joined
by internal vertical edges, regardless of their sampled states. -/
theorem lowerHull_points_connected (n : ℕ) (t : ℝ) (ω : TiltedConfiguration (2*n) t)
    (C : Finset LatticeVertex) (hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω)
    (z : LatticeVertex) (hz : z ∈ C) :
    (squareLattice.induce (C : Set LatticeVertex)).Reachable
      ⟨(0,0),lowerHull_core_mem n t ω C hC 0 (by omega)⟩ ⟨z,hz⟩ := by
  classical
  have hz' : z ∈ (C : Set LatticeVertex) := hz
  rw [hC] at hz'
  obtain ⟨v,hv,rfl⟩ := hz'
  obtain ⟨k,hk,u,hu,⟨p⟩⟩ := hv
  let hom : (tiltedOpenGraph (2*n) t ω) →g squareLattice :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => (tiltedOpenGraph_adj_iff (2*n) t ω a b).mp hab |>.1 }
  have hpc : ∀ w ∈ (p.map hom).support, w ∈ (C : Set LatticeVertex) := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    apply (lowerHull_coe_mem_iff n t ω C hC a).mpr
    exact ⟨k,hk,u,hu,(p.takeUntil a ha).reachable⟩
  obtain ⟨r,hr⟩ := PlanarTopology.vertical_walk_between 0 0 (k:ℤ)
  have hrc : ∀ w ∈ r.support, w ∈ (C : Set LatticeVertex) := by
    intro w hw
    have hh := hr w hw
    have hkn : (0:ℤ) ≤ k := by omega
    simp only [min_eq_left hkn,max_eq_right hkn] at hh
    have hnw : w.2.toNat ≤ n := by omega
    have he : w = (0,(w.2.toNat:ℤ)) := by
      apply Prod.ext hh.1
      exact (Int.toNat_of_nonneg hh.2.1).symm
    rw [he]
    exact lowerHull_core_mem n t ω C hC _ hnw
  let R := r.induce (C : Set LatticeVertex) hrc
  let P := (p.map hom).induce (C : Set LatticeVertex) hpc
  have hstart : (⟨(0,0),hrc _ r.start_mem_support⟩ : (C : Set LatticeVertex)) =
      ⟨(0,0),lowerHull_core_mem n t ω C hC 0 (by omega)⟩ := rfl
  have hj : (⟨(0,(k:ℤ)),hrc _ r.end_mem_support⟩ : (C : Set LatticeVertex)) =
      ⟨hom u,hpc _ (p.map hom).start_mem_support⟩ := Subtype.ext hu.symm
  have hend : (⟨hom v,hpc _ (p.map hom).end_mem_support⟩ : (C : Set LatticeVertex)) = ⟨v.val,hz⟩ := rfl
  exact (R.copy hstart hj).reachable.trans (P.copy rfl hend).reachable

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
