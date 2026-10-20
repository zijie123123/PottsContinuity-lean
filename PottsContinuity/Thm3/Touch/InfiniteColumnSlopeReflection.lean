module

public import PottsContinuity.Thm3.Touch.FiniteColumnSlopeReflection

@[expose] public section

namespace PottsContinuity.Thm3.Touch

open Filter MeasureTheory Topology
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm3.Prop4

noncomputable section

/-- Horizontal reflection carries the infinite tilted strip at slope `t` to
the strip at slope `-t`. -/
def tiltedStripSlopeReflectionIso (N : ℕ) (t : ℝ) :
    tiltedStripGraph N t ≃g tiltedStripGraph N (-t) where
  toEquiv :=
    { toFun := fun z => ⟨(-z.1.1,z.1.2), by
        change 0 ≤ tiltedHeight (-t) (-z.1.1,z.1.2) ∧
          tiltedHeight (-t) (-z.1.1,z.1.2) ≤ N
        rw [tiltedHeight_columnSlopeReflection]
        exact z.2⟩
      invFun := fun z => ⟨(-z.1.1,z.1.2), by
        change 0 ≤ tiltedHeight t (-z.1.1,z.1.2) ∧
          tiltedHeight t (-z.1.1,z.1.2) ≤ N
        have h : tiltedHeight t (-z.1.1,z.1.2) = tiltedHeight (-t) z.1 := by
          simpa only [neg_neg] using tiltedHeight_columnSlopeReflection (-t) z.1
        rw [h]
        exact z.2⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  map_rel_iff' := by
    intro u v
    change |(-u.1.1)-(-v.1.1)| + |u.1.2-v.1.2| = 1 ↔
      |u.1.1-v.1.1| + |u.1.2-v.1.2| = 1
    constructor <;> intro h <;>
      simpa only [neg_sub_neg, abs_sub_comm] using h

/-- The induced homeomorphism on the infinite-strip configuration carriers. -/
def tiltedStripSlopeReflectionHomeomorph (N : ℕ) (t : ℝ) :
    TiltedConfiguration N t ≃ₜ TiltedConfiguration N (-t) :=
  Homeomorph.piCongrLeft (Y := fun _ : (tiltedStripGraph N (-t)).edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (tiltedStripSlopeReflectionIso N t))

theorem tiltedStripSlopeReflectionHomeomorph_edge (N : ℕ) (t : ℝ)
    (ω : TiltedConfiguration N t) (e : (tiltedStripGraph N t).edgeSet) :
    tiltedStripSlopeReflectionHomeomorph N t ω
      ((tiltedStripSlopeReflectionIso N t).mapEdgeSet e) = ω e :=
  Homeomorph.piCongrLeft_apply_apply
    (Y := fun _ : (tiltedStripGraph N (-t)).edgeSet => Bool)
    (SimpleGraph.Iso.mapEdgeSet (tiltedStripSlopeReflectionIso N t)) ω e

def tiltedOpenGraphSlopeReflectionIso (N : ℕ) (t : ℝ)
    (ω : TiltedConfiguration N t) :
    tiltedOpenGraph N t ω ≃g
      tiltedOpenGraph N (-t) (tiltedStripSlopeReflectionHomeomorph N t ω) where
  toEquiv := (tiltedStripSlopeReflectionIso N t).toEquiv
  map_rel_iff' := by
    intro u v
    rw [tiltedOpenGraph_adj_iff, tiltedOpenGraph_adj_iff]
    constructor
    · rintro ⟨h,hstate⟩
      have hbase : (tiltedStripGraph N t).Adj u v :=
        (tiltedStripSlopeReflectionIso N t).map_adj_iff.mp h
      let e : (tiltedStripGraph N t).edgeSet := ⟨s(u,v),hbase⟩
      have he : (tiltedStripSlopeReflectionIso N t).mapEdgeSet e =
          ⟨s(tiltedStripSlopeReflectionIso N t u,
            tiltedStripSlopeReflectionIso N t v),h⟩ := rfl
      refine ⟨hbase,?_⟩
      have hmap := tiltedStripSlopeReflectionHomeomorph_edge N t ω e
      change tiltedStripSlopeReflectionHomeomorph N t ω
          ((tiltedStripSlopeReflectionIso N t).mapEdgeSet e) = ω e at hmap
      rw [he] at hmap
      exact hmap ▸ hstate
    · rintro ⟨h,hstate⟩
      have hbase : (tiltedStripGraph N (-t)).Adj
          (tiltedStripSlopeReflectionIso N t u)
          (tiltedStripSlopeReflectionIso N t v) :=
        (tiltedStripSlopeReflectionIso N t).map_adj_iff.mpr h
      let e : (tiltedStripGraph N t).edgeSet := ⟨s(u,v),h⟩
      have he : (tiltedStripSlopeReflectionIso N t).mapEdgeSet e =
          ⟨s(tiltedStripSlopeReflectionIso N t u,
            tiltedStripSlopeReflectionIso N t v),hbase⟩ := rfl
      refine ⟨hbase,?_⟩
      have hmap := tiltedStripSlopeReflectionHomeomorph_edge N t ω e
      change tiltedStripSlopeReflectionHomeomorph N t ω
          ((tiltedStripSlopeReflectionIso N t).mapEdgeSet e) = ω e at hmap
      rw [he] at hmap
      exact hmap.symm ▸ hstate

/-- The bounded central-to-top connection is carried exactly by horizontal
reflection. -/
theorem tiltedTopConnectionWithinBox_columnSlopeReflection_iff
    (n R : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (ω : TiltedConfiguration (2*n) t) :
    ω ∈ tiltedTopConnectionWithinBox n R t ↔
      tiltedStripSlopeReflectionHomeomorph (2*n) t ω ∈
        tiltedTopConnectionWithinBox n R (-t) := by
  let e := tiltedStripSlopeReflectionIso (2*n) t
  let F := tiltedStripSlopeReflectionHomeomorph (2*n) t
  constructor
  · rintro ⟨k,hk,z,hz,v,hv,p,hbox⟩
    let z' := e z
    let v' := e v
    have hz' : z'.1 = (0,(k : ℤ)) := by
      change (-z.1.1,z.1.2) = (0,(k : ℤ))
      rw [hz]
      simp
    have hv' : tiltedTop (2*n) (-t) v'.1 := by
      change tiltedTop (2*n) (-t) (-v.1.1,v.1.2)
      exact (tiltedTop_columnSlopeReflection_iff (2*n) t ht v.1).mpr hv
    let hom := (tiltedOpenGraphSlopeReflectionIso (2*n) t ω).toHom
    let p' := p.map hom
    have hs : p'.support = p.support.map e := SimpleGraph.Walk.support_map hom p
    refine ⟨k,hk,z',hz',v',hv',p',?_⟩
    intro w hw
    have hw' : w ∈ p.support.map e := hs ▸ hw
    obtain ⟨u,hu,huw⟩ := List.mem_map.mp hw'
    have hboxu := hbox u hu
    have hcoord : w.1 = (-u.1.1,u.1.2) := by
      have h := congrArg Subtype.val huw
      change (-u.1.1,u.1.2) = w.1 at h
      exact h.symm
    have hbox' := (Foundations.mem_box_iff_abs_le R u.1).mp hboxu
    apply (Foundations.mem_box_iff_abs_le R w.1).mpr
    rw [hcoord]
    simpa [abs_neg] using hbox'
  · rintro ⟨k,hk,z,hz,v,hv,p,hbox⟩
    let z' := e.symm z
    let v' := e.symm v
    have hz' : z'.1 = (0,(k : ℤ)) := by
      change (-z.1.1,z.1.2) = (0,(k : ℤ))
      rw [hz]
      simp
    have hv' : tiltedTop (2*n) t v'.1 := by
      change tiltedTop (2*n) t (-v.1.1,v.1.2)
      exact (tiltedTop_columnSlopeReflection_iff (2*n) t ht
        (-v.1.1,v.1.2)).mp (by simpa using hv)
    let hom := (tiltedOpenGraphSlopeReflectionIso (2*n) t ω).symm.toHom
    let p' := p.map hom
    have hs : p'.support = p.support.map e.symm := SimpleGraph.Walk.support_map hom p
    refine ⟨k,hk,z',hz',v',hv',p',?_⟩
    intro w hw
    have hw' : w ∈ p.support.map e.symm := hs ▸ hw
    obtain ⟨u,hu,huw⟩ := List.mem_map.mp hw'
    have hboxu := hbox u hu
    have hcoord : w.1 = (-u.1.1,u.1.2) := by
      have h := congrArg Subtype.val huw
      change (-u.1.1,u.1.2) = w.1 at h
      exact h.symm
    have hbox' := (Foundations.mem_box_iff_abs_le R u.1).mp hboxu
    apply (Foundations.mem_box_iff_abs_le R w.1).mpr
    rw [hcoord]
    simpa [abs_neg] using hbox'

end

end PottsContinuity.Thm3.Touch
