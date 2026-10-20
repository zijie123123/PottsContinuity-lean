-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripSourceEventExtension.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedExtensionPaths
public import PottsContinuity.FKC.FiniteFK.HorizontalStripWindowGeometry
public import PottsContinuity.FKC.FiniteFK.FiniteRegionSourceEvent
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleConfiguration
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripGoodEventClopen
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

def horizontalStripFiniteOpenToExtensionHom
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n)) :
    openGraph (horizontalStripCutRectangle N n) A →g
      horizontalStripRectangleOpenGraph N n
        (horizontalStripRectanglePlaneExtension N n A) where
  toFun := id
  map_rel' := by
    intro u v h
    rw [horizontalStripRectangleOpenGraph_eq_openGraph N n A]
    exact h

private theorem horizontalStripFiniteWalk_toExtension_support
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n))
    {u v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)}
    (p : (openGraph (horizontalStripCutRectangle N n) A).Walk u v) :
    (p.map (horizontalStripFiniteOpenToExtensionHom N n A)).support = p.support := by
  simp [horizontalStripFiniteOpenToExtensionHom, SimpleGraph.Walk.support_map]

def horizontalStripExtensionToFiniteHom
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n)) :
    horizontalStripRectangleOpenGraph N n
        (horizontalStripRectanglePlaneExtension N n A) →g
      openGraph (horizontalStripCutRectangle N n) A where
  toFun := id
  map_rel' := by
    intro u v h
    rw [← horizontalStripRectangleOpenGraph_eq_openGraph N n A]
    exact h

/-- A walk in the literal finite rectangle open graph projects to an actual
walk in the whole strip graph of the closed-outside extension. -/
def horizontalStripClosedExtension_rectangleWalk_projects
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n))
    (u v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))
    (p : (horizontalStripRectangleOpenGraph N n
      (horizontalStripRectanglePlaneExtension N n A)).Walk u v) :
    (horizontalStripOpenGraph n (horizontalStripRectanglePlaneExtension N n A)).Walk
      (horizontalStripBlockerRectangleToStrip N n u)
      (horizontalStripBlockerRectangleToStrip N n v) := by
  have hEq := horizontalStripRectangleOpenGraph_eq_openGraph N n A
  have p' : (horizontalStripRectangleOpenGraph N n
      (horizontalStripRectanglePlaneExtension N n A)).Walk u v := p
  exact p'.map (horizontalStripBlockerRectangleToStripHom N n
    (horizontalStripRectanglePlaneExtension N n A))

/-- Any strip walk ending at a vertex in the finite collar lifts to the actual
finite rectangle graph with every occurrence in its support retained. -/
theorem horizontalStripClosedExtension_stripWalk_lifts_at_end
    (N n : ℕ) (A : Configuration (horizontalStripCutRectangle N n))
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).Walk u v)
    (hv : -(N : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ N) :
    ∃ q : (horizontalStripRectangleOpenGraph N n
        (horizontalStripRectanglePlaneExtension N n A)).Walk
          (horizontalStripClosedExtension_rectangleVertex N n u
            (horizontalStripClosedExtension_walk_support_bounds_of_end N n A p hv
              u p.start_mem_support))
          (horizontalStripClosedExtension_rectangleVertex N n v hv),
      q.support.map (horizontalStripBlockerRectangleToStrip N n) = p.support := by
  classical
  let pr : (horizontalStripOpenGraph n
      (horizontalStripRectanglePlaneExtension N n A)).Walk v u := p.reverse
  obtain ⟨q, hq⟩ := horizontalStripClosedExtension_walk_lifts_to_rectangle
    N n A pr hv
  refine ⟨q.reverse, ?_⟩
  have hs : q.support.map (horizontalStripBlockerRectangleToStrip N n) = pr.support := hq
  rw [SimpleGraph.Walk.support_reverse]
  calc
    List.map (horizontalStripBlockerRectangleToStrip N n) q.support.reverse =
        (List.map (horizontalStripBlockerRectangleToStrip N n) q.support).reverse := by
          rw [List.map_reverse]
    _ = pr.support.reverse := congrArg List.reverse hs
    _ = p.support := by
      have hpr : pr = p.reverse := rfl
      rw [hpr, SimpleGraph.Walk.support_reverse]
      simp

/-- The universal source event is unchanged when the strip configuration is
the closed-outside extension of its literal finite rectangle restriction. -/
theorem horizontalStripSourceAEvent_closedExtension_iff_finiteRegionSourceEvent
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N)
    (A : Configuration (horizontalStripCutRectangle N n)) :
    horizontalStripRectanglePlaneExtension N n A ∈
        horizontalStripSourceAEvent n m k h hh ↔
      A ∈ finiteRegionSourceEvent
        (horizontalStripWindowRegion N n m k h)
        (horizontalStripWindowWiredRegion N n m k h)
        (horizontalStripWindowRoot N n m k h hh hN) := by
  classical
  let ω := horizontalStripRectanglePlaneExtension N n A
  let x := horizontalStripVertexOfNat n k h (by omega)
  let xR := horizontalStripWindowRoot N n m k h hh hN
  have hxCollar : horizontalStripBlockerCollarBound n N x := by
    change -(N : ℤ) ≤ k ∧ k ≤ N
    have hN' : k.natAbs + m + 1 ≤ N := by
      simpa [horizontalStripBlockerCollarRadius] using hN
    have hklo : -((k.natAbs : ℕ) : ℤ) ≤ k := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le k
    have hkhi : k ≤ ((k.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact le_abs_self k
    constructor <;> omega
  have hxBounds : -(N : ℤ) ≤ x.val.1 ∧ x.val.1 ≤ N := by
    simpa [horizontalStripBlockerCollarBound] using hxCollar
  have hxVal : (horizontalStripBlockerRectangleToStrip N n xR).val = x.val := by
    simp only [horizontalStripBlockerRectangleToStrip_val,
      x, horizontalStripVertexOfNat]
    rfl
  have hgraph : horizontalStripRectangleOpenGraph N n
      (horizontalStripRectanglePlaneExtension N n A) =
      openGraph (horizontalStripCutRectangle N n) A := by
    exact horizontalStripRectangleOpenGraph_eq_openGraph N n A
  have hconn (u v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :
      ActualConnected (horizontalStripCutRectangle N n) A u v ↔
        (horizontalStripRectangleOpenGraph N n ω).Reachable u v := by
    simpa [ω] using horizontalStripRectangleActualConnected_iff N n A u v
  change
    ((∃ v : horizontalStripVertex n,
      ∃ p : (horizontalStripOpenGraph n ω).Walk x v,
        horizontalStripWiredSide n m k h v) ∧
      ∀ u : horizontalStripVertex n,
        ¬ horizontalStripClosedWindow n m k h u →
          ∀ p : (horizontalStripOpenGraph n ω).Walk u x,
            ∃ z, z ∈ p.support ∧ horizontalStripWiredSide n m k h z) ↔
    ((∃ w ∈ horizontalStripWindowWiredRegion N n m k h,
        ActualConnected (horizontalStripCutRectangle N n) A xR w) ∧
      ∀ uR, uR ∉ horizontalStripWindowRegion N n m k h →
        ∀ pR : (openGraph (horizontalStripCutRectangle N n) A).Walk uR xR,
          ∃ zR ∈ pR.support, zR ∈ horizontalStripWindowWiredRegion N n m k h)
  constructor
  · rintro ⟨⟨v, p, hvW⟩, hblock⟩
    constructor
    · obtain ⟨q, hq⟩ := horizontalStripClosedExtension_walk_lifts_to_rectangle
        N n A p hxBounds
      let vR := horizontalStripClosedExtension_rectangleVertex N n v
        (horizontalStripClosedExtension_walk_support_bounds_of_start N n A p hxBounds
          v p.end_mem_support)
      have hvR : horizontalStripBlockerRectangleToStrip N n vR = v := by
        apply Subtype.ext
        rfl
      refine ⟨vR, ?_, ?_⟩
      · change horizontalStripWiredSide n m k h
          (horizontalStripBlockerRectangleToStrip N n vR)
        simpa [hvR] using hvW
      · have hstart :
            horizontalStripClosedExtension_rectangleVertex N n x hxBounds = xR := by
          apply Subtype.ext
          change (k, (h : ℤ)) = (k, (h : ℤ))
          rfl
        have hq' := q.copy hstart rfl
        exact (hconn xR vR).mpr ⟨hq'⟩
    · intro uR huR pR
      have huOut : ¬ horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip N n uR) := by
        intro hu
        exact huR (by simpa [horizontalStripWindowRegion] using hu)
      let pExt := pR.map (horizontalStripFiniteOpenToExtensionHom N n A)
      let pStrip := horizontalStripClosedExtension_rectangleWalk_projects N n A uR xR pExt
      let pStrip' := pStrip.copy rfl (Subtype.ext hxVal)
      obtain ⟨z, hz, hzW⟩ := hblock _ huOut pStrip'
      have hsCopy : pStrip'.support = pStrip.support :=
        SimpleGraph.Walk.support_copy pStrip rfl (Subtype.ext hxVal)
      have hz' : z ∈ pStrip.support := by rw [← hsCopy]; exact hz
      change z ∈ (pExt.map
        (horizontalStripBlockerRectangleToStripHom N n ω)).support at hz'
      rw [SimpleGraph.Walk.support_map] at hz'
      rcases List.mem_map.mp hz' with ⟨zR, hzR, hzeq⟩
      have hzROrig : zR ∈ pR.support := by
        have hs := horizontalStripFiniteWalk_toExtension_support N n A pR
        change zR ∈ pExt.support at hzR
        rw [hs] at hzR
        exact hzR
      refine ⟨zR, hzROrig, ?_⟩
      change horizontalStripWiredSide n m k h
        (horizontalStripBlockerRectangleToStrip N n zR)
      have hv : horizontalStripBlockerRectangleToStrip N n zR = z := by
        apply Subtype.ext
        exact congrArg Subtype.val hzeq
      simpa [hv] using hzW
  · rintro ⟨⟨w, hwW, hconnW⟩, hblock⟩
    constructor
    · rcases (hconn xR w).mp hconnW with ⟨q⟩
      let p := horizontalStripClosedExtension_rectangleWalk_projects N n A xR w q
      refine ⟨horizontalStripBlockerRectangleToStrip N n w,
        p.copy (Subtype.ext hxVal) rfl, ?_⟩
      exact hwW
    · intro u huOut p
      have huBound : horizontalStripBlockerCollarBound n N u :=
        horizontalStripClosedExtension_walk_support_bounds_of_end N n A p hxBounds
          u p.start_mem_support
      have huBounds : -(N : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ N := by
        simpa [horizontalStripBlockerCollarBound] using huBound
      let uR := horizontalStripClosedExtension_rectangleVertex N n u huBounds
      have huVal : (horizontalStripBlockerRectangleToStrip N n uR).val = u.val := by
        calc
          (horizontalStripBlockerRectangleToStrip N n uR).val = uR.val := rfl
          _ = u.val := horizontalStripClosedExtension_rectangleVertex_val N n u huBounds
      have huR : uR ∉ horizontalStripWindowRegion N n m k h := by
        intro hwin
        apply huOut
        change horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip N n uR)
        change horizontalStripClosedWindow n m k h
          (horizontalStripBlockerRectangleToStrip N n uR) at hwin
        simpa [huVal] using hwin
      obtain ⟨q, hq⟩ := horizontalStripClosedExtension_stripWalk_lifts_at_end
        N n A p hxBounds
      have hxR : horizontalStripClosedExtension_rectangleVertex N n x hxBounds = xR := by
        apply Subtype.ext
        calc
          (horizontalStripClosedExtension_rectangleVertex N n x hxBounds).val = x.val :=
            horizontalStripClosedExtension_rectangleVertex_val N n x hxBounds
          _ = (k, (h : ℤ)) := rfl
          _ = xR.val := by simp [xR, horizontalStripWindowRoot_val]
      let hq' := q.copy rfl hxR
      let hqOpen := hq'.map (horizontalStripExtensionToFiniteHom N n A)
      obtain ⟨zR, hzR, hzW⟩ := hblock uR huR hqOpen
      have hqcopy : hqOpen.support = q.support := by
        calc
          hqOpen.support = hq'.support := by
            simp [hqOpen, horizontalStripExtensionToFiniteHom,
              SimpleGraph.Walk.support_map]
          _ = q.support := by simp [hq', SimpleGraph.Walk.support_copy]
      have hzMap : horizontalStripBlockerRectangleToStrip N n zR ∈ p.support := by
        have hz' : horizontalStripBlockerRectangleToStrip N n zR ∈ hqOpen.support.map
            (horizontalStripBlockerRectangleToStrip N n) := by
          exact List.mem_map.mpr ⟨zR, hzR, rfl⟩
        rw [hqcopy, hq] at hz'
        exact hz'
      refine ⟨horizontalStripBlockerRectangleToStrip N n zR, hzMap, ?_⟩
      exact hzW

/-- Exact preimage of the original strip source event under the literal finite
rectangle extension map. -/
theorem horizontalStripSourceAEvent_closedExtension_preimage
    (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N) :
    {A : Configuration (horizontalStripCutRectangle N n) |
      horizontalStripRectanglePlaneExtension N n A ∈ horizontalStripSourceAEvent n m k h hh} =
      finiteRegionSourceEvent
        (horizontalStripWindowRegion N n m k h)
        (horizontalStripWindowWiredRegion N n m k h)
        (horizontalStripWindowRoot N n m k h hh hN) := by
  ext A
  exact horizontalStripSourceAEvent_closedExtension_iff_finiteRegionSourceEvent
    N n m k h hh hN A

/-- The genuine finite FK probability of the source event equals its image
probability under the closed-outside whole-plane extension. -/
theorem horizontalStripRectangleProbabilityMeasure_apply_sourceAEvent
    (q : ClusterWeight) (N n m : ℕ) (k : ℤ) (h : ℕ) (hh : h ≤ n)
    (hN : horizontalStripBlockerCollarRadius m k ≤ N)
    (ξ : PottsContinuity.FKC.FiniteFK.BoundaryCondition
      (RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n))) :
    (horizontalStripRectangleProbabilityMeasure q N n ξ :
      MeasureTheory.Measure LatticeConfiguration)
        (horizontalStripSourceAEvent n m k h hh) =
      measure (horizontalStripCutRectangle N n) q ξ
        (finiteRegionSourceEvent
          (horizontalStripWindowRegion N n m k h)
          (horizontalStripWindowWiredRegion N n m k h)
          (horizontalStripWindowRoot N n m k h hh hN)) := by
  rw [horizontalStripRectangleProbabilityMeasure_apply_preimage q N n ξ
    (horizontalStripSourceAEvent n m k h hh)
    (isClopen_horizontalStripSourceAEvent n m k h hh).1.measurableSet]
  rw [horizontalStripSourceAEvent_closedExtension_preimage N n m k h hh hN]

end
end PottsContinuity.FKC.Medial
