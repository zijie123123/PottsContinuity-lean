module

public import PottsContinuity.Thm3.Prop4.RawMaskedBridgeGluing
public import PottsContinuity.Thm3.Prop4.BoxRawQueryExitTransport
public import PottsContinuity.Thm3.Prop4.MaskedConfinedWalk
public import PottsContinuity.Thm3.Prop4.FiniteStrictCore

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite PlanarTopology Exploration
noncomputable section
local instance sourceBoxRawCoreGluingEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _
local instance sourceBoxRawCoreGluingRectangleEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- A source-faithful raw replay of EVERY strict-core reference crossing
contains an actual marked walk confined to the original Euclidean tube. -/
theorem sourceBox_raw_replay_strict_core_gluing
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (A B : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (hLower : ∀ z ∈ markedLowerBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ (z.val.2 : ℝ)-(t*z.val.1+b) ≤ 0)
    (hUpper : ∀ z ∈ markedUpperBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ 0 ≤ (z.val.2 : ℝ)-(t*z.val.1+b))
    (hB : B ∈ inducedStrictInteriorTubeCrossingEvent (box n) n R u.val v.val t b) :
    ∃ p : (openGraph (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
      (replayRevealedState (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n))
        (sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          (boxTubeRectangleIso n u) (boxTubeRectangleIso n v) (configurationIso (boxTubeRectangleIso n) A))
        (revealRecordConfiguration (sourceMarkedRawReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)) (configurationIso (boxTubeRectangleIso n) A))
        (configurationIso (boxTubeRectangleIso n) B))).Walk (boxTubeRectangleIso n u) (boxTubeRectangleIso n v),
      ∀ z ∈ p.support, z.val ∈ radiusTube n R u.val v.val := by
  classical
  let i : finiteLatticeGraph (box n) ≃g rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := boxTubeRectangleIso n
  let a : LatticeVertex := (-(n : ℤ),-(n : ℤ))
  let Ar := configurationIso i A
  let Br := configurationIso i B
  let T : Set LatticeVertex := ↑(radiusTube n R u.val v.val)
  let S : Set (RectangleVertex a (2*n) (2*n)) := {z | z.val ∈ T}
  let C := replayRevealedState (rectangleGraph a (2*n) (2*n))
    (sourceMarkedRawReveal a (2*n) (2*n) (i u) (i v) Ar)
    (revealRecordConfiguration (sourceMarkedRawReveal a (2*n) (2*n) (i u) (i v)) Ar) Br
  have hAr : ActualConnected (rectangleGraph a (2*n) (2*n)) Ar (i u) (i v) := by
    obtain ⟨p⟩ := hA
    exact ⟨p.map (openGraphIso i A).toHom⟩
  obtain ⟨l,r,hl,hr,p,hp⟩ := hB
  let P := p.map (openGraphIso i B).toHom
  have hP : ∀ z ∈ P.support, z.val ∈ T ∧ |(z.val.2 : ℝ)-(t*z.val.1+b)| < R-1 := by
    intro z hz
    have he : P.support = p.support.map (openGraphIso i B).toHom :=
      SimpleGraph.Walk.support_map (openGraphIso i B).toHom p
    rw [he] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    exact hp x hx
  have hMasked : ∃ Q : (openGraph (rectangleGraph a (2*n) (2*n))
      (Br ∩ RSW.inducedConfigurationErasure S (Finset.univ : Configuration (rectangleGraph a (2*n) (2*n))))).Walk (i l) (i r),
      ∀ z ∈ Q.support, z ∈ P.support := by
    have hmask := masked_walk_of_confined (rectangleGraph a (2*n) (2*n)) Br S P (fun z hz => (hP z hz).1)
    have heq : RSW.inducedConfigurationErasure S Br =
        Br ∩ RSW.inducedConfigurationErasure S (Finset.univ : Configuration (rectangleGraph a (2*n) (2*n))) := by
      ext e
      simp only [RSW.mem_inducedConfigurationErasure,Finset.mem_inter,Finset.mem_univ,true_and]
      rfl
    rw [heq] at hmask
    exact hmask
  obtain ⟨Q,hQ⟩ := hMasked
  have hconn := sourceMarkedRaw_masked_connection_of_query_exit_heights a (2*n) (2*n)
    (by omega) (by omega) (i u) (i v) hu (by change v.val.1 = -(n : ℤ)+(2*n : ℕ); omega)
    Ar Br hAr T t b R ht
    (sourceBox_lower_raw_query_exit_height_le n hn R hR u v hu hv t b hut hvt A hA hLower)
    (sourceBox_upper_raw_query_exit_height_ge n hn R hR u v hu hv t b hut hvt A hA hUpper)
    (i l) (i r) hl (by change r.val.1 = -(n : ℤ)+(2*n : ℕ); omega) Q
    (fun z hz => (hP z (hQ z hz)).2)
  have huT : i u ∈ S := by
    apply (mem_radiusTube n R u.val v.val u.val).mpr
    refine ⟨u.property,?_⟩
    rw [tubeDistance,Metric.infDist_zero_of_mem (left_mem_segment ℝ _ _)]
    exact hR
  apply (actualConnected_erasure_iff_confined_walk (rectangleGraph a (2*n) (2*n)) S C (i u) (i v) huT).mp
  have heq : RSW.inducedConfigurationErasure S C =
      C ∩ RSW.inducedConfigurationErasure S (Finset.univ : Configuration (rectangleGraph a (2*n) (2*n))) := by
    ext e
    simp only [RSW.mem_inducedConfigurationErasure,Finset.mem_inter,Finset.mem_univ,true_and]
  rw [heq]
  exact hconn

end
end PottsContinuity.Thm3.Prop4
