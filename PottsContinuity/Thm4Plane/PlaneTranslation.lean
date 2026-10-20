module

public import PottsContinuity.Infinite.Translation
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm4Plane

open PottsContinuity

/-- The free box-boundary connection event centered at the origin. -/
def centeredBoxBoundaryConnectionEvent (n : ℕ) :
    Set (squareLattice.edgeSet → Bool) :=
  {ω | ∃ y ∈ vertexBoundary (box n),
    (rcInfiniteOpenGraph ω).Reachable (0, 0) y}

/-- The translated version of the same box-boundary event, centered at `a`. -/
def translatedBoxBoundaryConnectionEvent (a : PD.FK.LatticeVertex) (n : ℕ) :
    Set (squareLattice.edgeSet → Bool) :=
  {ω | ∃ y ∈ PD.FK.latticeTranslate a '' vertexBoundary (box n),
    (rcInfiniteOpenGraph ω).Reachable a y}

private theorem translatedBoxBoundaryConnectionEvent_eq_preimage
    (a : PD.FK.LatticeVertex) (n : ℕ) :
    translatedBoxBoundaryConnectionEvent a n =
      (PD.FK.latticeConfigurationTranslate (-a)) ⁻¹'
        centeredBoxBoundaryConnectionEvent n := by
  classical
  cases Foundations.squareLattice_eq_PD
  ext ω
  simp only [Set.mem_ofPred_eq,
    translatedBoxBoundaryConnectionEvent, centeredBoxBoundaryConnectionEvent]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hreach⟩
    refine ⟨z, hz, ?_⟩
    have hreachPD : (PD.rcInfiniteOpenGraph ω).Reachable a
        (PD.FK.latticeTranslate a z) := by
      rw [← Foundations.rcInfiniteOpenGraph_eq_PD]
      exact hreach
    have hreach' :=
      (PD.RCInfinite.openGraphTranslationIso (-a) ω).reachable_iff.mpr hreachPD
    have ha : PD.FK.latticeTranslate (-a) a = (0, 0) := by
      ext <;> simp [PD.FK.latticeTranslate]
    have hz' : PD.FK.latticeTranslate (-a) (PD.FK.latticeTranslate a z) = z :=
      PD.FK.latticeTranslate_neg_cancel a z
    have hgraph : PD.rcInfiniteOpenGraph (PD.RCInfinite.edgeTranslate (-a) ω) =
        rcInfiniteOpenGraph (PD.FK.latticeConfigurationTranslate (-a) ω) := by
      simpa [PD.RCInfinite.edgeTranslate] using
        (Foundations.rcInfiniteOpenGraph_eq_PD
          (PD.FK.latticeConfigurationTranslate (-a) ω)).symm
    have hreachTarget :
        (PD.rcInfiniteOpenGraph (PD.RCInfinite.edgeTranslate (-a) ω)).Reachable
          (0, 0) z := by
      simpa [PD.RCInfinite.openGraphTranslationIso, PD.RCInfinite.edgeTranslate,
        PD.FK.latticeTranslationIso, PD.FK.latticeTranslate, ha, hz'] using hreach'
    rw [hgraph] at hreachTarget
    exact hreachTarget
  · rintro ⟨z, hz, hreach⟩
    refine ⟨PD.FK.latticeTranslate a z, ⟨z, hz, rfl⟩, ?_⟩
    have hgraph : PD.rcInfiniteOpenGraph (PD.RCInfinite.edgeTranslate (-a) ω) =
        rcInfiniteOpenGraph (PD.FK.latticeConfigurationTranslate (-a) ω) := by
      simpa [PD.RCInfinite.edgeTranslate] using
        (Foundations.rcInfiniteOpenGraph_eq_PD
          (PD.FK.latticeConfigurationTranslate (-a) ω)).symm
    have ha : PD.FK.latticeTranslate (-a) a = (0, 0) := by
      ext <;> simp [PD.FK.latticeTranslate]
    have hz' : PD.FK.latticeTranslate (-a) (PD.FK.latticeTranslate a z) = z :=
      PD.FK.latticeTranslate_neg_cancel a z
    have hreachTarget :
        (PD.rcInfiniteOpenGraph (PD.RCInfinite.edgeTranslate (-a) ω)).Reachable
          (0, 0) z := by
      rw [hgraph]
      exact hreach
    have hreachMapped :
        (PD.rcInfiniteOpenGraph (PD.RCInfinite.edgeTranslate (-a) ω)).Reachable
          ((PD.RCInfinite.openGraphTranslationIso (-a) ω) a)
          ((PD.RCInfinite.openGraphTranslationIso (-a) ω)
            (PD.FK.latticeTranslate a z)) := by
      simpa [PD.RCInfinite.openGraphTranslationIso, PD.RCInfinite.edgeTranslate,
        PD.FK.latticeTranslationIso, PD.FK.latticeTranslate, ha, hz'] using hreachTarget
    have hreach' := (PD.RCInfinite.openGraphTranslationIso (-a) ω).reachable_iff.mp
      hreachMapped
    rw [← Foundations.rcInfiniteOpenGraph_eq_PD] at hreach'
    simpa [PD.FK.latticeTranslate, ha, hz'] using hreach'

/-- Translation invariance of the free every-exhaustion limit identifies the
box-boundary connection probability at any center with the centered one. -/
theorem translatedBoxBoundaryConnection_probability_eq
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hq : 1 ≤ (q : ℝ)) (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 0 μ)
    (a : PD.FK.LatticeVertex) (n : ℕ) :
    μ.real (translatedBoxBoundaryConnectionEvent a n) =
      μ.real (centeredBoxBoundaryConnectionEvent n) := by
  cases Foundations.squareLattice_eq_PD
  change Measure PD.FK.LatticeConfiguration at μ
  have htrans := Infinite.infinite_volume_translation_invariant
    p q hq 0 μ hμ (-a)
  let B : Set PD.FK.LatticeConfiguration :=
    {ω | ∃ y ∈ vertexBoundary (box n),
      (PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y}
  have hBmeas : MeasurableSet B := by
    classical
    have hset : B =
        ⋃ y : {y : PD.FK.LatticeVertex // y ∈ vertexBoundary (box n)},
          {ω | (PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y.1} := by
      ext ω
      simp [B]
    rw [hset]
    exact MeasurableSet.iUnion fun y =>
      PD.RCInfinite.measurableSet_open_reachable (0, 0) y.1
  have hBcenter : centeredBoxBoundaryConnectionEvent n = B := by
    ext ω
    change (∃ y ∈ vertexBoundary (box n),
        (rcInfiniteOpenGraph ω).Reachable (0, 0) y) ↔
      (∃ y ∈ vertexBoundary (box n),
        (PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y)
    rw [Foundations.rcInfiniteOpenGraph_eq_PD]
  have hmap := congrArg (fun ν : Measure PD.FK.LatticeConfiguration => ν B) htrans
  have hmapPre :
      μ ((PD.FK.latticeConfigurationTranslate (-a)) ⁻¹' B) = μ B := by
    calc
      μ ((PD.FK.latticeConfigurationTranslate (-a)) ⁻¹' B) =
          (μ.map (PD.FK.latticeConfigurationTranslate (-a))) B :=
        (Measure.map_apply
          (PD.FK.latticeConfigurationTranslate_measurable (-a)) hBmeas).symm
      _ = μ B := hmap
  have hprob :
      μ ((PD.FK.latticeConfigurationTranslate (-a)) ⁻¹'
        centeredBoxBoundaryConnectionEvent n) =
        μ (centeredBoxBoundaryConnectionEvent n) := by
    rw [hBcenter]
    exact hmapPre
  rw [translatedBoxBoundaryConnectionEvent_eq_preimage]
  simp only [Measure.real]
  exact congrArg ENNReal.toReal hprob

end PottsContinuity.Thm4Plane
