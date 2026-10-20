-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverSelectedCorners.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCorners
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

/-- Actual corner labels contributed at a box vertex by selected retained
lifted faces. -/
noncomputable def parafermionicCoverFiniteFaceSelectedCorners {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ i ∈ S, parafermionicCoverFaceCorner i.1 c = v.1

theorem parafermionicCoverFiniteFaceSelectedCorners_mem_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) (c : Fin 4) :
    c ∈ parafermionicCoverFiniteFaceSelectedCorners S v ↔
      ∃ i ∈ S, parafermionicCoverFaceCorner i.1 c = v.1 := by
  classical
  simp [parafermionicCoverFiniteFaceSelectedCorners]

noncomputable def selectedIncidentFaceCorner
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n)
    (i : ParafermionicCoverFiniteFaceTopIndex n) : Fin 4 := by
  classical
  by_cases hi : i ∈ parafermionicCoverFiniteFaceSelectedIncidentVertices S v
  · exact Classical.choose
      ((parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_faceCorner i v).mp
        (Finset.mem_filter.mp hi).2)
  · exact 0

private theorem selectedIncidentFaceCorner_spec
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n)
    {i : ParafermionicCoverFiniteFaceTopIndex n}
    (hi : i ∈ parafermionicCoverFiniteFaceSelectedIncidentVertices S v) :
    parafermionicCoverFaceCorner i.1 (selectedIncidentFaceCorner S v i) = v.1 := by
  classical
  rw [selectedIncidentFaceCorner, dite_eq_left hi]
  exact Classical.choose_spec
    ((parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_faceCorner i v).mp
      (Finset.mem_filter.mp hi).2)

private theorem selectedIncidentFaceCorner_injOn
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    Set.InjOn (selectedIncidentFaceCorner S v)
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v :
        Set (ParafermionicCoverFiniteFaceTopIndex n)) := by
  intro i hi j hj heq
  apply Subtype.ext
  apply parafermionicCoverFaceCorner_injective_face (selectedIncidentFaceCorner S v i)
  calc
    parafermionicCoverFaceCorner i.1 (selectedIncidentFaceCorner S v i) = v.1 :=
      selectedIncidentFaceCorner_spec S v hi
    _ = parafermionicCoverFaceCorner j.1 (selectedIncidentFaceCorner S v i) := by
      rw [heq]
      exact (selectedIncidentFaceCorner_spec S v hj).symm

private theorem selectedCorners_eq_incidentFaceCorner_image
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFiniteFaceSelectedCorners S v =
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).image
        (selectedIncidentFaceCorner S v) := by
  classical
  ext c
  constructor
  · intro hc
    rcases (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v c).mp hc with
      ⟨i, hiS, hcorner⟩
    have hi : i ∈ parafermionicCoverFiniteFaceSelectedIncidentVertices S v := by
      apply Finset.mem_filter.mpr
      refine ⟨hiS, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_faceCorner i v).mpr
        ⟨c, hcorner⟩
    apply Finset.mem_image.mpr
    refine ⟨i, hi, ?_⟩
    have hchoice := selectedIncidentFaceCorner_spec S v hi
    exact parafermionicCoverFaceCorner_injective_label i.1
      (hchoice.trans hcorner.symm)
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨i, hi, hEq⟩
    have hcorner := selectedIncidentFaceCorner_spec S v hi
    apply (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v c).mpr
    refine ⟨i, (Finset.mem_filter.mp hi).1, ?_⟩
    rw [← hEq]
    exact hcorner

theorem parafermionicCoverFiniteFaceSelectedCorners_card {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverFiniteFaceSelectedCorners S v).card =
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card := by
  classical
  rw [selectedCorners_eq_incidentFaceCorner_image]
  exact Finset.card_image_of_injOn (selectedIncidentFaceCorner_injOn S v)

theorem parafermionicCoverFiniteFaceSelectedCorners_nonempty_iff_unionCarrier
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverFiniteFaceSelectedCorners S v).Nonempty ↔
      v ∈ parafermionicCoverFiniteFaceUnionCarrier S := by
  constructor
  · intro h
    apply (parafermionicCoverFiniteFaceUnionCarrier_iff_incidentVertices_nonempty S v).2
    have hpos : 0 <
        (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card := by
      rw [← parafermionicCoverFiniteFaceSelectedCorners_card]
      exact Finset.card_pos.mpr h
    exact Finset.card_pos.mp hpos
  · intro h
    have hi :=
      (parafermionicCoverFiniteFaceUnionCarrier_iff_incidentVertices_nonempty S v).1 h
    have hpos := Finset.card_pos.mpr hi
    rw [← parafermionicCoverFiniteFaceSelectedCorners_card] at hpos
    exact Finset.card_pos.mp hpos

end PottsContinuity.FKC.Medial
