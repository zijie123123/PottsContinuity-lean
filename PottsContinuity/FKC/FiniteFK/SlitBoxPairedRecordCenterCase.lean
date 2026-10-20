-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedRecordCenterCase.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedRecordCandidates
public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedCandidateRestoration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

/-- When the source is the bottom center itself, a genuine paired hit record
retains its selected right path from the center. Thus the frozen record is
already in the center-to-arc event, and restoring any deleted configuration
under the same actual paired reveal remains in that event. -/
theorem slitBoxPairedRecord_zeroX_restores_center_arc
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : u.val.1 = 0)
    (δ : PositiveMesh) (Arecord : Configuration (slitBoxGraph n))
    (hA : Arecord ∈ slitBoxWiredArcConnectionEvent n u)
    (hAReflect : configurationIso (slitBoxGraphHorizontalReflectionIso n) Arecord ∈
      slitBoxWiredArcConnectionEvent n u)
    (Adeleted : Configuration (edgeRestriction (slitBoxGraph n)
      (slitBoxPairedReveal n hn u huY (by omega) δ Arecord))) :
    Arecord ∩ slitBoxPairedReveal n hn u huY (by omega) δ Arecord ∈
        slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) ∧
      ((edgeRestrictionConfigurationEquiv (slitBoxGraph n)
        (slitBoxPairedReveal n hn u huY (by omega) δ Arecord) Adeleted).val ∪
          (Arecord ∩ slitBoxPairedReveal n hn u huY (by omega) δ Arecord)) ∈
        slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) := by
  classical
  let hux : 0 ≤ u.val.1 := by omega
  let R := slitBoxPairedReveal n hn u huY hux δ Arecord
  let p := slitBoxLeastOpenCandidateOnEvent n hn u huY hux δ Arecord hA
  let q := slitBoxLeastOpenCandidateOnEvent n hn u huY hux δ
    (configurationIso (slitBoxGraphHorizontalReflectionIso n) Arecord) hAReflect
  have hselected := slitBoxPairedReveal_selected_supports_on_good
    n hn u huY hux δ Arecord hA hAReflect
  have hpSupport : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ Arecord ∩ R := by
    simpa [p, R, hux] using hselected.1
  have hqSupport : slitBoxCandidateOriginalPathEdgeSupport n
      (slitBoxReflectVertex n u) (slitBoxReflectCandidate n u q) ⊆ Arecord ∩ R := by
    simpa [q, R, hux] using hselected.2
  have huCenter : u = slitBoxBottomCenterVertex n := by
    apply Subtype.ext
    rw [slitBoxBottomCenterVertex_val]
    exact Prod.ext huX huY
  have hcenterPath : slitBoxBottomCenterVertex n ∈
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support ∨
    slitBoxGraphHorizontalReflectionIso n (slitBoxBottomCenterVertex n) ∈
      (q.val.2 : (slitBoxGraph n).Walk u q.val.1).support := by
    left
    rw [← huCenter]
    simp
  have hrestores := slitBoxPairedCandidate_center_path_restores_arc
    n u p q (Arecord ∩ R) R Adeleted hpSupport hqSupport hcenterPath
  refine ⟨?_, ?_⟩
  · have hrestoredEmpty := slitBoxPairedCandidate_center_path_restores_arc
      n u p q (Arecord ∩ R) R (∅ : Configuration (edgeRestriction (slitBoxGraph n) R))
      hpSupport hqSupport hcenterPath
    simpa using hrestoredEmpty
  · simpa [R] using hrestores

end

end PottsContinuity.FKC.FiniteFK

