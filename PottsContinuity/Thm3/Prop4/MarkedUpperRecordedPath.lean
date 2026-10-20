module

public import PottsContinuity.Thm3.Prop4.MarkedLowerRecordedPath
public import PottsContinuity.Thm3.Prop4.MarkedJointRawReveal

/-! # Whole-support recorded paths for the actual upper box trace -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedUpperPathBoxEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- The exact original upper trace is the whole support of a prescribed
recorded-open walk, including repeated vertices and boundary corners. -/
theorem markedUpperBoxTrace_recorded_walk (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hne : (markedUpperBoxTrace n u v A).Nonempty) :
    ∃ p : (openGraph (finiteLatticeGraph (box n))
      (A ∩ markedUpperBoxRawReveal n u v A)).Walk u v,
      p.support.toFinset = markedUpperBoxTrace n u v A := by
  classical
  let e : (finiteLatticeGraph (box n)) ≃g (finiteLatticeGraph (box n)) := boxHalfTurnIso n
  have hnerot : (markedLowerBoxTrace n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
      (configurationIso e A)).Nonempty := by
    obtain ⟨z,hz⟩ := hne
    obtain ⟨y,hy,_⟩ := Finset.mem_map.mp hz
    exact ⟨y,hy⟩
  obtain ⟨p,hp⟩ := markedLowerBoxTrace_recorded_walk n (boxHalfTurnIso n v)
    (boxHalfTurnIso n u) (configurationIso e A) hnerot
  have hB : (configurationIso e).symm
      (configurationIso e A ∩ markedLowerBoxRawReveal n
        (boxHalfTurnIso n v) (boxHalfTurnIso n u) (configurationIso e A)) =
      A ∩ markedUpperBoxRawReveal n u v A := by
    let R := markedLowerBoxRawReveal n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
      (configurationIso e A)
    change (configurationIso e).symm
      (configurationIso e A ∩ R) =
      A ∩ (configurationIso e).symm R
    have hI := Push.configurationIso_symm_inter e (configurationIso e A) R
    have hA := (configurationIso e).symm_apply_apply A
    rw [hA] at hI
    convert hI using 1
  have hh := recorded_walk_pullback_support e _ v u p _ hp
  have hh' : ∃ q : (openGraph (finiteLatticeGraph (box n))
      (A ∩ markedUpperBoxRawReveal n u v A)).Walk v u,
      q.support.toFinset = markedUpperBoxTrace n u v A := by
    erw [hB] at hh
    obtain ⟨q,hq⟩ := hh
    refine ⟨q,?_⟩
    ext x
    simp only [markedUpperBoxTrace,List.mem_toFinset]
    have h := Finset.ext_iff.mp hq x
    simp only [List.mem_toFinset] at h
    convert h using 1
    rfl
  obtain ⟨q,hq⟩ := hh'
  refine ⟨q.reverse,?_⟩
  simpa only [SimpleGraph.Walk.support_reverse,List.toFinset_reverse] using hq

end
end PottsContinuity.Thm3.Prop4
