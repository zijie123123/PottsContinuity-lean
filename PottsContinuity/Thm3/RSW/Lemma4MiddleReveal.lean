module

public import PottsContinuity.Thm3.RSW.AnnulusRecordedSupport
public import PottsContinuity.Thm3.RSW.Lemma4SourceEvents

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
local instance lemma4MiddleEdgeEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _
local instance lemma4MiddleEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

/-- The entire closed middle vertex band, including the two boundary rows. -/
def lemma4MiddleVertices (n : ℕ) : Set {z : LatticeVertex // z ∈ box (56*n)} :=
  {v | |v.val.2| ≤ 2*(n:ℤ)}

/-- All original sampled bonds whose endpoints belong to the closed middle
band. The carrier and edge states are unchanged at every scale. -/
def lemma4MiddleReveal (n : ℕ) : Configuration (lemma4AmbientGraph n) :=
  by
    classical
    exact Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ lemma4MiddleVertices n)

/-- Every recorded bond has both endpoints in the literal middle band. -/
theorem lemma4MiddleReveal_endpoint (n : ℕ) {e : (lemma4AmbientGraph n).edgeSet}
    (he : e ∈ lemma4MiddleReveal n) {v : {z : LatticeVertex // z ∈ box (56*n)}}
    (hv : v ∈ e.val) : v ∈ lemma4MiddleVertices n := by
  classical
  exact (Finset.mem_filter.mp he).2 v hv

/-- The reveal includes every bond in any source annulus outer box whose
center is on the horizontal axis. -/
theorem lemma4MiddleReveal_records_annulus_bonds (n : ℕ) (x : ℤ)
    (e : (lemma4AmbientGraph n).edgeSet)
    (he : ∀ v ∈ e.val, v ∈ vertexBoxRegion (box (56*n)) (x,0) (2*n)) :
    e ∈ lemma4MiddleReveal n := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro v hv
  have h := he v hv
  change max |v.val.1-x| |v.val.2-0| ≤ ((2*n : ℕ) : ℤ) at h
  have hy := (le_max_right |v.val.1-x| |v.val.2-0|).trans h
  change |v.val.2| ≤ 2*(n:ℤ)
  simpa only [sub_zero,Nat.cast_mul,Nat.cast_ofNat] using hy

/-- The actual source annulus pair is determined by the recorded original
middle bonds, including its possible bonds in the boundary rows. -/
theorem lemma4AnnulusPairEvent_middle_visible (n : ℕ)
    (A A' : Configuration (lemma4AmbientGraph n))
    (hstate : A ∩ lemma4MiddleReveal n = A' ∩ lemma4MiddleReveal n) :
    A ∈ lemma4AnnulusPairEvent n ↔ A' ∈ lemma4AnnulusPairEvent n := by
  exact (annulus_event_visible_in_recorded_outerBonds (box (56*n)) (5*(n:ℤ),0) n
    (lemma4MiddleReveal n) (lemma4MiddleReveal_records_annulus_bonds n _) A A' hstate).and
    (annulus_event_visible_in_recorded_outerBonds (box (56*n)) (-5*(n:ℤ),0) n
      (lemma4MiddleReveal n) (lemma4MiddleReveal_records_annulus_bonds n _) A A' hstate)

end
end PottsContinuity.RSW
