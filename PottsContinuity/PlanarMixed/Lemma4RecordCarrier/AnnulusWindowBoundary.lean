module

public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.SourceAnnulusReveal

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW
noncomputable section

/-- An annulus-record edge in a connector window lies entirely on a vertical
boundary column. The source core boxes only touch these windows at their sides. -/
theorem lemma4_annulus_query_in_window_boundary
    (n : ℕ) (j : Fin 3) (e : (lemma4AmbientGraph n).edgeSet)
    (he : e ∈ lemma4AnnulusBondReveal n)
    (hwindow : ∀ v ∈ e.val, (10*(j:ℤ)-13)*(n:ℤ) ≤ v.val.1 ∧
      v.val.1 ≤ (10*(j:ℤ)-7)*(n:ℤ)) :
    (∀ v ∈ e.val, v.val.1=(10*(j:ℤ)-13)*(n:ℤ)) ∨
    (∀ v ∈ e.val, v.val.1=(10*(j:ℤ)-7)*(n:ℤ)) := by
  classical
  have hrec : (∀ v ∈ e.val, v ∈ vertexBoxRegion (box (56*n)) (5*(n:ℤ),0) (2*n)) ∨
      (∀ v ∈ e.val, v ∈ vertexBoxRegion (box (56*n)) (-5*(n:ℤ),0) (2*n)) := by
    simpa only [lemma4AnnulusBondReveal,Finset.mem_filter,Finset.mem_univ,true_and] using he
  have hpoint (z : ℤ × ℤ) (v : (box (56*n) : Set (ℤ × ℤ)))
      (hv : v ∈ vertexBoxRegion (box (56*n)) z (2*n)) :
      z.1-2*(n:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ z.1+2*(n:ℤ) := by
    change max |v.val.1-z.1| |v.val.2-z.2| ≤ ((2*n:ℕ):ℤ) at hv
    have h := abs_le.mp ((le_max_left _ _).trans hv)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at h
    omega
  fin_cases j
  · rcases hrec with hplus | hminus
    · left
      intro v hv
      have h := hpoint _ v (hplus v hv)
      have hw := hwindow v hv
      dsimp at h hw ⊢
      omega
    · right
      intro v hv
      have h := hpoint _ v (hminus v hv)
      have hw := hwindow v hv
      dsimp at h hw ⊢
      omega
  · rcases hrec with hplus | hminus
    · right
      intro v hv
      have h := hpoint _ v (hplus v hv)
      have hw := hwindow v hv
      dsimp at h hw ⊢
      omega
    · left
      intro v hv
      have h := hpoint _ v (hminus v hv)
      have hw := hwindow v hv
      dsimp at h hw ⊢
      omega
  · rcases hrec with hplus | hminus
    · left
      intro v hv
      have h := hpoint _ v (hplus v hv)
      have hw := hwindow v hv
      dsimp at h hw ⊢
      omega
    · left
      intro v hv
      have h := hpoint _ v (hminus v hv)
      have hw := hwindow v hv
      dsimp at h hw ⊢
      omega

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
