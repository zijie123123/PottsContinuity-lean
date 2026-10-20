module

public import PottsContinuity.Thm3.Push.StripOpenEmbedding
public import PottsContinuity.Thm3.Push.WalkPullback

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- A vertex of the Lemma-2 crossing band has its literal translated preimage
in the base rectangle. -/
theorem baseStripEmbedding_preimage (k : ℝ) (s : ℕ) (z : stripVertices s)
    (hz : z.val ∈ Set.Icc (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ ×ˢ
      Set.Icc (0 : ℤ) (2*s)) :
    ∃ u, baseStripEmbedding k s u = z := by
  have hmem : (z.val.1, z.val.2+s) ∈ topWiredRectangle k (4/3) (3*s) := by
    rw [mem_topWiredRectangle_iff, floor_four_thirds_mul_three]
    simp only [Set.mem_prod, Set.mem_Icc] at hz
    push_cast at hz ⊢
    exact ⟨hz.1.1, hz.1.2, by omega, by omega⟩
  refine ⟨⟨(z.val.1, z.val.2+s), hmem⟩, ?_⟩
  apply Subtype.ext
  simp [baseStripEmbedding]

/-- The actual sampled open graph of the restricted base domain embeds in
the strip's actual sampled open graph. Boundary wirings create no edges. -/
def baseRestrictedOpenEmbedding (k : ℝ) (s M : ℕ)
    (hM : ⌊k*(3*s : ℕ)⌋ ≤ (M : ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce
      (stripWindow s M : Set (ℤ × ℤ)))) :
    rcOpenGraph (topWiredRectangle k (4/3) (3*s))
      ((boolConfigurationEquiv _).symm
        (embeddedConfigurationRestriction _ _ (baseStripWindowEmbedding k s M hM)
          (baseStripWindowEmbedding_map_le k s M hM) C)) ↪g
      stripOpenGraph s (stripPlaneRestriction s (stripWindowPlaneConfiguration s M C)) where
  toFun := baseStripEmbedding k s
  inj' := (baseStripEmbedding k s).injective
  map_rel_iff' := by
    intro u v
    let ω := (boolConfigurationEquiv _).symm
      (embeddedConfigurationRestriction _ _ (baseStripWindowEmbedding k s M hM)
        (baseStripWindowEmbedding_map_le k s M hM) C)
    let j := openStateEmbedding (baseStripEmbedding k s) ω
      (stripPlaneRestriction s (stripWindowPlaneConfiguration s M C))
      (baseStripEmbedding_edge_state k s M hM C)
    have h := j.map_rel_iff' (a := u) (b := v)
    change (stripOpenGraph s (stripPlaneRestriction s (stripWindowPlaneConfiguration s M C))).Adj
      (baseStripEmbedding k s u) (baseStripEmbedding k s v) ↔
      (openGraph _ (boolConfigurationEquiv _ ω)).Adj u v at h
    have hEq := rcOpenGraph_eq (topWiredRectangle k (4/3) (3*s)) ω
    erw [hEq] at h
    exact h

/-- The shifted strip crossing yields the source base crossing in the
restricted finite configuration, with all vertices confined to height 3*s. -/
theorem strip_crossing_implies_base_restricted_crossing (k : ℝ) (s M : ℕ)
    (hM : ⌊k*(3*s : ℕ)⌋ ≤ (M : ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce
      (stripWindow s M : Set (ℤ × ℤ))))
    (hcross : stripPlaneRestriction s (stripWindowPlaneConfiguration s M C) ∈
      stripHorizontalCrossing s (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (2*s)) :
    horizontalCrossing (topWiredRectangle k (4/3) (3*s))
      (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ)
      ((boolConfigurationEquiv _).symm
        (embeddedConfigurationRestriction _ _ (baseStripWindowEmbedding k s M hM)
          (baseStripWindowEmbedding_map_le k s M hM) C)) := by
  obtain ⟨x, y, w, hx, hy, hw⟩ := hcross
  let j := baseRestrictedOpenEmbedding k s M hM C
  obtain ⟨u, hu⟩ := baseStripEmbedding_preimage k s x (hw x w.start_mem_support)
  obtain ⟨v, hv⟩ := baseStripEmbedding_preimage k s y (hw y w.end_mem_support)
  have hju : j u = x := hu
  have hjv : j v = y := hv
  let wc := w.copy hju.symm hjv.symm
  have hrange : ∀ z ∈ wc.support, z ∈ Set.range j := by
    intro z hz
    have hz' : z ∈ w.support := by simpa only [wc, SimpleGraph.Walk.support_copy] using hz
    exact baseStripEmbedding_preimage k s z (hw z hz')
  obtain ⟨wr, hwr⟩ := exists_walk_pullback_support j wc hrange
  have hcoords (z) : (j z).val = (z.val.1, z.val.2-s) := by rfl
  have hux := congrArg (fun z : stripVertices s => z.val) hju
  have hvx := congrArg (fun z : stripVertices s => z.val) hjv
  rw [hcoords] at hux hvx
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_Icc] at hx hy ⊢
  refine ⟨u, v, wr, ?_, ?_, ?_⟩
  · simp only [← hux] at hx
    push_cast at hx ⊢
    exact ⟨hx.1, by omega, by omega⟩
  · simp only [← hvx] at hy
    push_cast at hy ⊢
    exact ⟨hy.1, by omega, by omega⟩
  · intro z hz
    have hzs := hwr z hz
    have hzold : j z ∈ w.support := by
      simpa only [wc, SimpleGraph.Walk.support_copy] using hzs
    have hzw := hw (j z) hzold
    rw [hcoords] at hzw
    simp only [Set.mem_prod, Set.mem_Icc] at hzw ⊢
    push_cast at hzw ⊢
    exact ⟨hzw.1, by omega, by omega⟩

end
end PottsContinuity.Push
