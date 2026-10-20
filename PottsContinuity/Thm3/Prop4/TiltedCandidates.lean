module

public import PottsContinuity.Thm3.Prop4.LowestHeight
public import PottsContinuity.Thm3.RSW.Analytic

/-!
# Corrected finite candidate set in Lemma 6

DCST, TeX lines 1601–1608. Only the horizontal coordinate is bounded: using
S(n,t)∩Λ_(nm²) can omit the selected vertex. Each column has at most n+1
lattice vertices.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- Candidate lattice points in S(n,t) with horizontal coordinate in [-R,R]. -/
noncomputable def tiltedCandidates (n R : ℕ) (t : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (Finset.Icc (-(R : ℤ)) R).biUnion (fun k =>
    (Finset.Icc ⌈t*(k : ℝ)⌉ ⌊t*(k : ℝ)+(n : ℝ)⌋).image (fun l => (k,l)))

/-- The corrected candidate set imposes no spurious bound on the vertical coordinate. -/
theorem mem_tiltedCandidates (n R : ℕ) (t : ℝ) (z : ℤ × ℤ) :
    z ∈ tiltedCandidates n R t ↔ |z.1| ≤ (R : ℤ) ∧ z ∈ tiltedStripVertices n t := by
  classical
  simp only [tiltedCandidates, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, l, hl, rfl⟩
    refine ⟨abs_le.mpr hk, ?_, ?_⟩
    · have h := Int.ceil_le.mp hl.1
      dsimp [tiltedHeight]
      linarith only [h]
    · have h := Int.le_floor.mp hl.2
      dsimp [tiltedHeight]
      linarith only [h]
  · rintro ⟨hz, hlo, hhi⟩
    refine ⟨z.1, abs_le.mp hz, z.2, ⟨?_, ?_⟩, rfl⟩
    · apply Int.ceil_le.mpr
      dsimp [tiltedHeight] at hlo
      linarith only [hlo]
    · apply Int.le_floor.mpr
      dsimp [tiltedHeight] at hhi
      linarith only [hhi]

/-- Any column has at most n+1 lattice heights, also at nonintegral slopes. -/
theorem tilted_column_card_le (n : ℕ) (a : ℝ) :
    (Finset.Icc ⌈a⌉ ⌊a+(n : ℝ)⌋).card ≤ n+1 := by
  rw [Int.card_Icc, Int.floor_add_natCast]
  have h := Int.floor_le_ceil a
  omega

/-- Corrected geometric count: at most (2R+1)(n+1) actual candidate points. -/
theorem tiltedCandidates_card_le (n R : ℕ) (t : ℝ) :
    (tiltedCandidates n R t).card ≤ (2*R+1)*(n+1) := by
  classical
  have hcard : (Finset.Icc (-(R : ℤ)) R).card = 2*R+1 := by
    rw [Int.card_Icc]
    omega
  unfold tiltedCandidates
  calc
    _ ≤ (Finset.Icc (-(R : ℤ)) R).card * (n+1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun k _ =>
        (Finset.card_image_le).trans (tilted_column_card_le n (t*(k : ℝ))))
    _ = (2*R+1)*(n+1) := by rw [hcard]

/-- The local-minimum vertex is in the corrected candidate set, at height n
in the lower half of the height-2n strip. -/
theorem local_minimum_vertex_mem_candidates (n m : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration (2*n) t) (k : ℤ)
    (hk : |k| ≤ (n : ℤ)*(m : ℤ)^2)
    (hF : lowestTopConnectedHeight (2*n) (by omega) t ω k ≤ n) :
    (k,lowestTopConnectedVertex (2*n) (by omega) t ω k) ∈
      tiltedCandidates n (n*m^2) t := by
  apply (mem_tiltedCandidates _ _ _ _).mpr
  refine ⟨?_, (lowestTopConnectedHeight_mem (2*n) (by omega) t ω k).1, hF⟩
  simpa only [Nat.cast_mul, Nat.cast_pow] using hk

end PottsContinuity.Thm3.Prop4
