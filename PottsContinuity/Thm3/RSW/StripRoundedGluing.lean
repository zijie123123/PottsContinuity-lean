module

public import PottsContinuity.Thm3.RSW.StripInterlacing

/-! # Translated strip gluing without the divisible-scale restriction -/

@[expose] public section

namespace PottsContinuity.RSW

/-- The arc spacing can differ from n/9. A chain spanning at least the target
width still gives the literal crossing after contiguous coordinate clipping. -/
theorem strip_translated_connections_glue_of_scale_le
    (k : ℕ) (hk : 1 ≤ k) (n s : ℕ) (_hs : 1 ≤ s)
    (hns : n ≤ 9*s) :
    (⋂ j : Fin (18*k),
      stripLocalConnection n s (stripConnectionShift k s j)) ⊆
        stripHorizontalCrossing n
          (-⌊(k : ℝ)*(n : ℕ)⌋) ⌊(k : ℝ)*(n : ℕ)⌋
          0 (2*(n : ℕ)) := by
  classical
  let hinterlaced := strip_interlaced_walks_intersect n
  have hnz : (n : ℤ) ≤ 9*(s : ℤ) := by exact_mod_cast hns
  have hspan := mul_le_mul_of_nonneg_left hnz (Int.natCast_nonneg k)
  intro ω hω
  have hE : ∀ j : Fin (18 * k), ∃ (u v : stripVertices n)
      (w : (stripOpenGraph n ω).Walk u v),
      u.1 ∈ Set.Icc (stripConnectionShift k s j + 4 * s)
        (stripConnectionShift k s j + 5 * s) ×ˢ ({0} : Set ℤ) ∧
      v.1 ∈ Set.Icc (stripConnectionShift k s j + 6 * s)
        (stripConnectionShift k s j + 7 * s) ×ˢ ({0} : Set ℤ) ∧
      ∀ z ∈ w.support, z.1.2 ∈ Set.Icc (0 : ℤ) (2 * (n : ℕ)) := by
    intro j
    have hj := Set.mem_iInter.mp hω j
    obtain ⟨u, v, w, hu, hv, hw⟩ := hj
    refine ⟨u, v, w, hu, hv, ?_⟩
    intro z hz
    have h := hw z hz
    simp only [stripRectangleVertices, Finset.mem_preimage, latticeRectangle,
      Finset.mem_product, Finset.mem_Icc] at h
    exact h.2
  choose u v w hu hv hw using hE
  let m := 18 * k - 1
  have hm : m + 1 = 18 * k := by dsimp [m]; omega
  let idx : ℕ → Fin (18 * k) := fun j => ⟨min j m, by omega⟩
  have hidx (j : ℕ) (hj : j ≤ m) : (idx j).val = j := min_eq_left hj
  have hfloor : ⌊(k : ℝ) * (n : ℕ)⌋ = (k * n : ℕ) := by
    rw [← Nat.cast_mul, Int.floor_natCast]
  rw [hfloor]
  apply stripHorizontalCrossing_of_intersecting_chain n ω _ _ 0 _
    (by
      have hnonneg : (0 : ℤ) ≤ (k * n : ℕ) := Int.natCast_nonneg _
      omega) (fun j => u (idx j)) (fun j => v (idx j)) (fun j => w (idx j)) m
  · have h := (hu (idx 0)).1.2
    have hi := hidx 0 (Nat.zero_le m)
    dsimp [stripConnectionShift] at h
    rw [hi] at h
    push_cast at h ⊢
    nlinarith
  · have h := (hv (idx m)).1.1
    have hi := hidx m le_rfl
    dsimp [stripConnectionShift] at h
    rw [hi] at h
    have hmcast : (m : ℤ) + 1 = 18 * (k : ℤ) := by exact_mod_cast hm
    push_cast at h ⊢
    nlinarith
  · intro j _ z hz
    exact hw (idx j) z hz
  · intro j hj
    have hi := hidx j hj.le
    have hi' := hidx (j + 1) (by omega)
    apply hinterlaced ω (u (idx j)) (u (idx (j + 1))) (v (idx j)) (v (idx (j + 1)))
      (w (idx j)) (w (idx (j + 1)))
    · exact (hu (idx j)).2
    · exact (hu (idx (j + 1))).2
    · exact (hv (idx j)).2
    · exact (hv (idx (j + 1))).2
    · have h1 := (hu (idx j)).1.2
      have h2 := (hu (idx (j + 1))).1.1
      dsimp [stripConnectionShift] at h1 h2
      rw [hi] at h1
      rw [hi'] at h2
      push_cast at h2
      nlinarith
    · have h1 := (hu (idx (j + 1))).1.2
      have h2 := (hv (idx j)).1.1
      dsimp [stripConnectionShift] at h1 h2
      rw [hi'] at h1
      rw [hi] at h2
      push_cast at h1
      nlinarith
    · have h1 := (hv (idx j)).1.2
      have h2 := (hv (idx (j + 1))).1.1
      dsimp [stripConnectionShift] at h1 h2
      rw [hi] at h1
      rw [hi'] at h2
      push_cast at h2
      nlinarith
    · intro z hz
      exact (hw (idx j) z hz).1
    · intro z hz
      exact (hw (idx (j + 1)) z hz).1

end PottsContinuity.RSW
