module

public import PottsContinuity.Thm3.RSW.WalkClipping

/-!
# Joining chains of actual paths while retaining the vertical constraint

Consecutive shared vertices suffice for a confined-band spanning walk. Clipping
then supplies the actual rectangle crossing. The planar statement forcing
intersection of interlaced bottom-to-bottom paths is proved in
`Thm3.RSW.StripInterlacing` (`strip_interlaced_walks_intersect`).
-/

@[expose] public section

namespace PottsContinuity.RSW

/-- A finite chain of walks with consecutive intersections can be joined,
retaining every vertex constraint satisfied by the original walks. -/
theorem walk_chain_of_consecutive_intersections {V : Type*} (G : SimpleGraph V)
    (P : V → Prop) (u v : ℕ → V) (w : ∀ j : ℕ, G.Walk (u j) (v j))
    (m : ℕ) (hP : ∀ j ≤ m, ∀ z ∈ (w j).support, P z)
    (hinter : ∀ j < m, ∃ z, z ∈ (w j).support ∧ z ∈ (w (j + 1)).support) :
    ∃ p : G.Walk (u 0) (v m), ∀ z ∈ p.support, P z := by
  classical
  have happend : ∀ {x y z : V} (p : G.Walk x y) (r : G.Walk y z),
      (∀ t ∈ p.support, P t) → (∀ t ∈ r.support, P t) →
      ∀ t ∈ (p.append r).support, P t := by
    intro x y z p r hp hr t ht
    rcases (SimpleGraph.Walk.mem_support_append_iff p r).mp ht with ht | ht
    · exact hp t ht
    · exact hr t ht
  induction m with
  | zero => exact ⟨w 0, hP 0 le_rfl⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih (fun j hj => hP j (Nat.le.step hj))
      (fun j hj => hinter j (Nat.lt_succ_of_lt hj))
    obtain ⟨z, hz, hz'⟩ := hinter m (Nat.lt_succ_self m)
    let r := ((p.append (w m).reverse).append ((w m).takeUntil z hz)).append
      ((w (m + 1)).dropUntil z hz')
    refine ⟨r, ?_⟩
    apply happend
    · apply happend
      · apply happend p (w m).reverse hp
        intro t ht
        apply hP m (Nat.le_succ m) t
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ht
      · intro t ht
        exact hP m (Nat.le_succ m) t ((w m).support_takeUntil_subset_support hz ht)
    · intro t ht
      exact hP (m + 1) le_rfl t ((w (m + 1)).support_dropUntil_subset_support hz' ht)

/-- A chain of actual open strip paths that spans the horizontal interval and
stays in the vertical band yields a crossing confined to the target rectangle. -/
theorem stripHorizontalCrossing_of_intersecting_chain
    (n : ℕ) (ω : StripConfiguration n) (a b c d : ℤ) (hab : a ≤ b)
    (u v : ℕ → stripVertices n)
    (w : ∀ j : ℕ, (stripOpenGraph n ω).Walk (u j) (v j))
    (m : ℕ) (hleft : (u 0).1.1 ≤ a) (hright : b ≤ (v m).1.1)
    (hband : ∀ j ≤ m, ∀ z ∈ (w j).support, z.1.2 ∈ Set.Icc c d)
    (hinter : ∀ j < m, ∃ z, z ∈ (w j).support ∧ z ∈ (w (j + 1)).support) :
    ω ∈ stripHorizontalCrossing n a b c d := by
  obtain ⟨p, hp⟩ := walk_chain_of_consecutive_intersections (stripOpenGraph n ω)
    (fun z => z.1.2 ∈ Set.Icc c d) u v w m hband hinter
  have hstep : ∀ {u v : stripVertices n}, (stripOpenGraph n ω).Adj u v →
      v.1.1 ≤ u.1.1 + 1 := by
    intro u v huv
    have hsq := stripOpenGraph_le n ω huv
    change |u.1.1 - v.1.1| + |u.1.2 - v.1.2| = 1 at hsq
    have := abs_nonneg (u.1.2 - v.1.2)
    have := neg_le_abs (u.1.1 - v.1.1)
    omega
  obtain ⟨x, y, r, hx, hy, hr⟩ := walk_clip_coordinate (stripOpenGraph n ω)
    (fun z => z.1.1) hstep a b hab (fun z => z.1.2 ∈ Set.Icc c d)
    p hleft hright hp
  refine ⟨x, y, r, ⟨hx, (hr x r.start_mem_support).2.2⟩,
    ⟨hy, (hr y r.end_mem_support).2.2⟩, ?_⟩
  intro z hz
  exact ⟨⟨(hr z hz).1, (hr z hz).2.1⟩, (hr z hz).2.2⟩

end PottsContinuity.RSW
