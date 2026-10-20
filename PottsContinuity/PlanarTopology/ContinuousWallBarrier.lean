module

public import PottsContinuity.PlanarTopology.ContinuousThreeArc
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

namespace PottsContinuity.PlanarTopology
noncomputable section

/-- Two path walls attached to opposite sides, joined by a continuous connector,
form a barrier to every opposite-direction crossing. The connector need not be
a lattice path. All contacts in the conclusion belong to the original walls. -/
theorem continuous_wall_barrier
    (l r b t : ℝ) {a d c e s w x y u v : ℝ × ℝ}
    (G : Path a d) (G' : Path c e) (L : Path s a) (R : Path w c)
    (P : Path x y) (Q : Path u v)
    (hG : ∀ z ∈ Set.range G, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hG' : ∀ z ∈ Set.range G', l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hL : ∀ z ∈ Set.range L, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hR : ∀ z ∈ Set.range R, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hP : ∀ z ∈ Set.range P, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hQ : ∀ z ∈ Set.range Q, l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t)
    (hs : s.1 = l) (hw : w.1 = r) (hx : x.2 = t) (hy : y.2 = b)
    (hGQ : (Set.range G ∩ Set.range Q).Nonempty)
    (hG'Q : (Set.range G' ∩ Set.range Q).Nonempty)
    (hPQ : Disjoint (Set.range P) (Set.range Q)) :
    ∃ z, z ∈ Set.range P ∧
      (z ∈ Set.range G ∨ z ∈ Set.range G' ∨ z ∈ Set.range L ∨ z ∈ Set.range R) := by
  have hI : IsPathConnected (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc _ _).isPathConnected ⟨0,by norm_num⟩
  let : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp hI
  let W := ((Set.range L ∪ Set.range G) ∪ Set.range Q) ∪ (Set.range G' ∪ Set.range R)
  have hLG : IsPathConnected (Set.range L ∪ Set.range G) :=
    (isPathConnected_range L.continuous).union (isPathConnected_range G.continuous)
      ⟨a,L.target_mem_range,G.source_mem_range⟩
  have hLGQ : IsPathConnected ((Set.range L ∪ Set.range G) ∪ Set.range Q) := by
    obtain ⟨z,hzG,hzQ⟩ := hGQ
    exact hLG.union (isPathConnected_range Q.continuous) ⟨z,Or.inr hzG,hzQ⟩
  have hGR : IsPathConnected (Set.range G' ∪ Set.range R) :=
    (isPathConnected_range G'.continuous).union (isPathConnected_range R.continuous)
      ⟨c,G'.source_mem_range,R.target_mem_range⟩
  have hW : IsPathConnected W := by
    obtain ⟨z,hzG,hzQ⟩ := hG'Q
    exact hLGQ.union hGR ⟨z,Or.inr hzQ,Or.inl hzG⟩
  have hsW : s ∈ W := Or.inl (Or.inl (Or.inl L.source_mem_range))
  have hwW : w ∈ W := Or.inr (Or.inr R.source_mem_range)
  obtain ⟨K,hK⟩ := hW.joinedIn s hsW w hwW
  have hKbox : ∀ θ, l ≤ (K θ).1 ∧ (K θ).1 ≤ r ∧ b ≤ (K θ).2 ∧ (K θ).2 ≤ t := by
    intro θ
    rcases hK θ with ((hz | hz) | hz) | (hz | hz)
    · exact hL _ hz
    · exact hG _ hz
    · exact hQ _ hz
    · exact hG' _ hz
    · exact hR _ hz
  have hPb := hP x P.source_mem_range
  obtain ⟨α,β,hαβ⟩ := PD.FK.Curves.pathRectangle_crossing_intersection
    (a := (l,b)) (b := (r,t)) K P.symm
    (by dsimp; linarith [hPb.1,hPb.2.1])
    (by dsimp; linarith [hPb.2.2.1,hPb.2.2.2]) hKbox
    (fun θ => hP _ ((Path.symm_range P) ▸ ⟨θ,rfl⟩))
    (by simpa using (congrArg Prod.fst K.source').trans hs)
    (by simpa using (congrArg Prod.fst K.target').trans hw)
    (by simpa using hy) (by simpa using hx)
  have hzP : K α ∈ Set.range P := by
    rw [hαβ]
    exact (Path.symm_range P) ▸ ⟨β,rfl⟩
  refine ⟨K α,hzP,?_⟩
  rcases hK α with ((hz | hz) | hz) | (hz | hz)
  · exact Or.inr (Or.inr (Or.inl hz))
  · exact Or.inl hz
  · exact False.elim (Set.disjoint_left.mp hPQ hzP hz)
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr (Or.inr hz))

end
end PottsContinuity.PlanarTopology
