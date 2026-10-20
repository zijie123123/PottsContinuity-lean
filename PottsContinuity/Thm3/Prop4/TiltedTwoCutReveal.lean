module

public import PottsContinuity.Thm3.Prop4.TiltedCutScan
public import PottsContinuity.Thm3.Prop4.CutScanPrefix
public import PottsContinuity.Thm3.Prop4.TiltedRemovedCuts

/-!
# A complete exterior stopping record between two scanned closed cuts

Successful left/right scans retain their surviving interval and reveal exactly
all non-inner edges. If either scan fails, the entire finite state is revealed.
This is an actual exploration on every configuration, with no missing branch.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance twoCutEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance twoCutEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- The inclusive surviving columns after increasing-left and decreasing-right
scans; failure means that there is no surviving interval. -/
def tiltedTwoCutBounds (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ)
    (A : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))) :
    Option (ℤ × ℤ) :=
  match (tiltedCutScan n M t (fun i => a+i) K A).2,
      (tiltedCutScan n M t (fun i => b-i) K A).2 with
  | some i,some j => some (a+i+1,b-j)
  | _,_ => none

/-- Reveal the complete exterior of a successfully isolated interval; on a
failed scan, reveal every original edge of the finite window. -/
def tiltedTwoCutReveal (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ)
    (A : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))) :
    PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) :=
  match tiltedTwoCutBounds n M t a b K A with
  | some (lo,hi) => PD.FK.subgraphRemovedEdges
      ((squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
        (tiltedIntervalEmbedding n M t lo hi))
      (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))
  | none => Finset.univ

/-- Both scans' actually tested edges belong to the complete exterior record. -/
theorem tiltedCutScans_tested_subset_reveal (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ)
    (A : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))) :
    (tiltedCutScan n M t (fun i => a+i) K A).1 ∪
      (tiltedCutScan n M t (fun i => b-i) K A).1 ⊆ tiltedTwoCutReveal n M t a b K A := by
  cases hL : (tiltedCutScan n M t (fun i => a+i) K A).2 with
  | none => simp [tiltedTwoCutReveal,tiltedTwoCutBounds,hL]
  | some i =>
    cases hR : (tiltedCutScan n M t (fun i => b-i) K A).2 with
    | none => simp [tiltedTwoCutReveal,tiltedTwoCutBounds,hR]
    | some j =>
      simp only [tiltedTwoCutReveal,tiltedTwoCutBounds,hL,hR]
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨r,hri,her⟩ := firstClosedBlockScan_tested_index_le
          (fun r => tiltedWindowCutEdges n M t (a+r)) A K i hL e he
        exact tiltedCutEdges_subset_intervalRemoved n M t (a+i+1) (b-j) (a+r)
          (Or.inl (by omega)) her
      · obtain ⟨r,hrj,her⟩ := firstClosedBlockScan_tested_index_le
          (fun r => tiltedWindowCutEdges n M t (b-r)) A K j hR e he
        exact tiltedCutEdges_subset_intervalRemoved n M t (a+i+1) (b-j) (b-r)
          (Or.inr (by omega)) her

private theorem agree_on_subset {E : Type*} [DecidableEq E]
    (A B R T : Finset E) (hT : T ⊆ R) (h : B ∩ R = A ∩ R) : B ∩ T = A ∩ T := by
  have h' := congrArg (fun S : Finset E => S ∩ T) h
  simpa only [Finset.inter_assoc,Finset.inter_eq_right.mpr hT] using h'

/-- Agreement on the complete exterior record fixes both scan results and
therefore fixes the random surviving interval and the revealed edge set. -/
theorem tiltedTwoCutReveal_stable (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ) :
    ∀ A B, B ∩ tiltedTwoCutReveal n M t a b K A = A ∩ tiltedTwoCutReveal n M t a b K A →
      tiltedTwoCutReveal n M t a b K B = tiltedTwoCutReveal n M t a b K A := by
  intro A B h
  have hsub := Finset.union_subset_iff.mp (tiltedCutScans_tested_subset_reveal n M t a b K A)
  have hL := tiltedCutScan_eq_of_agree n M t (fun i => a+i) K A B
    (agree_on_subset A B _ _ hsub.1 h)
  have hR := tiltedCutScan_eq_of_agree n M t (fun i => b-i) K A B
    (agree_on_subset A B _ _ hsub.2 h)
  unfold tiltedTwoCutReveal tiltedTwoCutBounds
  rw [hL,hR]

end

end PottsContinuity.Thm3.Prop4
