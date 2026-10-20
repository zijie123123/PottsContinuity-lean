-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FirstClosedBlockScan.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {E ι : Type*} [DecidableEq E] [DecidableEq ι]

/-- The union of the edge blocks in a finite ordered list. -/
def firstClosedBlockUnion (D : ι → Finset E) : List ι → Finset E
  | [] => ∅
  | j :: js => D j ∪ firstClosedBlockUnion D js

/-- Scan blocks in order. The tested set contains each failed block and the first
block disjoint from the actual open set, if one exists; blocks after a hit are
not tested. -/
def firstClosedBlockScan (D : ι → Finset E) (A : Finset E) :
    List ι → Finset E × Option ι
  | [] => (∅, none)
  | j :: js =>
      if Disjoint A (D j) then (D j, some j)
      else
        let tail := firstClosedBlockScan D A js
        (D j ∪ tail.1, tail.2)

private theorem finset_inter_left_of_inter_union_eq
    (A B U V : Finset E) (h : B ∩ (U ∪ V) = A ∩ (U ∪ V)) :
    B ∩ U = A ∩ U := by
  ext x
  have hx : (x ∈ B ∧ (x ∈ U ∨ x ∈ V)) ↔
      (x ∈ A ∧ (x ∈ U ∨ x ∈ V)) := by
    simpa only [Finset.mem_inter, Finset.mem_union] using
      Iff.of_eq (congrArg (fun S : Finset E => x ∈ S) h)
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxB, hxU⟩
    have hx' := hx.mp ⟨hxB, Or.inl hxU⟩
    exact ⟨hx'.1, hxU⟩
  · rintro ⟨hxA, hxU⟩
    have hx' := hx.mpr ⟨hxA, Or.inl hxU⟩
    exact ⟨hx'.1, hxU⟩

omit [DecidableEq ι] in
/-- Agreement on the tested edge set fixes both the tested set and the first
closed block (including `none`). -/
theorem firstClosedBlockScan_eq_of_agree
    (D : ι → Finset E) (A B : Finset E) (js : List ι)
    (h : B ∩ (firstClosedBlockScan D A js).1 =
      A ∩ (firstClosedBlockScan D A js).1) :
    firstClosedBlockScan D B js = firstClosedBlockScan D A js := by
  induction js with
  | nil => simp [firstClosedBlockScan]
  | cons j js ih =>
      by_cases hdisj : Disjoint A (D j)
      · have hhead : B ∩ D j = A ∩ D j := by
          simpa [firstClosedBlockScan, hdisj] using h
        have hdisjB : Disjoint B (D j) := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          rw [hhead]
          exact Finset.disjoint_iff_inter_eq_empty.mp hdisj
        simp [firstClosedBlockScan, hdisj, hdisjB]
      · have hscan : B ∩ (D j ∪ (firstClosedBlockScan D A js).1) =
            A ∩ (D j ∪ (firstClosedBlockScan D A js).1) := by
          simpa [firstClosedBlockScan, hdisj] using h
        have hhead := finset_inter_left_of_inter_union_eq A B (D j)
          (firstClosedBlockScan D A js).1 hscan
        have htail : B ∩ (firstClosedBlockScan D A js).1 =
            A ∩ (firstClosedBlockScan D A js).1 := by
          ext x
          have hx : (x ∈ B ∧ (x ∈ D j ∨ x ∈ (firstClosedBlockScan D A js).1)) ↔
              (x ∈ A ∧ (x ∈ D j ∨ x ∈ (firstClosedBlockScan D A js).1)) := by
            simpa only [Finset.mem_inter, Finset.mem_union] using
              Iff.of_eq (congrArg (fun S : Finset E => x ∈ S) hscan)
          simp only [Finset.mem_inter]
          constructor
          · rintro ⟨hxB, hxTail⟩
            have hx' := hx.mp ⟨hxB, Or.inr hxTail⟩
            exact ⟨hx'.1, hxTail⟩
          · rintro ⟨hxA, hxTail⟩
            have hx' := hx.mpr ⟨hxA, Or.inr hxTail⟩
            exact ⟨hx'.1, hxTail⟩
        have hdisjB : Disjoint B (D j) ↔ Disjoint A (D j) := by
          rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty,
            hhead]
        have htailEq := ih htail
        simp [firstClosedBlockScan, hdisj, hdisjB, htailEq]

omit [DecidableEq ι] in
/-- A successful scan returns an index from the input list and its block is
actually closed (disjoint from the open edge set). -/
theorem firstClosedBlockScan_hit
    (D : ι → Finset E) (A : Finset E) (js : List ι) (j : ι)
    (h : (firstClosedBlockScan D A js).2 = some j) :
    j ∈ js ∧ Disjoint A (D j) := by
  induction js with
  | nil => simp [firstClosedBlockScan] at h
  | cons i js ih =>
      by_cases hi : Disjoint A (D i)
      · simp [firstClosedBlockScan, hi] at h
        subst j
        exact ⟨by simp, hi⟩
      · have htail : (firstClosedBlockScan D A js).2 = some j := by
          simpa [firstClosedBlockScan, hi] using h
        rcases ih htail with ⟨hmem, hclosed⟩
        exact ⟨by simp [hmem], hclosed⟩

omit [DecidableEq ι] in
/-- `none` is returned exactly when every listed block meets the open set. -/
theorem firstClosedBlockScan_none_iff
    (D : ι → Finset E) (A : Finset E) (js : List ι) :
    (firstClosedBlockScan D A js).2 = none ↔
      ∀ j ∈ js, ¬ Disjoint A (D j) := by
  induction js with
  | nil => simp [firstClosedBlockScan]
  | cons j js ih =>
      by_cases hj : Disjoint A (D j)
      · simp [firstClosedBlockScan, hj]
      · simp [firstClosedBlockScan, hj, ih]

omit [DecidableEq ι] in
/-- A successful scan stops exactly at its first disjoint block; every earlier
block intersects the open set, and no later block contributes to the tested set. -/
theorem firstClosedBlockScan_hit_prefix
    (D : ι → Finset E) (A : Finset E) (js : List ι) (j : ι)
    (h : (firstClosedBlockScan D A js).2 = some j) :
    ∃ pre post : List ι, js = pre ++ j :: post ∧
      (∀ i ∈ pre, ¬ Disjoint A (D i)) ∧ Disjoint A (D j) ∧
      (firstClosedBlockScan D A js).1 = firstClosedBlockUnion D (pre ++ [j]) := by
  induction js with
  | nil => simp [firstClosedBlockScan] at h
  | cons i js ih =>
      by_cases hi : Disjoint A (D i)
      · simp [firstClosedBlockScan, hi] at h
        subst j
        refine ⟨[], js, ?_, ?_, hi, ?_⟩
        · simp
        · simp
        · simp [firstClosedBlockScan, hi, firstClosedBlockUnion]
      · have htail : (firstClosedBlockScan D A js).2 = some j := by
          simpa [firstClosedBlockScan, hi] using h
        obtain ⟨pre, post, hjs, hpre, hj, htested⟩ := ih htail
        refine ⟨i :: pre, post, ?_, ?_, hj, ?_⟩
        · simp [hjs]
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hi
          · exact hpre x hx
        · rw [hjs]
          rw [hjs] at htested
          simpa [firstClosedBlockUnion, firstClosedBlockScan, hi] using
            congrArg (fun F : Finset E => D i ∪ F) htested

end
end PottsContinuity.FKC.FiniteFK
