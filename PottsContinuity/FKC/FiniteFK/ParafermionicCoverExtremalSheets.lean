-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverExtremalSheets.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRectangleBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC
noncomputable section

local instance coverExtremalVertexFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _
local instance coverExtremalVertexDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientVertex n) := Classical.decEq _
local instance coverExtremalBaseFintype (n : ℕ) :
    Fintype {x // x ∈ latticeBox (0,0) n} := Fintype.ofFinite _

def coverExtremalSheetEmbedding (n : ℕ) (b : Bool) :
    {x // x ∈ latticeBox (0,0) n} ↪ ParafermionicAmbientVertex n := by
  let N : ℤ := ((n ^ 5 : ℕ) : ℤ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨fun x => ⟨(x.1, if b then N else -N), ?_⟩, ?_⟩
  · change (x.1, if b then N else -N) ∈ parafermionicCoverBoxFinset n
    rw [parafermionicCoverBoxFinset, Finset.mem_product]
    constructor
    · exact x.2
    · simp only [Finset.mem_Icc]
      cases b <;> simp only [ite_eq_left, ite_eq_right, Bool.false_eq_true, not_false_eq_true,
        ] <;> norm_cast <;> omega
  · intro x y h
    have hp := congrArg Subtype.val h
    have hx : x.1 = y.1 := congrArg Prod.fst hp
    exact Subtype.ext hx

def coverExtremalSheetImage (n : ℕ) (b : Bool) :
    Finset (ParafermionicAmbientVertex n) :=
  Finset.univ.map (coverExtremalSheetEmbedding n b)

/-- The two literal extremal sheet slices of the finite cover carrier. -/
def parafermionicCoverExtremalSheetVertices (n : ℕ) :
    Finset (ParafermionicAmbientVertex n) :=
  coverExtremalSheetImage n true ∪ coverExtremalSheetImage n false

@[simp] theorem mem_parafermionicCoverExtremalSheetVertices
    (n : ℕ) (v : ParafermionicAmbientVertex n) :
    v ∈ parafermionicCoverExtremalSheetVertices n ↔
      v.1.2 = ((n ^ 5 : ℕ) : ℤ) ∨ v.1.2 = -((n ^ 5 : ℕ) : ℤ) := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hp | hm
    · obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hp
      have hs := congrArg (fun z : ParafermionicAmbientVertex n => z.1.2) hx
      change ((n ^ 5 : ℕ) : ℤ) = v.1.2 at hs
      exact Or.inl hs.symm
    · obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hm
      have hs := congrArg (fun z : ParafermionicAmbientVertex n => z.1.2) hx
      change -((n ^ 5 : ℕ) : ℤ) = v.1.2 at hs
      exact Or.inr hs.symm
  · intro hv
    have hvbox : v.1 ∈ parafermionicCoverBoxVertices n := by
      exact v.2
    have hmem := (parafermionicCoverBoxVertices_mem n v.1).mp hvbox
    have hbase : v.1.1 ∈ latticeBox (0,0) n := by
      rw [mem_latticeBox]
      exact ⟨⟨by simpa using hmem.1, by simpa using hmem.2.1⟩,
        ⟨by simpa using hmem.2.2.1, by simpa using hmem.2.2.2.1⟩⟩
    let x : {x // x ∈ latticeBox (0,0) n} := ⟨v.1.1, hbase⟩
    rcases hv with hplus | hminus
    · apply Finset.mem_union.mpr
      left
      refine Finset.mem_map.mpr ⟨x, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hplus.symm
    · apply Finset.mem_union.mpr
      right
      refine Finset.mem_map.mpr ⟨x, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hminus.symm

theorem parafermionicCoverExtremalSheetVertices_card
    (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverExtremalSheetVertices n).card =
      2 * (2 * n + 1) ^ 2 := by
  classical
  have hdisj : Disjoint (coverExtremalSheetImage n true)
      (coverExtremalSheetImage n false) := by
    rw [Finset.disjoint_left]
    intro v hv hm
    obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hv
    obtain ⟨y, -, hy⟩ := Finset.mem_map.mp hm
    have hxy := congrArg (fun z : ParafermionicAmbientVertex n => z.1.2)
      (hx.trans hy.symm)
    change ((n ^ 5 : ℕ) : ℤ) = -((n ^ 5 : ℕ) : ℤ) at hxy
    have hpos : 0 < ((n ^ 5 : ℕ) : ℤ) := by
      exact_mod_cast Nat.pow_pos (by omega : 0 < n)
    omega
  rw [parafermionicCoverExtremalSheetVertices, Finset.card_union_of_disjoint hdisj]
  have hcard (b : Bool) : (coverExtremalSheetImage n b).card = (2 * n + 1) ^ 2 := by
    rw [coverExtremalSheetImage, Finset.card_map, Finset.card_univ, Fintype.card_coe,
      card_latticeBox]
  rw [hcard true, hcard false]
  ring

/-- The origin vertex in the actual finite cover box. -/
def parafermionicCoverBoxOrigin (n : ℕ) : ParafermionicAmbientVertex n :=
  ⟨((0,0),0), by
    rw [parafermionicCoverBoxFinset, Finset.mem_product]
    exact ⟨center_mem_latticeBox (0,0) n, by simp⟩⟩

@[simp] theorem parafermionicCoverBoxOrigin_val (n : ℕ) :
    (parafermionicCoverBoxOrigin n).1 = ((0,0),0) := rfl

end
end PottsContinuity.FKC.FiniteFK
