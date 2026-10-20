-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/ConnectorGraph.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.FiniteTreeBranches
public import PottsContinuity.PD.RCInfinite.BoxConnector
public import PottsContinuity.PD.RCInfinite.SurgeryEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

abbrev BoxExitCarrier (n : ℕ) := BoxVertex (0, 0) n ⊕ Fin 3

/-- The finite connector consists of the box graph and one degree-one portal
for each chosen exit. -/
def boxExitConnectorGraph (n : ℕ) (exits : Fin 3 → BoxExit n) :
    SimpleGraph (BoxExitCarrier n) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inl b => (boxGraph (0, 0) n).Adj a b
    | Sum.inl a, Sum.inr j => a.val = boxExitInside (exits j)
    | Sum.inr j, Sum.inl a => boxExitInside (exits j) = a.val
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h.symm
    · exact h.symm
    · exact h.elim⟩
  loopless := ⟨by
    rintro x h
    cases x with
    | inl a => exact (boxGraph (0, 0) _).irrefl h
    | inr j => change False at h; exact h⟩

@[simp] theorem boxExitConnector_adj_inl_inl (n : ℕ)
    (exits : Fin 3 → BoxExit n) (a b : BoxVertex (0, 0) n) :
    (boxExitConnectorGraph n exits).Adj (Sum.inl a) (Sum.inl b) ↔
      (boxGraph (0, 0) n).Adj a b := Iff.rfl

@[simp] theorem boxExitConnector_adj_inl_inr (n : ℕ)
    (exits : Fin 3 → BoxExit n) (a : BoxVertex (0, 0) n) (j : Fin 3) :
    (boxExitConnectorGraph n exits).Adj (Sum.inl a) (Sum.inr j) ↔
      a.val = boxExitInside (exits j) := Iff.rfl

@[simp] theorem boxExitConnector_adj_inr_inl (n : ℕ)
    (exits : Fin 3 → BoxExit n) (j : Fin 3) (a : BoxVertex (0, 0) n) :
    (boxExitConnectorGraph n exits).Adj (Sum.inr j) (Sum.inl a) ↔
      boxExitInside (exits j) = a.val := Iff.rfl

def boxExitConnectorTerminals (n : ℕ) : Finset (BoxExitCarrier n) :=
  Finset.univ.image Sum.inr

theorem boxExitConnectorGraph_connected (n : ℕ) (exits : Fin 3 → BoxExit n) :
    (boxExitConnectorGraph n exits).Connected := by
  let C := boxExitConnectorGraph n exits
  let f : boxGraph (0, 0) n →g C :=
    { toFun := Sum.inl
      map_rel' := fun h => h }
  have lift {a b : BoxVertex (0, 0) n}
      (h : (boxGraph (0, 0) n).Reachable a b) : C.Reachable (Sum.inl a) (Sum.inl b) := by
    obtain ⟨w⟩ := h
    exact w.map f |>.reachable
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b => exact lift ((boxGraph_connected n).preconnected a b)
    | inr j =>
      let port : BoxVertex (0, 0) n := (exits j).val.1
      have hbox := (boxGraph_connected n).preconnected a port
      have hattach : C.Adj (Sum.inl port) (Sum.inr j) := by
        simp [C, boxExitConnectorGraph, port, boxExitInside]
      exact (lift hbox).trans hattach.reachable
  | inr j =>
    cases y with
    | inl b =>
      let port : BoxVertex (0, 0) n := (exits j).val.1
      have hbox := (boxGraph_connected n).preconnected port b
      have hattach : C.Adj (Sum.inr j) (Sum.inl port) := by
        simp [C, boxExitConnectorGraph, port, boxExitInside]
      exact hattach.reachable.trans (lift hbox)
    | inr k =>
      let portj : BoxVertex (0, 0) n := (exits j).val.1
      let portk : BoxVertex (0, 0) n := (exits k).val.1
      have hbox := (boxGraph_connected n).preconnected portj portk
      have hj : C.Adj (Sum.inr j) (Sum.inl portj) := by
        simp [C, boxExitConnectorGraph, portj, boxExitInside]
      have hk : C.Adj (Sum.inl portk) (Sum.inr k) := by
        simp [C, boxExitConnectorGraph, portk, boxExitInside]
      exact hj.reachable.trans
        ((lift hbox).trans hk.reachable)

def boxExitPortalIn (n : ℕ) (U : Finset (BoxExitCarrier n))
    (hTU : boxExitConnectorTerminals n ⊆ U) (j : Fin 3) : U :=
  ⟨Sum.inr j, hTU (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩

/-- A finite connector tree whose three portal vertices separate at a branch
point. -/
theorem exists_box_exit_connector_separator (n : ℕ) (exits : Fin 3 → BoxExit n) :
    ∃ U : Finset (BoxExitCarrier n), ∃ hTU : boxExitConnectorTerminals n ⊆ U,
      ∃ H : SimpleGraph (U : Set (BoxExitCarrier n)),
        H ≤ (boxExitConnectorGraph n exits).induce (U : Set (BoxExitCarrier n)) ∧
        H.IsTree ∧
        ∃ v, SeparatesThreeTerminals H
          (Finset.univ.image (boxExitPortalIn n U hTU)) v := by
  classical
  let C := boxExitConnectorGraph n exits
  let T := boxExitConnectorTerminals n
  obtain ⟨U, hTU, H, hHG, htree, hleaves⟩ :=
    exists_terminal_tree C (boxExitConnectorGraph_connected n exits) T
  let port := boxExitPortalIn n U hTU
  let T' : Finset U := Finset.univ.image port
  have hport_inj : Function.Injective port := by
    intro j k h
    exact Sum.inr.inj (congrArg Subtype.val h)
  have hT'card : T'.card = 3 := by
    rw [Finset.card_image_of_injective _ hport_inj]
    simp
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  let : Nontrivial U := ⟨⟨port 0, port 1, fun h => h01 (hport_inj h)⟩⟩
  have hportalDegree (j : Fin 3) : H.degree (port j) = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    have hconn := htree.preconnected.degree_pos_of_nontrivial (port j)
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj (G := H) (v := port j)).mp hconn
    have hbase : C.Adj (Sum.inr j) w.val := hHG hw
    refine ⟨w, hw, ?_⟩
    intro z hz
    have hzbase : C.Adj (Sum.inr j) z.val := hHG hz
    rcases w with ⟨wv, hwU⟩
    rcases z with ⟨zv, hzU⟩
    have hbase : C.Adj (Sum.inr j) wv := by simpa using hbase
    have hzbase : C.Adj (Sum.inr j) zv := by simpa using hzbase
    cases wv with
    | inl a =>
      have ha : boxExitInside (exits j) = a.val := by
        simpa [C, boxExitConnectorGraph] using hbase
      cases zv with
      | inl b =>
        have hb : boxExitInside (exits j) = b.val := by
          simpa [C, boxExitConnectorGraph] using hzbase
        apply Subtype.ext
        apply congrArg Sum.inl
        exact Subtype.ext (hb.symm.trans ha)
      | inr k => simp [C, boxExitConnectorGraph] at hzbase
    | inr k => simp [C, boxExitConnectorGraph] at hbase
  have hleaf (w : U) (hw : H.degree w = 1) : w ∈ T' := by
    have hwT := hleaves w hw
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hwT
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, Subtype.ext hj⟩
  have hTleaf (w : U) (hw : w ∈ T') : H.degree w = 1 := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hw
    rw [← hj]
    exact hportalDegree j
  obtain ⟨v, hv⟩ := tree_three_leaves_have_separator H htree T' hT'card hleaf hTleaf
  exact ⟨U, hTU, H, hHG, htree, v, hv⟩

end
end PottsContinuity.PD.RCInfinite
