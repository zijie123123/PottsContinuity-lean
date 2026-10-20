-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/FiniteBoxCounting.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.RCInfinite.Trifurcation
public import PottsContinuity.PD.RCInfinite.ComponentSeparators
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

@[expose] public section

open Set Finset

namespace PottsContinuity.PD.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- A finite walk from inside a set to outside it reaches a boundary vertex;
the initial segment stays in the set. -/
theorem walk_prefix_to_boundary {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : V} (w : G.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ z, z ∈ S ∧ ∃ p : G.Walk x z,
      (∀ u, u ∈ p.support → u ∈ S) ∧ ∃ y', G.Adj z y' ∧ y' ∉ S := by
  induction w with
  | nil => exact (hy hx).elim
  | @cons x y z h w ih =>
    by_cases hyS : y ∈ S
    · obtain ⟨t, htS, p, hpS, u, htu, hu⟩ := ih hyS hy
      refine ⟨t, htS, SimpleGraph.Walk.cons h p, ?_, u, htu, hu⟩
      intro a ha
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hx
      · exact hpS a ha
    · refine ⟨x, hx, SimpleGraph.Walk.nil, ?_, y, h, hyS⟩
      intro a ha
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at ha
      subst a
      exact hx

/-- Each infinite branch after deleting a trifurcation vertex reaches the
vertex boundary of every finite box containing the trifurcation. The path
lifts to the induced graph on that box. -/
theorem trifurcation_branch_reaches_boundary
    (ω : LatticeConfiguration) (v : LatticeVertex) (n : ℕ)
    (hv : v ∈ latticeBox (0, 0) n) (ys : Fin 3 → LatticeVertex)
    (hys : ∀ j, (rcInfiniteOpenGraph ω).Adj v (ys j) ∧ deletedInfiniteAt ω v (ys j)) :
    ∀ j : Fin 3, ∃ z : BoxVertex (0, 0) (n + 1),
      z.val ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) (n + 1)) ∧
      ((deletedOpenGraph ω v).induce (latticeBox (0, 0) (n + 1) : Set LatticeVertex)).Reachable
        ⟨ys j, by
          obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω v (ys j)).mp (hys j).1
          have hadj : squareLattice.Adj v (ys j) := squareLattice.mem_edgeSet.mp he
          change ys j ∈ latticeBox (0, 0) (n + 1)
          rw [mem_latticeBox] at hv ⊢
          rw [squareLattice_adj_iff] at hadj
          simp only at hv ⊢
          omega⟩ z := by
  intro j
  obtain ⟨y, hyout, hreach⟩ :=
    (deleted_infinite_iff_escape ω v (ys j)).mp (hys j).2 (latticeBox (0, 0) (n + 1))
  obtain ⟨w⟩ := hreach
  have hysBox : ys j ∈ latticeBox (0, 0) (n + 1) := by
    obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω v (ys j)).mp (hys j).1
    have hadj : squareLattice.Adj v (ys j) := squareLattice.mem_edgeSet.mp he
    rw [mem_latticeBox] at hv ⊢
    rw [squareLattice_adj_iff] at hadj
    simp only at hv ⊢
    omega
  obtain ⟨z, hz, p, hpS, y', hzy', hy'⟩ :=
    walk_prefix_to_boundary w hysBox (by simpa using hyout)
  have hboundary : z ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) (n + 1)) := by
    refine ⟨by simpa using hz, ?_⟩
    refine ⟨y', ?_, ?_⟩
    · have hOpen : (rcInfiniteOpenGraph ω).Adj z y' :=
        (SimpleGraph.deleteIncidenceSet_adj.mp hzy').1
      obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω z y').mp hOpen
      exact squareLattice.mem_edgeSet.mp he
    · simpa using hy'
  have hpath := p.induce (latticeBox (0, 0) (n + 1) : Set LatticeVertex) hpS
  refine ⟨⟨z, ?_⟩, ?_, hpath.reachable⟩
  · change z ∈ (latticeBox (0, 0) (n + 1) : Set LatticeVertex)
    exact hz
  · exact hboundary

/-- The finite open graph induced on a lattice box. -/
def boxOpenGraph (ω : LatticeConfiguration) (n : ℕ) : SimpleGraph (BoxVertex (0, 0) n) :=
  (rcInfiniteOpenGraph ω).induce (latticeBox (0, 0) n : Set LatticeVertex)

/-- The vertices on the geometric boundary of a box, viewed on its finite carrier. -/
def boxBoundaryVertices (n : ℕ) : Finset (BoxVertex (0, 0) n) :=
  Finset.univ.filter (fun x =>
    x.val ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) n))

theorem box_boundary_coordinate_edge (n : ℕ) {x : LatticeVertex}
    (hx : x ∈ PottsContinuity.PD.vertexBoundary (latticeBox (0, 0) n)) :
    x.1 = -(n : ℤ) ∨ x.1 = (n : ℤ) ∨ x.2 = -(n : ℤ) ∨ x.2 = (n : ℤ) := by
  rw [PottsContinuity.PD.vertexBoundary] at hx
  rcases hx with ⟨hin, y, hadj, hout⟩
  rw [mem_latticeBox] at hin hout
  rw [squareLattice_adj_iff] at hadj
  simp only at hin hout
  omega

def boxLeftSide (n : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image (fun y => (-(n : ℤ), y))

def boxRightSide (n : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image (fun y => ((n : ℤ), y))

def boxBottomSide (n : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image (fun x => (x, -(n : ℤ)))

def boxTopSide (n : ℕ) : Finset LatticeVertex :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image (fun x => (x, (n : ℤ)))

def boxPerimeter (n : ℕ) : Finset LatticeVertex :=
  ((boxLeftSide n ∪ boxRightSide n) ∪ boxBottomSide n) ∪ boxTopSide n

theorem card_box_side (n : ℕ) (s : Finset LatticeVertex)
    (hs : s = boxLeftSide n ∨ s = boxRightSide n ∨
      s = boxBottomSide n ∨ s = boxTopSide n) : s.card = 2 * n + 1 := by
  have hI : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    have hcast : (n : ℤ) + 1 - (-(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by
      push_cast
      omega
    rw [hcast]
    norm_cast
  rcases hs with hs | hs | hs | hs
  · subst s
    simp only [boxLeftSide]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.snd h), hI]
  · subst s
    simp only [boxRightSide]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.snd h), hI]
  · subst s
    simp only [boxBottomSide]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h), hI]
  · subst s
    simp only [boxTopSide]
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h), hI]

theorem box_boundary_values_subset_perimeter (n : ℕ) :
    (boxBoundaryVertices n).image (fun x => x.val) ⊆ boxPerimeter n := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  have hb := (Finset.mem_filter.mp hv).2
  have hcoord := box_boundary_coordinate_edge n hb
  have hvbox : v.val ∈ latticeBox (0, 0) n := v.property
  rw [mem_latticeBox] at hvbox
  simp only at hvbox
  have hylo : -(n : ℤ) ≤ v.val.2 := by omega
  have hyhi : v.val.2 ≤ (n : ℤ) := by omega
  have hxlo : -(n : ℤ) ≤ v.val.1 := by omega
  have hxhi : v.val.1 ≤ (n : ℤ) := by omega
  have hleft (h : v.val.1 = -(n : ℤ)) : v.val ∈ boxLeftSide n := by
    rw [boxLeftSide, Finset.mem_image]
    refine ⟨v.val.2, Finset.mem_Icc.mpr ⟨hylo, hyhi⟩, ?_⟩
    exact Prod.ext h.symm rfl
  have hright (h : v.val.1 = (n : ℤ)) : v.val ∈ boxRightSide n := by
    rw [boxRightSide, Finset.mem_image]
    refine ⟨v.val.2, Finset.mem_Icc.mpr ⟨hylo, hyhi⟩, ?_⟩
    exact Prod.ext h.symm rfl
  have hbottom (h : v.val.2 = -(n : ℤ)) : v.val ∈ boxBottomSide n := by
    rw [boxBottomSide, Finset.mem_image]
    refine ⟨v.val.1, Finset.mem_Icc.mpr ⟨hxlo, hxhi⟩, ?_⟩
    exact Prod.ext rfl h.symm
  have htop (h : v.val.2 = (n : ℤ)) : v.val ∈ boxTopSide n := by
    rw [boxTopSide, Finset.mem_image]
    refine ⟨v.val.1, Finset.mem_Icc.mpr ⟨hxlo, hxhi⟩, ?_⟩
    exact Prod.ext rfl h.symm
  rw [boxPerimeter]
  simp only [Finset.mem_union]
  rcases hcoord with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (hleft h)))
  · exact Or.inl (Or.inl (Or.inr (hright h)))
  · exact Or.inl (Or.inr (hbottom h))
  · exact Or.inr (htop h)

theorem box_boundary_card_le (n : ℕ) : (boxBoundaryVertices n).card ≤ 4 * (2 * n + 1) := by
  have hcardImage : (boxBoundaryVertices n).card =
      ((boxBoundaryVertices n).image (fun x => x.val)).card := by
    symm
    apply Finset.card_image_of_injective
    exact Subtype.val_injective
  calc
    (boxBoundaryVertices n).card =
        ((boxBoundaryVertices n).image (fun x => x.val)).card := hcardImage
    _ ≤ (boxPerimeter n).card := Finset.card_le_card (box_boundary_values_subset_perimeter n)
    _ ≤ ((boxLeftSide n).card + (boxRightSide n).card +
        (boxBottomSide n).card) + (boxTopSide n).card := by
      calc
        (boxPerimeter n).card ≤
            ((boxLeftSide n ∪ boxRightSide n) ∪ boxBottomSide n).card +
              (boxTopSide n).card := by
                rw [boxPerimeter]
                exact Finset.card_union_le _ _
        _ ≤ ((boxLeftSide n ∪ boxRightSide n).card + (boxBottomSide n).card) +
              (boxTopSide n).card := Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ ((boxLeftSide n).card + (boxRightSide n).card + (boxBottomSide n).card) +
              (boxTopSide n).card := by
                apply Nat.add_le_add_right
                exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = 4 * (2 * n + 1) := by
      rw [card_box_side n (boxLeftSide n) (Or.inl rfl),
        card_box_side n (boxRightSide n) (Or.inr (Or.inl rfl)),
        card_box_side n (boxBottomSide n) (Or.inr (Or.inr (Or.inl rfl))),
        card_box_side n (boxTopSide n) (Or.inr (Or.inr (Or.inr rfl)))]
      omega

theorem reachable_deleteIncidenceSet_to_root {V : Type*} {G : SimpleGraph V}
    {v x : V} (h : (G.deleteIncidenceSet v).Reachable x v) : x = v := by
  by_contra hne
  obtain ⟨w⟩ := h
  have hne' : v ≠ x := fun heq => hne heq.symm
  obtain ⟨u, hadj, tail, _⟩ := w.reverse.exists_eq_cons_of_ne hne'
  exact (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1 rfl

theorem trifurcation_in_box_is_separator
    (ω : LatticeConfiguration) (n : ℕ) (v : BoxVertex (0, 0) n)
    (htri : isTrifurcationAt ω v.val) :
    (⟨v.val, by
      apply latticeBox_mono (c := (0, 0)) (show n ≤ n + 1 by omega)
      exact v.property⟩ : BoxVertex (0, 0) (n + 1)) ∈
      separatingTerminals (boxOpenGraph ω (n + 1))
        (boxBoundaryVertices (n + 1) : Set (BoxVertex (0, 0) (n + 1))) := by
  classical
  obtain ⟨ys, hys, hsep⟩ := htri
  let S : Set LatticeVertex := latticeBox (0, 0) (n + 1)
  let v' : BoxVertex (0, 0) (n + 1) :=
    ⟨v.val, latticeBox_mono (c := (0, 0)) (show n ≤ n + 1 by omega) v.property⟩
  have hb := trifurcation_branch_reaches_boundary ω v.val n v.property ys hys
  choose zs hzs using hb
  have hysBox (j : Fin 3) : ys j ∈ latticeBox (0, 0) (n + 1) := by
    obtain ⟨he, _⟩ := (rcInfiniteOpenGraph_adj ω v.val (ys j)).mp (hys j).1
    have hadj := squareLattice.mem_edgeSet.mp he
    have hv' := v.property
    rw [mem_latticeBox] at hv' ⊢
    rw [squareLattice_adj_iff] at hadj
    simp only at hv' ⊢
    omega
  let y' : Fin 3 → BoxVertex (0, 0) (n + 1) := fun j => ⟨ys j, hysBox j⟩
  let G := boxOpenGraph ω (n + 1)
  let D := (deletedOpenGraph ω v.val).induce S
  have hbranch (j : Fin 3) : D.Reachable (y' j) (zs j) := by
    exact (hzs j).2
  let toOpen : D →g G := {
    toFun := fun x => x
    map_rel' := by
      intro x y hxy
      change (deletedOpenGraph ω v.val).Adj x.val y.val at hxy
      rw [deletedOpenGraph, SimpleGraph.deleteIncidenceSet_adj] at hxy
      change (rcInfiniteOpenGraph ω).Adj x.val y.val
      exact hxy.1
  }
  let toDeleted : G.deleteIncidenceSet v' →g deletedOpenGraph ω v.val := {
    toFun := fun x => x.val
    map_rel' := by
      intro x y hxy
      rw [SimpleGraph.deleteIncidenceSet_adj] at hxy
      have hGxy : G.Adj x y := hxy.1
      have hOpen : (rcInfiniteOpenGraph ω).Adj x.val y.val :=
        SimpleGraph.induce_adj.mp hGxy
      have hne1 : x.val ≠ v.val := by
        intro heq
        apply hxy.2.1
        exact Subtype.ext heq
      have hne2 : y.val ≠ v.val := by
        intro heq
        apply hxy.2.2
        exact Subtype.ext heq
      rw [deletedOpenGraph, SimpleGraph.deleteIncidenceSet_adj]
      exact ⟨hOpen, hne1, hne2⟩
  }
  have hyreach (j : Fin 3) : G.Reachable v' (y' j) := by
    have hadj : G.Adj v' (y' j) := by
      change (rcInfiniteOpenGraph ω).Adj v.val (ys j)
      exact (hys j).1
    exact hadj.reachable
  have hzreach (j : Fin 3) : G.Reachable (y' j) (zs j) := (hbranch j).map toOpen
  have hvreach (j : Fin 3) : G.Reachable v' (zs j) := (hyreach j).trans (hzreach j)
  have hznotv (j : Fin 3) : (zs j).val ≠ v.val := by
    intro heq
    have hreach : (deletedOpenGraph ω v.val).Reachable (ys j) v.val :=
      (hbranch j).map {
        toFun := fun x => x.val
        map_rel' := fun hxy => (SimpleGraph.induce_adj.mp hxy)
      } |> fun hh => by simpa [heq, y'] using hh
    have hx : ys j = v.val := reachable_deleteIncidenceSet_to_root hreach
    have hAdj := (hys j).1
    rw [hx] at hAdj
    exact ((rcInfiniteOpenGraph ω).irrefl) hAdj
  have hsepLocal (j k : Fin 3) (hjk : j ≠ k) :
      ¬(G.deleteIncidenceSet v').Reachable (zs j) (zs k) := by
    intro hlocal
    have hglobal := hlocal.map toDeleted
    have hleft : (deletedOpenGraph ω v.val).Reachable (ys j) (zs j) := by
      exact (hbranch j).map {
        toFun := fun x => x.val
        map_rel' := fun hxy => SimpleGraph.induce_adj.mp hxy
      }
    have hright : (deletedOpenGraph ω v.val).Reachable (zs k) (ys k) := by
      exact ((hbranch k).map {
        toFun := fun x => x.val
        map_rel' := fun hxy => SimpleGraph.induce_adj.mp hxy
      }).symm
    exact hsep j k hjk (hleft.trans (hglobal.trans hright))
  have hterm (j : Fin 3) : zs j ∈ (boxBoundaryVertices (n + 1) : Set _) := by
    simp only [boxBoundaryVertices, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (hzs j).1
  have hne (j : Fin 3) : zs j ≠ v' := by
    intro heq
    exact hznotv j (congrArg Subtype.val heq)
  have hsep3 : SeparatesThreeTerminals G (boxBoundaryVertices (n + 1) : Set _) v' := by
    refine ⟨zs, ?_, hsepLocal⟩
    intro j
    exact ⟨hvreach j, hterm j, hne j⟩
  simpa only [separatingTerminals, Finset.mem_filter, Finset.mem_univ, true_and] using hsep3

def boxTrifurcationVertices (ω : LatticeConfiguration) (n : ℕ) :
    Finset (BoxVertex (0, 0) n) :=
  Finset.univ.filter (fun v => isTrifurcationAt ω v.val)

theorem box_trifurcation_card_le_boundary (ω : LatticeConfiguration) (n : ℕ) :
    (boxTrifurcationVertices ω n).card ≤ (boxBoundaryVertices (n + 1)).card := by
  classical
  let G := boxOpenGraph ω (n + 1)
  let T := boxBoundaryVertices (n + 1)
  let S := separatingTerminals G (T : Set (BoxVertex (0, 0) (n + 1)))
  let f : {v // v ∈ boxTrifurcationVertices ω n} → S := fun v =>
    ⟨⟨v.val.val,
      latticeBox_mono (c := (0, 0)) (show n ≤ n + 1 by omega) v.val.property⟩,
      trifurcation_in_box_is_separator ω n v.val (Finset.mem_filter.mp v.property).2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => z.val.val) hxy
  have hcard : (boxTrifurcationVertices ω n).card ≤ S.card := by
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe] using hc
  have hsep := finite_graph_terminal_separator_card_le G T
  exact hcard.trans (by simpa only [S, T, G] using hsep)

end
end PottsContinuity.PD.RCInfinite
