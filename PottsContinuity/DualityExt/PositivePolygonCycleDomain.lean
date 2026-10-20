module

public import PottsContinuity.DualityExt.PositivePolygonLatticeCycle
public import PottsContinuity.FKC.Domains.LatticePolygonOfCycle
public import PottsContinuity.FKC.Domains.PolygonDomain

@[expose] public section

namespace PottsContinuity.DualityExt
open PottsContinuity.FKC
open PottsContinuity.FKC.LatticePolygon
open OAI.SLEExactGauge
open SimpleGraph
open Set
noncomputable section

def p5aForwardCycle {m : ℕ} (P : LatticePolygon m) := (polygonCycle P).reverse

 theorem p5aForwardCycle_isCycle {m : ℕ} (P : LatticePolygon m) :
    (p5aForwardCycle P).IsCycle :=
  (polygonCycle_isCycle P).reverse

private theorem p5aCyclicWalk_getVert {m : ℕ} (P : LatticePolygon m) (j : ℕ)
    (hj : j ≤ m + 2) :
    (polygonCyclicWalk P).getVert j = P.vertex (j : ZMod (m + 3)) := by
  have hnonempty : polygonCyclicList P ≠ [] := by simp [polygonCyclicList]
  have hchain : (polygonCyclicList P).IsChain squareLattice.Adj := by
    change (List.ofFn (fun i : Fin (m + 3) => P.vertex (i.val : ZMod (m + 3)))).IsChain _
    rw [List.isChain_ofFn]
    intro i hi
    rw [Nat.cast_add]
    exact P.adjacent (i : ZMod (m + 3))
  change (Walk.ofSupport (polygonCyclicList P) hnonempty hchain).getVert j = _
  rw [Walk.getVert_eq_getD_support]
  rw [Walk.support_ofSupport hnonempty hchain]
  change (List.ofFn (fun k : Fin (m + 3) => P.vertex (k.val : ZMod (m + 3)))).getD j _ = _
  have hlen : (List.ofFn (fun k : Fin (m + 3) => P.vertex (k.val : ZMod (m + 3)))).length = m + 3 := by
    simp
  have hjlt : j < (List.ofFn (fun k : Fin (m + 3) => P.vertex (k.val : ZMod (m + 3)))).length := by
    rw [hlen]
    omega
  rw [List.getD_eq_getElem _ _ hjlt]
  rw [List.getElem_ofFn]

private theorem p5aCyclicWalk_length {m : ℕ} (P : LatticePolygon m) :
    (polygonCyclicWalk P).length = m + 2 := by
  have hnonempty : polygonCyclicList P ≠ [] := by simp [polygonCyclicList]
  have hchain : (polygonCyclicList P).IsChain squareLattice.Adj := by
    change (List.ofFn (fun i : Fin (m + 3) => P.vertex (i.val : ZMod (m + 3)))).IsChain _
    rw [List.isChain_ofFn]
    intro i hi
    rw [Nat.cast_add]
    exact P.adjacent (i : ZMod (m + 3))
  change (Walk.ofSupport (polygonCyclicList P) hnonempty hchain).length = _
  rw [Walk.length_ofSupport]
  simp [polygonCyclicList]

private theorem p5aForwardCycle_length {m : ℕ} (P : LatticePolygon m) :
    (p5aForwardCycle P).length = m + 3 := by
  simp [p5aForwardCycle, polygonCycle, p5aCyclicWalk_length]

private theorem p5aForwardCycle_getVert {m : ℕ} (P : LatticePolygon m) (j : ℕ)
    (hj : j ≤ m + 2) :
    (p5aForwardCycle P).getVert j = P.vertex (j : ZMod (m + 3)) := by
  have hlenC : (polygonCycle P).length = m + 3 := by
    simp [polygonCycle, p5aCyclicWalk_length]
  rw [p5aForwardCycle, Walk.getVert_reverse, hlenC]
  have hpos : m + 3 - j ≠ 0 := by omega
  unfold polygonCycle
  rw [Walk.getVert_cons _ _ hpos]
  rw [Walk.getVert_reverse]
  have hidx : (polygonCyclicWalk P).length - ((m + 3) - j - 1) = j := by
    rw [p5aCyclicWalk_length]
    omega
  rw [hidx]
  exact p5aCyclicWalk_getVert P j hj

private theorem p5aCastIndex_val {a b : ℕ} (h : a = b) (i : ZMod a) :
    (Equiv.cast (congrArg ZMod h) i).val = i.val := by
  cases h
  rfl

private theorem p5aCastIndex_one {a b : ℕ} (h : a = b) :
    Equiv.cast (congrArg ZMod h) (1 : ZMod a) = (1 : ZMod b) := by
  cases h
  rfl

private theorem p5aCastIndex_add {a b : ℕ} (h : a = b) (i j : ZMod a) :
    Equiv.cast (congrArg ZMod h) (i + j) =
      Equiv.cast (congrArg ZMod h) i + Equiv.cast (congrArg ZMod h) j := by
  cases h
  rfl

theorem positive_polygonCycle_domain_eq {m : ℕ} (P : LatticePolygon m) :
    (latticePolygonOfCycle (p5aForwardCycle_isCycle P)).domain ⟨1, by norm_num⟩ =
      P.domain ⟨1, by norm_num⟩ := by
  let n' := (p5aForwardCycle P).length - 3 + 3
  have hmod : n' = m + 3 := by
    dsimp [n']
    rw [p5aForwardCycle_length]
    omega
  let e : ZMod n' ≃ ZMod (m + 3) := Equiv.cast (congrArg ZMod hmod)
  let Q := latticePolygonOfCycle (p5aForwardCycle_isCycle P)
  have hQvertex (i : ZMod n') : Q.vertex i = P.vertex (e i) := by
    have hindex : i.val ≤ m + 2 := by
      have hi : i.val < m + 3 := Nat.lt_of_lt_of_le i.val_lt (Nat.le_of_eq hmod)
      omega
    change (p5aForwardCycle P).getVert i.val = P.vertex (e i)
    rw [p5aForwardCycle_getVert P i.val hindex]
    have hi : i.val < m + 3 := Nat.lt_of_lt_of_le i.val_lt (Nat.le_of_eq hmod)
    have hcast : e i = (i.val : ZMod (m + 3)) := by
      apply ZMod.val_injective
      have hv : (e i).val = i.val := by simpa [e] using p5aCastIndex_val hmod i
      rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    rw [hcast]
  have hsucc (i : ZMod n') : e (i + 1) = e i + 1 := by
    change Equiv.cast (congrArg ZMod hmod) (i + 1) =
      Equiv.cast (congrArg ZMod hmod) i + 1
    rw [p5aCastIndex_add hmod i (1 : ZMod n'), p5aCastIndex_one hmod]
  have hcarrier : Q.carrier ⟨1, by norm_num⟩ = P.carrier ⟨1, by norm_num⟩ := by
    change (⋃ i : ZMod n',
        segment ℝ (latticeEmbed ⟨1, by norm_num⟩ (Q.vertex i))
          (latticeEmbed ⟨1, by norm_num⟩ (Q.vertex (i + 1)))) =
      ⋃ i : ZMod (m + 3),
        segment ℝ (latticeEmbed ⟨1, by norm_num⟩ (P.vertex i))
          (latticeEmbed ⟨1, by norm_num⟩ (P.vertex (i + 1)))
    exact Set.iUnion_congr_of_surjective e e.surjective (by
      intro i
      rw [hQvertex, hQvertex, hsucc])
  change complexInside (Q.carrier ⟨1, by norm_num⟩) =
      complexInside (P.carrier ⟨1, by norm_num⟩)
  rw [hcarrier]

end
end PottsContinuity.DualityExt
