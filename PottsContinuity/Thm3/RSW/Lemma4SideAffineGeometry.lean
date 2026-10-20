module

public import PottsContinuity.Thm3.RSW.Lemma4SideRectangleIso
public import PottsContinuity.Thm3.RSW.Lemma4SideBandProduct
public import PottsContinuity.PD.Duality.LatticePorts

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial
noncomputable section

/-- Inverse side coordinates on original primal vertices. -/
def lemma4SideInversePrimal (n : ℕ) (i : Fin 2) (v : LatticeVertex) : LatticeVertex :=
  (v.1, lemma4SideSign i * (v.2 + 2*(n:ℤ)))

/-- Inverse side coordinates on lower-left dual face bases. -/
def lemma4SideInverseFace (n : ℕ) (i : Fin 2) (v : LatticeVertex) : LatticeVertex :=
  (v.1, lemma4SideSign i * (v.2 + 2*(n:ℤ)) + (lemma4SideSign i - 1)/2)

/-- The normalized original bond after undoing the side coordinates. -/
def lemma4SideInverseBond (n : ℕ) (i : Fin 2) (b : LatticeBond) : LatticeBond :=
  ⟨(b.base.1, lemma4SideSign i * (b.base.2 + 2*(n:ℤ)) +
      match b.axis with
      | .horizontal => 0
      | .vertical => (lemma4SideSign i - 1)/2), b.axis⟩

theorem lemma4SideInversePrimal_injective (n : ℕ) (i : Fin 2) :
    Function.Injective (lemma4SideInversePrimal n i) := by
  intro u v h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  rcases lemma4SideSign_eq_one_or_neg_one i with hi | hi <;> simp [lemma4SideInversePrimal, hi] at hx hy <;>
    exact Prod.ext hx (by omega)

theorem lemma4SideInverseBond_edge (n : ℕ) (i : Fin 2) (b : LatticeBond) :
    (lemma4SideInverseBond n i b).toSym2 =
      Sym2.map (lemma4SideInversePrimal n i) b.toSym2 := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  rcases lemma4SideSign_eq_one_or_neg_one i with hi | hi <;> cases ax <;>
    simp [lemma4SideInverseBond, lemma4SideInversePrimal, hi,
      LatticeBond.toSym2, LatticeBond.source, LatticeBond.target, Sym2.map_mk,
      Prod.mk.injEq] <;> omega

theorem lemma4SideInverseBond_faces (n : ℕ) (i : Fin 2) (b : LatticeBond) :
    s((lemma4SideInverseBond n i b).faceBase false,
      (lemma4SideInverseBond n i b).faceBase true) =
      Sym2.map (lemma4SideInverseFace n i) s(b.faceBase false,b.faceBase true) := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  rcases lemma4SideSign_eq_one_or_neg_one i with hi | hi <;> cases ax <;>
    simp [lemma4SideInverseBond, lemma4SideInverseFace, hi,
      LatticeBond.faceBase, Sym2.map_mk, Prod.mk.injEq] <;> omega

/-- The inverse primal coordinates preserve actual lattice adjacency. -/
def lemma4SideInversePrimalEmbedding (n : ℕ) (i : Fin 2) :
    PD.FK.squareLattice ↪g PD.FK.squareLattice where
  toFun := lemma4SideInversePrimal n i
  inj' := lemma4SideInversePrimal_injective n i
  map_rel_iff' := by
    intro u v
    rw [squareLattice_adj_iff, squareLattice_adj_iff]
    rcases lemma4SideSign_eq_one_or_neg_one i with hi | hi <;>
      simp [lemma4SideInversePrimal, hi] <;> omega

end
end PottsContinuity.RSW
