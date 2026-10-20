module

public import PottsContinuity.Thm4.FKCGraphBridge
public import PottsContinuity.Thm4.Exploration
public import PottsContinuity.FKC.Medial.ParafermionicCoverExploration

@[expose] public section

namespace PottsContinuity.Thm4.FKCBridge
open PottsContinuity.Thm4.Medial
noncomputable section

/-- Coordinate-preserving identification of the two axis types. -/
def axisEquiv : LatticeAxis ≃ PottsContinuity.FKC.Medial.LatticeAxis where
  toFun a := match a with | .horizontal => .horizontal | .vertical => .vertical
  invFun a := match a with | .horizontal => .horizontal | .vertical => .vertical
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

def bondEquiv : LatticeBond ≃ PottsContinuity.FKC.Medial.LatticeBond where
  toFun b := ⟨b.base, axisEquiv b.axis⟩
  invFun b := ⟨b.base, axisEquiv.symm b.axis⟩
  left_inv b := by cases b; simp
  right_inv b := by cases b; simp

def portEquiv : LatticePort ≃ PottsContinuity.FKC.Medial.LatticePort where
  toFun p := ⟨bondEquiv p.bond, p.tip, p.side⟩
  invFun p := ⟨bondEquiv.symm p.bond, p.tip, p.side⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

def coverPortEquiv : ParafermionicCoverPort ≃ PottsContinuity.FKC.Medial.ParafermionicCoverPort :=
  Equiv.prodCongr portEquiv (Equiv.refl ℤ)

@[simp] theorem vertex_eq (c : ParafermionicCoverPort) :
    PottsContinuity.FKC.Medial.parafermionicCoverPortVertex (coverPortEquiv c) = parafermionicCoverPortVertex c := by
  rcases c with ⟨⟨⟨b, a⟩, t, s⟩, k⟩
  cases a <;> cases t <;> rfl

@[simp] theorem edge_eq (c : ParafermionicCoverPort) :
    PottsContinuity.FKC.Medial.parafermionicCoverPortEdge (coverPortEquiv c) =
      fkcWholeEdgeEquiv (parafermionicCoverPortEdge c) := by
  apply Subtype.ext
  rcases c with ⟨⟨⟨b, a⟩, t, s⟩, k⟩
  cases a <;> cases t <;> rfl

@[simp] theorem openPair_eq (c : ParafermionicCoverPort) :
    coverPortEquiv (parafermionicCoverOpenPair c) = PottsContinuity.FKC.Medial.parafermionicCoverOpenPair (coverPortEquiv c) := by
  rcases c with ⟨⟨⟨b, a⟩, t, s⟩, k⟩
  cases a <;> cases t <;> rfl

@[simp] theorem closedPair_eq (c : ParafermionicCoverPort) :
    coverPortEquiv (parafermionicCoverClosedPair c) = PottsContinuity.FKC.Medial.parafermionicCoverClosedPair (coverPortEquiv c) := by
  rcases c with ⟨⟨⟨b, a⟩, t, s⟩, k⟩
  cases a <;> rfl

@[simp] theorem cornerPair_eq (c : ParafermionicCoverPort) :
    coverPortEquiv (parafermionicCoverCornerPair c) = PottsContinuity.FKC.Medial.parafermionicCoverCornerPair (coverPortEquiv c) := by
  rcases c with ⟨⟨⟨b, a⟩, t, s⟩, k⟩
  cases a <;> cases t <;> cases s <;> rfl

theorem bondState_eq (n : ℕ) (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverPort) :
    PottsContinuity.FKC.Medial.parafermionicCoverPortBondState
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtensionState n (fkcConfiguration n A))
      (coverPortEquiv c) =
    parafermionicCoverPortBondState (parafermionicCoverConfigurationExtensionState n A) c := by
  unfold PottsContinuity.FKC.Medial.parafermionicCoverPortBondState parafermionicCoverPortBondState
  rw [edge_eq, fkc_configurationExtensionState]

theorem localPair_eq (n : ℕ) (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverPort) :
    coverPortEquiv (parafermionicCoverLocalPair (parafermionicCoverConfigurationExtensionState n A) c) =
      PottsContinuity.FKC.Medial.parafermionicCoverLocalPair
        (PottsContinuity.FKC.FiniteFK.parafermionicCoverConfigurationExtensionState n (fkcConfiguration n A)) (coverPortEquiv c) := by
  unfold parafermionicCoverLocalPair PottsContinuity.FKC.Medial.parafermionicCoverLocalPair
  rw [bondState_eq]
  split <;> simp only [openPair_eq, closedPair_eq]

/-- All retained port occurrences are transported, including boundary half-ports. -/
def finitePortEquiv (n : ℕ) : ParafermionicCoverFinitePort n ≃ PottsContinuity.FKC.FiniteFK.ParafermionicCoverFinitePort n where
  toFun c := ⟨coverPortEquiv c.1, by
    rw [vertex_eq, PottsContinuity.FKC.parafermionicCoverBoxVertices_mem]
    exact (parafermionicCoverBoxVertices_mem n (parafermionicCoverPortVertex c.1)).mp c.2⟩
  invFun d := ⟨coverPortEquiv.symm d.1, by
    have h := vertex_eq (coverPortEquiv.symm d.1)
    rw [coverPortEquiv.apply_symm_apply] at h
    rw [← h]
    exact d.2⟩
  left_inv c := Subtype.ext (coverPortEquiv.symm_apply_apply c.1)
  right_inv d := Subtype.ext (coverPortEquiv.apply_symm_apply d.1)

@[simp] theorem finiteLocalPair_eq (n : ℕ) (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    finitePortEquiv n (parafermionicCoverFiniteLocalPairPerm n A c) =
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteLocalPairPerm n (fkcConfiguration n A) (finitePortEquiv n c) := by
  apply Subtype.ext
  exact localPair_eq n A c.1

@[simp] theorem finiteCornerPair_eq (n : ℕ) (c : ParafermionicCoverFinitePort n) :
    finitePortEquiv n (parafermionicCoverFiniteCornerPairPerm n c) =
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm n (finitePortEquiv n c) := by
  apply Subtype.ext
  exact cornerPair_eq c.1

@[simp] theorem finiteOrigin_eq (n : ℕ) (hn : 1 ≤ n) :
    finitePortEquiv n (parafermionicCoverFiniteOriginCornerPort n hn) =
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginCornerPort n hn := by
  apply Subtype.ext
  rfl

end
end PottsContinuity.Thm4.FKCBridge
