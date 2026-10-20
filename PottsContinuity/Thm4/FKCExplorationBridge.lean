module

public import PottsContinuity.Thm4.FKCPortBridge
public import PottsContinuity.Thm4.ExplorationOrientation
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationOrientation
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport

@[expose] public section

namespace PottsContinuity.Thm4.FKCBridge
open PottsContinuity.Thm4.Medial SimpleGraph
noncomputable section

def explorationVertexEquiv (n : ℕ) : (ParafermionicCoverFinitePort n × Bool) ≃
    (PottsContinuity.FKC.FiniteFK.ParafermionicCoverFinitePort n × Bool) :=
  Equiv.prodCongr (finitePortEquiv n) (Equiv.refl Bool)

theorem cutCornerPair_eq (n : ℕ) (hn : 1 ≤ n) (c : ParafermionicCoverFinitePort n) :
    finitePortEquiv n (pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n) c) =
    PottsContinuity.FKC.Medial.pairingSingleCutPerm (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm n)
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginCornerPort n hn)
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm_involutive n) (finitePortEquiv n c) := by
  simp only [pairingSingleCutPerm_apply, PottsContinuity.FKC.Medial.pairingSingleCutPerm_apply,
    pairingSingleCut, PottsContinuity.FKC.Medial.pairingSingleCut,
    ← finiteOrigin_eq, ← finiteCornerPair_eq, (finitePortEquiv n).injective.eq_iff]
  split <;> simp_all only [finiteCornerPair_eq]

/-- Isomorphism of the actual two-layer corner-cut exploration graphs. -/
def explorationGraphIso (n : ℕ) (hn : 1 ≤ n)
    (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n)) :
    parafermionicCoverFiniteCornerCutPairingGraph n hn A ≃g
      PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerCutPairingGraph n hn (fkcConfiguration n A) where
  toEquiv := explorationVertexEquiv n
  map_rel_iff' := by
    intro u v
    rw [PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerCutPairingGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp only [explorationVertexEquiv, Equiv.prodCongr_apply, Equiv.refl_apply,
      Prod.map, ← finiteLocalPair_eq, ← cutCornerPair_eq,
      ne_eq, (finitePortEquiv n).injective.eq_iff]

/-- The unique actual exploration is carried to FKC's unique exploration;
there is no assumption about either library's edge-cut seed choice. -/
theorem exploration_support_eq (n : ℕ) (hn : 1 ≤ n)
    (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n)) :
    (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginExplorationPath n hn (fkcConfiguration n A)).support =
      (parafermionicCoverFiniteOriginExplorationPath n hn A).support.map (explorationVertexEquiv n) := by
  let E := explorationGraphIso n hn A
  let p := parafermionicCoverFiniteOriginExplorationPath n hn A
  have hs : E (parafermionicCoverFiniteOriginCornerPort n hn, true) =
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginCornerPort n hn, true) := by
    exact Prod.ext (finiteOrigin_eq n hn) rfl
  have ht : E (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn), true) =
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm n
        (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginCornerPort n hn), true) := by
    exact Prod.ext ((finiteCornerPair_eq n _).trans
      (congrArg (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerPairPerm n) (finiteOrigin_eq n hn))) rfl
  let q := (p.map E.toHom).copy hs ht
  have hq : q.IsPath := by
    simp only [q, Walk.isPath_def, Walk.support_copy, Walk.support_map]
    exact (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A).support_nodup.map E.injective
  have heq : q = PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginExplorationPath n hn (fkcConfiguration n A) := by
    obtain ⟨r, hr, huniq⟩ := PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteCornerCut_existsUnique_isPath
      n hn (fkcConfiguration n A)
    exact (huniq q hq).trans (huniq _
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginExplorationPath_isPath n hn (fkcConfiguration n A))).symm
  rw [← heq]
  simp only [q, Walk.support_copy, Walk.support_map]
  rfl

theorem exploration_visit_iff (n : ℕ) (hn : 1 ≤ n)
    (A : PottsContinuity.PD.FK.Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) (b : Bool) :
    (finitePortEquiv n c, b) ∈
      (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteOriginExplorationPath n hn (fkcConfiguration n A)).support ↔
    (c, b) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
  rw [exploration_support_eq]
  change explorationVertexEquiv n (c, b) ∈ _ ↔ _
  exact List.mem_map_of_injective (explorationVertexEquiv n).injective

end
end PottsContinuity.Thm4.FKCBridge
