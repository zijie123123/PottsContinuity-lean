-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/DomainBonds.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.LatticePorts
public import PottsContinuity.FKC.Domains.LatticeGraph
public import PottsContinuity.FKC.FiniteFK.Graph

/-!
# Actual domain bonds and their four medial ports

A domain bond is a normalized unit lattice segment wholly contained in the
closure of the domain. The equivalence below identifies these bonds with the
actual original edges of `domainLatticeGraph`, without discarding boundary
edges or isolated vertices. Boundedness proves finiteness.

Every such bond has four distinct ports. An actual finite FK configuration
induces the same local open/closed pairing as on the full grid. This module
does not construct the boundary pairing or assert a two-terminal condition.
-/

@[expose] public section

namespace PottsContinuity.FKC.Medial

noncomputable section

/-- A genuine unit bond whose full closed segment lies in the domain closure. -/
abbrev DomainBond (δ : PositiveMesh) (D : Set ℂ) :=
  {e : LatticeBond //
    segment ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) ⊆ closure D}

namespace DomainBond

variable {δ : PositiveMesh} {D : Set ℂ}

def source (e : DomainBond δ D) : DomainVertex δ D :=
  ⟨e.val.source, e.property (left_mem_segment ℝ _ _)⟩

def target (e : DomainBond δ D) : DomainVertex δ D :=
  ⟨e.val.target, e.property (right_mem_segment ℝ _ _)⟩

/-- The original unoriented graph edge, with its actual domain endpoints. -/
def toGraphEdge (e : DomainBond δ D) : (domainLatticeGraph δ D).edgeSet :=
  ⟨s(e.source, e.target), (domainLatticeGraph δ D).mem_edgeSet.mpr
    ⟨e.val.adjacent, e.property⟩⟩

theorem toGraphEdge_injective : Function.Injective (@toGraphEdge δ D) := by
  intro e f h
  apply Subtype.ext
  apply LatticeBond.toSym2_injective
  exact congrArg (Sym2.map Subtype.val) (congrArg Subtype.val h)

theorem toGraphEdge_surjective : Function.Surjective (@toGraphEdge δ D) := by
  rintro ⟨uv, huv⟩
  induction uv using Sym2.inductionOn with
  | hf u v =>
    have h := (domainLatticeGraph δ D).mem_edgeSet.mp huv
    obtain ⟨e, he⟩ := LatticeBond.exists_of_adj h.1
    rcases (Sym2.eq_iff.mp he) with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have heD : segment ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) ⊆
          closure D := by
        rw [hs, ht]
        exact h.2
      refine ⟨⟨e, heD⟩, ?_⟩
      apply Subtype.ext
      change s(source ⟨e, heD⟩, target ⟨e, heD⟩) = s(u, v)
      exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hs, Subtype.ext ht⟩)
    · have heD : segment ℝ (latticeEmbed δ e.source) (latticeEmbed δ e.target) ⊆
          closure D := by
        rw [hs, ht, segment_symm]
        exact h.2
      refine ⟨⟨e, heD⟩, ?_⟩
      apply Subtype.ext
      change s(source ⟨e, heD⟩, target ⟨e, heD⟩) = s(u, v)
      exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hs, Subtype.ext ht⟩)

/-- Canonical bonds represent exactly all actual unoriented domain graph edges. -/
def edgeEquiv (δ : PositiveMesh) (D : Set ℂ) :
    DomainBond δ D ≃ (domainLatticeGraph δ D).edgeSet :=
  Equiv.ofBijective toGraphEdge ⟨toGraphEdge_injective, toGraphEdge_surjective⟩

@[simp] theorem edgeEquiv_apply (e : DomainBond δ D) :
    edgeEquiv δ D e = e.toGraphEdge := rfl

/-- No finiteness premise is added to the carrier: boundedness of the domain suffices. -/
theorem finite (δ : PositiveMesh) {D : Set ℂ} (hD : Bornology.IsBounded D) :
    Finite (DomainBond δ D) := by
  let := domainVertex_finite δ hD
  exact Finite.of_injective toGraphEdge toGraphEdge_injective

end DomainBond

/-- Four distinct flags over each actual domain bond; no ports are geometrically identified. -/
structure DomainPort (δ : PositiveMesh) (D : Set ℂ) where
  bond : DomainBond δ D
  tip : Bool
  side : Bool
  deriving DecidableEq

namespace DomainPort

variable {δ : PositiveMesh} {D : Set ℂ}

/-- Forget only the domain membership proof, retaining both independent port flags. -/
def toLatticePort (p : DomainPort δ D) : LatticePort :=
  ⟨p.bond.val, p.tip, p.side⟩

theorem toLatticePort_injective : Function.Injective (@toLatticePort δ D) := by
  rintro ⟨e, t, s⟩ ⟨f, u, v⟩ h
  have he : e = f := Subtype.ext (congrArg LatticePort.bond h)
  have ht : t = u := congrArg LatticePort.tip h
  have hs : s = v := congrArg LatticePort.side h
  cases he
  cases ht
  cases hs
  rfl

/-- The finite port carrier is precisely original edge × endpoint flag × cell-side flag. -/
def edgeFlagsEquiv (δ : PositiveMesh) (D : Set ℂ) :
    DomainPort δ D ≃ (domainLatticeGraph δ D).edgeSet × Bool × Bool where
  toFun p := (DomainBond.edgeEquiv δ D p.bond, p.tip, p.side)
  invFun p := ⟨(DomainBond.edgeEquiv δ D).symm p.1, p.2.1, p.2.2⟩
  left_inv := by rintro ⟨e, t, s⟩; simp only [Equiv.symm_apply_apply]
  right_inv := by rintro ⟨e, t, s⟩; simp only [Equiv.apply_symm_apply]

theorem finite (δ : PositiveMesh) {D : Set ℂ} (hD : Bornology.IsBounded D) :
    Finite (DomainPort δ D) := by
  let := domainVertex_finite δ hD
  exact Finite.of_equiv _ (edgeFlagsEquiv δ D).symm

end DomainPort

namespace DomainBond

variable {δ : PositiveMesh} {D : Set ℂ}

/-- Membership in the actual FK configuration of original graph edges. -/
def isOpen (C : FiniteFK.Configuration (domainLatticeGraph δ D)) (e : DomainBond δ D) :
    Bool := by
  classical
  exact decide (e.toGraphEdge ∈ C)

@[simp] theorem isOpen_eq_true (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (e : DomainBond δ D) : isOpen C e = true ↔ e.toGraphEdge ∈ C := by
  classical
  simp [isOpen]

/-- The full-grid indicator of exactly the original bonds selected by the configuration. -/
def gridState (C : FiniteFK.Configuration (domainLatticeGraph δ D)) (e : LatticeBond) :
    Bool := by
  classical
  exact decide (∃ b : DomainBond δ D, b.val = e ∧ b.toGraphEdge ∈ C)

@[simp] theorem gridState_val (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (e : DomainBond δ D) : gridState C e.val = isOpen C e := by
  classical
  unfold gridState isOpen
  congr 1
  apply propext
  constructor
  · rintro ⟨b, hb, hC⟩
    have hbe : b = e := Subtype.ext hb
    simpa only [hbe] using hC
  · intro hC
    exact ⟨e, rfl, hC⟩

end DomainBond

namespace DomainPort

variable {δ : PositiveMesh} {D : Set ℂ}

/-- The actual configuration chooses an open cell-side turn or a closed endpoint turn. -/
def localPair (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) : DomainPort δ D :=
  if DomainBond.isOpen C p.bond then ⟨p.bond, !p.tip, p.side⟩
  else ⟨p.bond, p.tip, !p.side⟩

@[simp] theorem localPair_bond (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) : (localPair C p).bond = p.bond := by
  cases h : DomainBond.isOpen C p.bond <;> simp [localPair, h]

/-- Restriction to the domain gives exactly the full-grid local pairing, port by port. -/
theorem toLatticePort_localPair (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) :
    (localPair C p).toLatticePort = LatticePort.localPair (DomainBond.gridState C)
      p.toLatticePort := by
  cases h : DomainBond.isOpen C p.bond <;>
    simp [localPair, toLatticePort, LatticePort.localPair, LatticePort.openPair,
      LatticePort.closedPair, h]

theorem localPair_involutive (C : FiniteFK.Configuration (domainLatticeGraph δ D)) :
    Function.Involutive (localPair C) := by
  intro p
  apply toLatticePort_injective
  rw [toLatticePort_localPair, toLatticePort_localPair]
  exact LatticePort.localPair_involutive _ _

theorem localPair_ne (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) : localPair C p ≠ p := by
  intro h
  apply LatticePort.localPair_ne (DomainBond.gridState C) p.toLatticePort
  rw [← toLatticePort_localPair, h]

theorem localPair_faceBase_of_open (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) (hp : p.bond.toGraphEdge ∈ C) :
    (localPair C p).toLatticePort.faceBase = p.toLatticePort.faceBase := by
  have h := (DomainBond.isOpen_eq_true C p.bond).mpr hp
  simp [localPair, h, toLatticePort, LatticePort.faceBase]

@[simp] theorem localPair_position (C : FiniteFK.Configuration (domainLatticeGraph δ D))
    (p : DomainPort δ D) :
    (localPair C p).toLatticePort.position δ = p.toLatticePort.position δ := by
  rw [toLatticePort_localPair, LatticePort.localPair_position]

end DomainPort

end

end PottsContinuity.FKC.Medial
