import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Ordered_Product
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Interlattice_Properties
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Bounded_Subtype
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Consistent_Approximating_Operator
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Reliable_Pair
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Stable_Revision_Operator
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Prudent_Pair
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Chain_Complete_Partial_Order

import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_10
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_12

variable
  {D : Type u}
  {D1 D2 : D → Prop}
  [O : PartialOrder D]
  [BoundedPartialOrder D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)]
  [L2 : CompleteLatticeFromOrder (Subtype D2)]
  (interlub : interlattice_lub D D1 D2)
  (interglb : interlattice_glb D D1 D2)
  (limitOrdinal : Ordinal)
  (isLimit : limitOrdinal.IsLimit)
  (chain : (@ChainCompletePartialOrder.Chain {x : Subtype D1 × Subtype D2 | ⊗x} (@InfoPoset _ _ _ O).toPreorder))
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
  (conA : consistent_approximating_operator A)
  (A_reliable : ∀ limitOrdinal, ∀ (i : {x | x < limitOrdinal}), (reliable A (chain i.val)))

def Proposition_13_A : reliable A ((Proposition_12_B interlub interglb limitOrdinal isLimit).cSup chain) := by

  let cCompletePoset := Proposition_12_B interlub interglb limitOrdinal isLimit
  let cₛᵤₚ := (cCompletePoset.cSup chain)

  -- chain i ≲ cₛᵤₚ
  have p1 : ∀ (i : {x | x < limitOrdinal}), (chain i).val ≲ cₛᵤₚ := by
    intro i
    exact cCompletePoset.le_cSup chain i

  -- A (chain i) ≲ A cₛᵤₚ
  have p2 : ∀ (i : {x | x < limitOrdinal}), A (chain i) ≤ (A cₛᵤₚ).val := by
    intro i
    exact conA (chain i) cₛᵤₚ (p1 i)

  -- chain i ≲ A cₛᵤₚ
  have p3 : ∀ (i : {x | x < limitOrdinal}), (chain i).val ≲ (A cₛᵤₚ).val := by
    intro i
    exact cCompletePoset.le_trans (chain i) (A (chain i)) (A cₛᵤₚ) (A_reliable limitOrdinal i) (p2 i)

  -- cₛᵤₚ ≲ A cₛᵤₚ, by virtue of A cₛᵤₚ being u.b. of chain and cₛᵤₚ being least upper bound
  have p5 : cₛᵤₚ ≲ (A cₛᵤₚ).val := by
    exact cCompletePoset.cSup_le chain (A cₛᵤₚ) p3

  exact p5


-- ((Proposition_12_B interlub interglb limitOrdinal isLimit).cSup chain).val.1, ((Proposition_12_B interlub interglb limitOrdinal isLimit).cSup chain).val.2
--

def Proposition_13_B
(prudent_chain : ∀ (i : {x | x < limitOrdinal}), prudent interlub A conA ⟨chain i, A_reliable limitOrdinal i⟩) :
prudent interlub A conA
⟨((Proposition_12_B interlub interglb limitOrdinal isLimit).cSup chain), (Proposition_13_A interlub interglb limitOrdinal isLimit chain A conA A_reliable)⟩
 := by

  let cCompletePoset := Proposition_12_B interlub interglb limitOrdinal isLimit
  let cₛᵤₚ := (cCompletePoset.cSup chain)
  let cₛᵤₚ_Aᵣₑ := Proposition_13_A interlub interglb limitOrdinal isLimit chain A conA A_reliable

  let aₗₛ := cₛᵤₚ.val.1
  let bₗₛ := cₛᵤₚ.val.2

  let CLbₗₛ := Proposition_8_A bₗₛ interlub

  let A₁ₛ := A₁OrderHom interlub A conA ⟨cₛᵤₚ, cₛᵤₚ_Aᵣₑ⟩

  let lfpbₗₛ := rOb interlub A conA ⟨cₛᵤₚ, cₛᵤₚ_Aᵣₑ⟩

  have P10 := Proposition_10 interlub interglb A conA ⟨cₛᵤₚ, cₛᵤₚ_Aᵣₑ⟩

  -- bᵢ↓ ∈ lowerBounds {x | A(x, bᵢ)₁ ≤ x}
  have p8 : ∀ (i : {x | x < limitOrdinal}), (rOb interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) ∈ {x | (A₁OrderHom interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) x ≤ x} ∧ (rOb interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) ∈ lowerBounds {x | (A₁OrderHom interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) x ≤ x}:= by
    intro i
    exact (@OrderHom.isLeast_lfp_le {x // (boundedSubtype _ _ _ D1 ⊥ (chain i).val.2) x} (Proposition_8_A (chain i).val.2 interlub) (A₁OrderHom interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩))

  -- bₗₛ↓ ∈ lowerBounds {x | A(x, bₗₛ)₁ ≤ x}
  have p10 : lfpbₗₛ ∈ {x | A₁ₛ x ≤ x} ∧ lfpbₗₛ ∈ lowerBounds {x | A₁ₛ x ≤ x} :=
    (@OrderHom.isLeast_lfp_le {x // (boundedSubtype _ _ _ D1 ⊥ bₗₛ) x} CLbₗₛ A₁ₛ)

  -- (x, bᵢ) ≲ (x, bₗₛ)
  have p11 : ∀ (i : {x | x < limitOrdinal}), ∀ a ∈ {x | boundedSubtype D D1 D2 D1 ⊥ bₗₛ x}, (a, (chain i).val.2) ≲ (a, bₗₛ) := by
    intro i a _
    apply And.intro
    .
      rfl
    .
      exact (cCompletePoset.le_cSup chain i).2

  -- A (x, bᵢ) ≲ A (x, bₗₛ)
  have p12 : ∀ (i : {x | x < limitOrdinal}), ∀ a : {x | boundedSubtype D D1 D2 D1 ⊥ bₗₛ x}, A ⟨(a, (chain i).val.2), O.le_trans a bₗₛ (chain i).val.2 a.prop.2 (cCompletePoset.le_cSup chain i).2⟩ ≲ (A ⟨(a, bₗₛ), a.prop.2⟩).val  := by
    intro i a
    exact conA ⟨(a, (chain i).val.2), O.le_trans a bₗₛ (chain i).val.2 a.prop.2 (cCompletePoset.le_cSup chain i).2⟩ ⟨(a, bₗₛ), a.prop.2⟩ (p11 i a a.prop)

  -- ∀ x ∈ [⊥, bₗₛ], x ≤ bᵢ
  have p13 : ∀ (i : {x | x < limitOrdinal}), ∀ x : {x | boundedSubtype D D1 D2 D1 ⊥ bₗₛ x}, x.val ≤ (chain i).val.2.val := by
    intro i x
    exact O.le_trans x bₗₛ (chain i).val.2 x.prop.2 (cCompletePoset.le_cSup chain i).2

  -- x ∈ {x | A(x, bₗₛ)₁ ≤ x}, A(x, bᵢ)₁ ≤ x
  have p14 : ∀ (i : {x | x < limitOrdinal}), ∀ x : {x | boundedSubtype D D1 D2 D1 ⊥ bₗₛ x}, A₁ₛ x ≤ x → (A₁OrderHom interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) ⟨x, ⟨L1.bot_le x, (p13 i) x⟩⟩ ≤ x.val := by
    intro i x h
    have A₁_le_A₁ₛ := ((p12 i) x).1
    exact O.le_trans (A ⟨(x, (chain i).val.2), O.le_trans x bₗₛ (chain i).val.2 x.prop.2 (cCompletePoset.le_cSup chain i).2⟩).val.1 (A ⟨(x, bₗₛ), x.prop.2⟩).val.1 x A₁_le_A₁ₛ h

  -- A (bₗₛ↓, bᵢ)₁ ≤ bₗₛ↓
  have p15 : ∀ (i : {x | x < limitOrdinal}), (A₁OrderHom interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) ⟨lfpbₗₛ, ⟨L1.bot_le lfpbₗₛ, O.le_trans lfpbₗₛ bₗₛ (chain i).val.2 P10.1 (cCompletePoset.le_cSup chain i).2⟩⟩ ≤ ⟨lfpbₗₛ, ⟨L1.bot_le lfpbₗₛ, O.le_trans lfpbₗₛ bₗₛ (chain i).val.2 P10.1 (cCompletePoset.le_cSup chain i).2⟩⟩ := by
    intro i
    exact p14 i lfpbₗₛ p10.1

  -- A (x, bᵢ)₁ ≤ x → bᵢ↓ ≤ x
  have p16 : ∀ (i : {x | x < limitOrdinal}), ∀ x, (A₁OrderHom interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) x ≤ x → (rOb interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) ≤ x.val := by
    intro i
    exact (p8 i).2

  -- bᵢ↓ ≤ bₗₛ↓
  have p17 : ∀ (i : {x | x < limitOrdinal}), (rOb interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) ≤ lfpbₗₛ.val := by
    intro i
    exact p16 i ⟨lfpbₗₛ, ⟨L1.bot_le lfpbₗₛ, O.le_trans lfpbₗₛ bₗₛ (chain i).val.2 P10.1 (cCompletePoset.le_cSup chain i).2⟩⟩ (p15 i)

  -- aᵢ ≤ bᵢ↓
  have p18 : ∀ (i : {x | x < limitOrdinal}), (chain i).val.1 ≤ (rOb interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩) :=
    λ i => prudent_chain i

  -- aᵢ ≤ bₗₛ↓
  have p19 : ∀ (i : {x | x < limitOrdinal}), (chain i).val.1 ≤ lfpbₗₛ.val := by
    intro i
    exact O.le_trans (chain i).val.1 (rOb interlub A conA ⟨chain i, (A_reliable limitOrdinal i)⟩).val lfpbₗₛ.val (p18 i) (p17 i)

  -- ∀ (x, y) upperBound of the chain → aₗₛ ≤ x
  have p20 : ∀ x, (∀ (i : {x | x < limitOrdinal}), (chain i) ≤ x) → aₗₛ ≤ x.val.1 := by
    intro x h
    exact (cCompletePoset.cSup_le chain x h).1

  -- (bₗₛ↓, bₗₛ) upperBound of the chain
  have p21 : ∀ (i : {x | x < limitOrdinal}), (chain i).val ≲ (lfpbₗₛ.val, bₗₛ) := by
    intro i
    exact ⟨p19 i, (cCompletePoset.le_cSup chain i).2⟩

  -- aₗₛ ≤ bₗₛ↓
  have p22 : aₗₛ ≤ lfpbₗₛ.val :=
    p20 ⟨(lfpbₗₛ.val, bₗₛ), lfpbₗₛ.prop.2⟩ p21

  exact p22
