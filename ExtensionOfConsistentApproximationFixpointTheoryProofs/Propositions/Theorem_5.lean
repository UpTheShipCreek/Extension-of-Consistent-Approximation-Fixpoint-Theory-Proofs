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
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_11
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_12
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Propositions.Proposition_13

variable
  {D : Type u}
  {D1 D2 : D → Prop}
  [O : PartialOrder D]
  [L : BoundedPartialOrder D]
  [L1 : CompleteLatticeFromOrder (Subtype D1)]
  [L2 : CompleteLatticeFromOrder (Subtype D2)]
  (interlub : interlattice_lub D D1 D2)
  (interglb : interlattice_glb D D1 D2)
  (chain : @ChainCompletePartialOrder.Chain {x : Subtype D1 × Subtype D2 | ⊗x} (@InfoPoset _ _ _ O).toPreorder)
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
  (conA : consistent_approximating_operator A)
  (A_reliable : ∀ limitOrdinal : Ordinal, ∀ (i : {x | x < limitOrdinal}), (reliable A (chain i)))
  (prudent_chain : ∀ limitOrdinal, ∀ (i : {x | x < limitOrdinal}), prudent interlub A conA ⟨chain i, A_reliable limitOrdinal i⟩)

def C_A (ab : {x // prudent interlub A conA x}) : {x // prudent interlub A conA x} :=
  let bᵥ := rOb interlub A conA ab
  let aᵤ := rOa interglb A conA ab
  ⟨⟨⟨(bᵥ, aᵤ), (Proposition_10 interlub interglb A conA ab).2.2.2⟩, (Proposition_11_A interlub interglb A conA ab).2⟩, (Proposition_11_B interlub interglb A conA ab)⟩

def L1bot_le_L2top : L1.bot ≤ L2.top.val :=
  have L1bot_eq_Lbot : L1.bot = L.bot := by
    have t1 : D1 L.bot := interlub.2.1.2.1
    aesop
  have L2top_eq_Ltop : L2.top = L.top := by
    have t1 : D2 L.top := interlub.2.1.2.2.1
    aesop
  have Lbot_le_Ltop : L.bot ≤ L.top := L.bot_le L.top
  L1bot_eq_Lbot ▸ L2top_eq_Ltop▸ Lbot_le_Ltop

noncomputable section

def Theorem_5_sequence (o : Ordinal) : {x // prudent interlub A conA x} :=
  Ordinal.limitRecOn
    o
    ⟨⟨⟨(L1.bot, L2.top), L1bot_le_L2top interlub⟩, sorry⟩, sorry⟩
    (λ sucOrdinal s => C_A interlub interglb A conA s)
    (λ limitOrdinal isLimit _ => ⟨⟨(Proposition_12_B interlub interglb limitOrdinal isLimit).cSup chain, Proposition_13_A interlub interglb limitOrdinal isLimit chain A conA A_reliable⟩, Proposition_13_B interlub interglb limitOrdinal isLimit chain A conA A_reliable (prudent_chain limitOrdinal)⟩)
