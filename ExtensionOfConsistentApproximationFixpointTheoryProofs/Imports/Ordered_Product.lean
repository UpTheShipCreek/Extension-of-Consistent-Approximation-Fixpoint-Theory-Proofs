import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs

-- The set of pairs (d1, d2) ∈ (D1, D2) such that d1 ≤ d2
def ordered_product {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] : (Subtype D1 × Subtype D2) → Prop :=
  λ d => (d.1 : D) ≤ (d.2 : D)
prefix:50 "⊗" => ordered_product
