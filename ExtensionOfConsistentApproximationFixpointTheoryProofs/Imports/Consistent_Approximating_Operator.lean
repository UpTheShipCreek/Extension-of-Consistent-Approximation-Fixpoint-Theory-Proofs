import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Ordered_Product
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Info_Ordering

def consistent_approximating_operator
  {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x}) : Prop :=
  -- ∀ d, d' ∈ D1 ⊗ D2
  ∀ (d d' : {x : Subtype D1 × Subtype D2 // ⊗x}),
    -- d ≲ d' →
    d.val ≲ d' →
      -- A d ≲ A d'
      (A d).val ≲ A d'
