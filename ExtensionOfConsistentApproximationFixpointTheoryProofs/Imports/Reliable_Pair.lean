import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Ordered_Product
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Info_Ordering

def reliable
  {D : Type u} {D1 D2 : D → Prop} [PartialOrder D] [BoundedPartialOrder D]
  -- A : D1 ⊗ D2 → D1 ⊗ D2 and monotone
  (A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
  -- (a, b) ∈ D1 ⊗ D2
  (d : {x : Subtype D1 × Subtype D2 // ⊗x}) : Prop :=
  -- (a, b) ≲ A (a, b)
    d.val ≲ A d
