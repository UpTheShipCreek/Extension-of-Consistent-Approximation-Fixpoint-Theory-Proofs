import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Ordered_Product
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Interlattice_Properties
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Bounded_Subtype
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Consistent_Approximating_Operator
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Reliable_Pair
import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Stable_Revision_Operator

variable
{D : Type u}
{D1 D2 : D → Prop}
[PartialOrder D]
[BoundedPartialOrder D]
[CompleteLatticeFromOrder (Subtype D1)]
[CompleteLatticeFromOrder (Subtype D2)]
(interlub : interlattice_lub D D1 D2)
(A : {x : Subtype D1 × Subtype D2 // ⊗x} → {x : Subtype D1 × Subtype D2 // ⊗x})
(conA : consistent_approximating_operator A)
(ab : {x // reliable A x})

-- An A-reliable approximation (a, b) is A-prudent if a ≤ b↓.
def prudent : Prop :=
  let a := ab.1.1.1
  a.val ≤ rOb interlub A conA ab
