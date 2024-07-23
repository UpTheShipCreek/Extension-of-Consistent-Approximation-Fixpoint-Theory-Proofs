import ThesisProofs.Imports.Defs

def boundedSubtype (D : Type u) (D1 D2 D' : D → Prop) [PartialOrder D] [BoundedPartialOrder D] (a : (Subtype D1)) (b : (Subtype D2)) : (Subtype D') → Prop :=
  (λ x => (a : D) ≤ (x : D) ∧ (x : D) ≤ (b : D))
