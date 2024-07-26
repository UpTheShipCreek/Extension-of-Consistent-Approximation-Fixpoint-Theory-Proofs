import ExtensionOfConsistentApproximationFixpointTheoryProofs.Imports.Defs

def subtypesCreateType (D : Type u) (D1 D2 : D → Prop) [Nonempty (Subtype D1)] [Nonempty (Subtype D2)] : Prop :=
  ∀ (d : D), D1 d ∨ D2 d

def subtypesContainTopBot (D : Type u) (D1 D2 : D → Prop) [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [L : BoundedPartialOrder D] : Prop :=
  D1 L.top ∧ D1 L.bot ∧ D2 L.top ∧ D2 L.bot

def interlattice_lub (D : Type u) (D1 D2 : D → Prop) [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [BoundedPartialOrder D]  [L1 :(CompleteLatticeFromOrder (Subtype D1))] : Prop :=
  -- D1 ∪ D2 = D
  (subtypesCreateType D D1 D2) ∧
  -- Both contain the elements ⊥ and ⊤
  (subtypesContainTopBot D D1 D2) ∧
  -- Interlattice lub
  -- b ∈ D2
  ∀ (b : D), D2 b →
    --  S ⊆ D1 such that for every x ∈ S, x ≤ b
    ∀ (S : Set (Subtype D1)), (∀ x, x ∈ S → ↑x ≤ b) →
      -- Then ∨L1 S ≤ b
      ↑(L1.sSup S) ≤ b

def interlattice_glb (D : Type u) (D1 D2 : D → Prop) [Nonempty {x // D1 x}] [Nonempty {x // D2 x}] [PartialOrder D] [BoundedPartialOrder D] [L2 : (CompleteLatticeFromOrder (Subtype D2))] : Prop :=
  -- D1 ∪ D2 = D
  (subtypesCreateType D D1 D2) ∧
  -- Both contain the elements ⊥ and ⊤
  (subtypesContainTopBot D D1 D2) ∧
  -- Interlattice glb
  -- a ∈ D1
  ∀ (a : D), D1 a →
    -- S ⊆ D2 such that for every x ∈ S x, ≥ a
    ∀ (S : Set (Subtype D2)), (∀ x, x ∈ S → ↑x ≥ a) →
      -- Then, ∧L2 S ≥ a
      ↑(L2.sInf S) ≥ a
