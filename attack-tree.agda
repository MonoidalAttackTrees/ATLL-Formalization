open import prelude

module attack-tree {𝔹 : Set} {pf : dec 𝔹} where

data ATree : Set where
  NODE : (b : 𝔹) → ATree
  AND  : ATree → ATree → ATree
  OR   : ATree → ATree → ATree
  SAND : ATree → ATree → ATree

data _⟿_ : ATree → ATree → Set where
  ⟿-OR-sym : ∀{A B} → OR A B ⟿ OR B A
  ⟿-AND-sym : ∀{A B} → AND A B ⟿ AND B A
  ⟿-contract : ∀{A} → OR A A ⟿ A
  ⟿-OR-assoc : ∀{A B C} → OR A (OR B C) ⟿ OR (OR A B) C
  ⟿-AND-assoc : ∀{A B C} → AND A (AND B C) ⟿ AND (AND A B) C
  ⟿-SAND-assoc : ∀{A B C} → SAND A (SAND B C) ⟿ SAND (SAND A B) C

  ⟿-AND-dist : ∀{A B C : ATree} → (AND A (OR B C)) ⟿ (OR (AND A B) (AND A C))
  ⟿-SAND-dist : ∀{A B C : ATree} → (SAND A (OR B C)) ⟿ (OR (SAND A B) (SAND A C))

  ⟿-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (AND A₁ B) ⟿ (AND A₂ B)
  ⟿-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (AND A B₁) ⟿ (AND A B₂)

  ⟿-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (OR A₁ B) ⟿ (OR A₂ B)
  ⟿-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (OR A B₁) ⟿ (OR A B₂)

  ⟿-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (SAND A₁ B) ⟿ (SAND A₂ B)
  ⟿-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (SAND A B₁) ⟿ (SAND A B₂)

