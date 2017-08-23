open import prelude
open import lineale
open import lineale-thms
open import dialectica-cat
open import dialectica-smcc
open import dialectica-at-ops

module attack-tree (𝔹 : Set) (pf : dec 𝔹) where

data ATree : Set where
  NODE : (b : 𝔹) → ATree
  AND  : ATree → ATree → ATree
  OR   : ATree → ATree → ATree
  SAND : ATree → ATree → ATree
  
data _⟿©_ : ATree → ATree → Set where
  ⟿©-contract : ∀{A : ATree} → (OR A A) ⟿© A
  ⟿©-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿© A₂ → (AND A₁ B) ⟿© (AND A₂ B)
  ⟿©-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿© B₂ → (AND A B₁) ⟿© (AND A B₂)
  ⟿©-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿© A₂ → (OR A₁ B) ⟿© (OR A₂ B)
  ⟿©-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿© B₂ → (OR A B₁) ⟿© (OR A B₂)
  ⟿©-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿© A₂ → (SAND A₁ B) ⟿© (SAND A₂ B)
  ⟿©-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿© B₂ → (SAND A B₁) ⟿© (SAND A B₂)

data _⟿*©_ : ATree → ATree → Set where
  ⟿©-step : ∀{A B : ATree} → A ⟿© B → A ⟿*© B
  ⟿©-refl : ∀{A : ATree} → A ⟿*© A
  ⟿©-trans : ∀{A B C : ATree} → A ⟿*© B → B ⟿*© C → A ⟿*© C

data _↪_ : ATree → ATree → Set where
  ↪-OR-sym : ∀{A B : ATree} → (OR A B) ↪ (OR B A)
  ↪-AND-sym : ∀{A B : ATree} → (AND A B) ↪ (AND B A)
  ↪-OR-assoc : ∀{A B C : ATree} → (OR A (OR B C)) ↪ (OR (OR A B) C)
  ↪-AND-assoc : ∀{A B C : ATree} → (AND A (AND B C)) ↪ (AND (AND A B) C)
  ↪-SAND-assoc : ∀{A B C : ATree} → (SAND A (SAND B C)) ↪ (SAND (SAND A B) C)
  ↪-AND-distl : ∀{A B C : ATree} → (AND A (OR B C)) ↪ (OR (AND A B) (AND A C))
  ↪-SAND-distl : ∀{A B C : ATree} → (SAND A (OR B C)) ↪ (OR (SAND A B) (SAND A C))
  ↪-AND-distr : ∀{A B C : ATree} → (AND (OR A B) C) ↪ (OR (AND A C) (AND B C))
  ↪-SAND-distr : ∀{A B C : ATree} → (SAND (OR A B) C) ↪ (OR (SAND A C) (SAND B C))    
  ↪-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ↪ A₂ → (AND A₁ B) ↪ (AND A₂ B)
  ↪-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ↪ B₂ → (AND A B₁) ↪ (AND A B₂)
  ↪-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ↪ A₂ → (OR A₁ B) ↪ (OR A₂ B)
  ↪-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ↪ B₂ → (OR A B₁) ↪ (OR A B₂)
  ↪-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ↪ A₂ → (SAND A₁ B) ↪ (SAND A₂ B)
  ↪-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ↪ B₂ → (SAND A B₁) ↪ (SAND A B₂)

data _↪*_ : ATree → ATree → Set where
  ↪-step : ∀{A B : ATree} → A ↪ B → A ↪* B
  ↪-refl : ∀{A : ATree} → A ↪* A
  ↪-trans : ∀{A B C : ATree} → A ↪* B → B ↪* C → A ↪* C

data _⟿_ : ATree → ATree → Set where
  ↪-reduce : ∀{A B : ATree} → A ↪ B → A ⟿ B
  ⟿-contract : ∀{A : ATree} → (OR A A) ⟿ A

data _⟿*_ : ATree → ATree → Set where
  ⟿-step : ∀{A B : ATree} → A ⟿ B → A ⟿* B
  ⟿-refl : ∀{A : ATree} → A ⟿* A
  ⟿-trans : ∀{A B C : ATree} → A ⟿* B → B ⟿* C → A ⟿* C

data _≃_ : ATree → ATree → Set where
  ↪-reduce : ∀{A B : ATree} → A ↪* B → A ≃ B
  ≃-sym : ∀{A B : ATree} → A ≃ B → B ≃ A

data _≈_ : ATree → ATree → Set where
  ≈-reduce : ∀{A B : ATree} → A ⟿ B → A ≈ B
  ≈-refl : ∀{A : ATree} → A ≈ A
  ≈-sym : ∀{A B : ATree} → A ≈ B → B ≈ A
  ≈-trans : ∀{A B C : ATree} → A ≈ B → B ≈ C → A ≈ C

_≅_ : (t₁ : ATree) → (t₂ : ATree) → ((t₁ ≡ t₂) ⊎ (t₁ ≡ t₂ → ⊥ {lzero}))
NODE b₁ ≅ NODE b₂ with dec-pf pf {b₁}{b₂}
NODE b₁ ≅ NODE b₂ | inj₁ x = inj₁ (cong {A = 𝔹}{ATree} NODE {b₁}{b₂} x)
NODE b₁ ≅ NODE b₂ | inj₂ y = inj₂ aux
 where
  aux : NODE b₁ ≡ NODE b₂ → ⊥ {lzero}
  aux refl = y refl
NODE b ≅ AND t₂ t₃ = inj₂ aux
 where
  aux : NODE b ≡ AND t₂ t₃ → ⊥ {lzero}
  aux ()
NODE b ≅ OR t₂ t₃ = inj₂ aux
 where
  aux : NODE b ≡ OR t₂ t₃ → ⊥ {lzero}
  aux ()
NODE b ≅ SAND t₂ t₃ = inj₂ aux
 where
  aux : NODE b ≡ SAND t₂ t₃ → ⊥ {lzero}
  aux ()
AND t₁ t₂ ≅ NODE b = inj₂ aux
 where
  aux : AND t₁ t₂ ≡ NODE b  → ⊥ {lzero}
  aux ()
AND t₁ t₂ ≅ AND t₃ t₄ with t₁ ≅ t₃ | t₂ ≅ t₄
AND t₁ t₂ ≅ AND t₃ t₄ | inj₁ refl | (inj₁ refl) = inj₁ refl
AND t₁ t₂ ≅ AND t₃ t₄ | inj₁ refl | (inj₂ y) = inj₂ aux
 where
  aux : AND t₁ t₂ ≡ AND t₁ t₄ → ⊥ {lzero}
  aux refl = y refl
AND t₁ t₂ ≅ AND t₃ t₄ | inj₂ y | (inj₁ refl) = inj₂ aux
 where
  aux : AND t₁ t₂ ≡ AND t₃ t₂ → ⊥
  aux refl = y refl
AND t₁ t₂ ≅ AND t₃ t₄ | inj₂ y₁ | (inj₂ y₂) = inj₂ aux
 where
  aux : AND t₁ t₂ ≡ AND t₃ t₄ → ⊥ {lzero}
  aux refl = y₁ refl
AND t₁ t₂ ≅ OR t₃ t₄ = inj₂ aux
 where
  aux : AND t₁ t₂ ≡ OR t₃ t₄ → ⊥ {lzero}
  aux ()
AND t₁ t₂ ≅ SAND t₃ t₄ = inj₂ aux
 where
  aux : AND t₁ t₂ ≡ SAND t₃ t₄ → ⊥ {lzero}
  aux ()
OR t₁ t₂ ≅ NODE b = inj₂ aux
 where
   aux : OR t₁ t₂ ≡ NODE b → ⊥ {lzero}
   aux ()
OR t₁ t₂ ≅ AND t₃ t₄ = inj₂ aux
 where
   aux : OR t₁ t₂ ≡ AND t₃ t₄ → ⊥ {lzero}
   aux ()
OR t₁ t₂ ≅ OR t₃ t₄ with t₁ ≅ t₃ | t₂ ≅ t₄
OR t₁ t₂ ≅ OR t₃ t₄ | inj₁ refl | (inj₁ refl) = inj₁ refl
OR t₁ t₂ ≅ OR t₃ t₄ | inj₁ refl | (inj₂ y) = inj₂ aux
 where
   aux : OR t₁ t₂ ≡ OR t₁ t₄ → ⊥ {lzero}
   aux refl = y refl
OR t₁ t₂ ≅ OR t₃ t₄ | inj₂ y | (inj₁ refl) = inj₂ aux
 where
  aux : OR t₁ t₂ ≡ OR t₃ t₂ → ⊥
  aux refl = y refl
OR t₁ t₂ ≅ OR t₃ t₄ | inj₂ y₁ | (inj₂ y₂) = inj₂ aux
 where
  aux : OR t₁ t₂ ≡ OR t₃ t₄ → ⊥
  aux refl = y₁ refl
OR t₁ t₂ ≅ SAND t₃ t₄ = inj₂ aux
 where
   aux : OR t₁ t₂ ≡ SAND t₃ t₄ → ⊥ {lzero}
   aux ()
SAND t₁ t₂ ≅ NODE b = inj₂ aux
 where
   aux : SAND t₁ t₂ ≡ NODE b → ⊥ {lzero}
   aux ()
SAND t₁ t₂ ≅ AND t₃ t₄ = inj₂ aux
 where
  aux : SAND t₁ t₂ ≡ AND t₃ t₄ → ⊥ {lzero}
  aux ()
SAND t₁ t₂ ≅ OR t₃ t₄ = inj₂ aux
 where
   aux : SAND t₁ t₂ ≡ OR t₃ t₄ → ⊥ {lzero}
   aux ()
SAND t₁ t₂ ≅ SAND t₃ t₄ with t₁ ≅ t₃ | t₂ ≅ t₄
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₁ refl | (inj₁ refl) = inj₁ refl
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₁ refl | (inj₂ y) = inj₂ aux
 where
  aux : SAND t₁ t₂ ≡ SAND t₁ t₄ → ⊥
  aux refl = y refl
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₂ y | (inj₁ refl) = inj₂ aux
 where
  aux : SAND t₁ t₂ ≡ SAND t₃ t₂ → ⊥
  aux refl = y refl
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₂ y₁ | (inj₂ y₂) = inj₂ aux
 where
  aux : SAND t₁ t₂ ≡ SAND t₃ t₄ → ⊥
  aux refl = y₁ refl

contract : ATree → ATree
contract (OR t₁ t₂) with t₁ ≅ t₂
contract (OR t₁ t₂) | inj₁ eq = contract t₁
contract (OR t₁ t₂) | inj₂ neq = OR (contract t₁) (contract t₂)
contract (AND t₁ t₂) = AND (contract t₁) (contract t₂)
contract (SAND t₁ t₂) = SAND (contract t₁) (contract t₂)
contract t = t

_≈'_ : (t₁ t₂ : ATree) → Set
t₁ ≈' t₂ = Σ[ s ∈ ATree ]( t₁ ⟿* s × t₂ ⟿* s )

⟿©-AND : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿© s₁ → t₂ ⟿© s₂ → (AND t₁ t₂) ⟿*© (AND s₁ s₂)
⟿©-AND {t₁}{s₁}{t₂}{s₂} p₁ p₂ with ⟿©-AND₁ {t₁}{s₁}{t₂} p₁ | ⟿©-AND₂ {s₁}{t₂}{s₂} p₂
... | r₁ | r₂ = ⟿©-trans (⟿©-step r₁) (⟿©-step r₂)

⟿©-SAND : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿© s₁ → t₂ ⟿© s₂ → (SAND t₁ t₂) ⟿*© (SAND s₁ s₂)
⟿©-SAND {t₁}{s₁}{t₂}{s₂} p₁ p₂ with ⟿©-SAND₁ {t₁}{s₁}{t₂} p₁ | ⟿©-SAND₂ {s₁}{t₂}{s₂} p₂
... | r₁ | r₂ = ⟿©-trans (⟿©-step r₁) (⟿©-step r₂)

⟿©-OR : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿© s₁ → t₂ ⟿© s₂ → (OR t₁ t₂) ⟿*© (OR s₁ s₂)
⟿©-OR {t₁}{s₁}{t₂}{s₂} p₁ p₂ with ⟿©-OR₁ {t₁}{s₁}{t₂} p₁ | ⟿©-OR₂ {s₁}{t₂}{s₂} p₂
... | r₁ | r₂ = ⟿©-trans (⟿©-step r₁) (⟿©-step r₂)

⟿*©-AND : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿*© s₁ → t₂ ⟿*© s₂ → (AND t₁ t₂) ⟿*© (AND s₁ s₂)
⟿*©-AND {t₁} {s₁} {t₂} {s₂} (⟿©-step p₁) (⟿©-step p₂) = ⟿©-AND p₁ p₂
⟿*©-AND {t₁} {s₁} {t₂} {.t₂} (⟿©-step p) ⟿©-refl = ⟿©-step (⟿©-AND₁ p)
⟿*©-AND {t₁} {s₁} {t₂} {s₂} p₁ (⟿©-trans {_}{t₃}{_} p₂ p₃) with ⟿*©-AND p₁ p₂ | ⟿*©-AND (⟿©-refl {s₁}) p₃
... | r₁ | r₂ = ⟿©-trans r₁ r₂
⟿*©-AND {t₁} {.t₁} {t₂} {s₂} ⟿©-refl (⟿©-step p) = ⟿©-step (⟿©-AND₂ p)
⟿*©-AND {t₁} {.t₁} {t₂} {.t₂} ⟿©-refl ⟿©-refl = ⟿©-refl
⟿*©-AND {t₁} {s₁} {t₂} {s₂} (⟿©-trans {_}{t₃}{_} p₁ p₂) p₃ with ⟿*©-AND p₁ p₃ | ⟿*©-AND {t₃}{s₁}{s₂}{s₂} p₂ ⟿©-refl
... | r₁ | r₂ = ⟿©-trans  r₁ r₂

⟿*©-OR : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿*© s₁ → t₂ ⟿*© s₂ → (OR t₁ t₂) ⟿*© (OR s₁ s₂)
⟿*©-OR {t₁} {s₁} {t₂} {s₂} (⟿©-step p₁) (⟿©-step p₂) = ⟿©-OR p₁ p₂
⟿*©-OR {t₁} {s₁} {t₂} {.t₂} (⟿©-step p) ⟿©-refl = ⟿©-step (⟿©-OR₁ p)
⟿*©-OR {t₁} {s₁} {t₂} {s₂} p₁ (⟿©-trans {_}{t₃}{_} p₂ p₃) with ⟿*©-OR p₁ p₂ | ⟿*©-OR (⟿©-refl {s₁}) p₃
... | r₁ | r₂ = ⟿©-trans r₁ r₂
⟿*©-OR {t₁} {.t₁} {t₂} {s₂} ⟿©-refl (⟿©-step p) = ⟿©-step (⟿©-OR₂ p)
⟿*©-OR {t₁} {.t₁} {t₂} {.t₂} ⟿©-refl ⟿©-refl = ⟿©-refl
⟿*©-OR {t₁} {s₁} {t₂} {s₂} (⟿©-trans {_}{t₃}{_} p₁ p₂) p₃ with ⟿*©-OR p₁ p₃ | ⟿*©-OR {t₃}{s₁}{s₂}{s₂} p₂ ⟿©-refl
... | r₁ | r₂ = ⟿©-trans  r₁ r₂

⟿*©-SAND : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿*© s₁ → t₂ ⟿*© s₂ → (SAND t₁ t₂) ⟿*© (SAND s₁ s₂)
⟿*©-SAND {t₁} {s₁} {t₂} {s₂} (⟿©-step p₁) (⟿©-step p₂) = ⟿©-SAND p₁ p₂
⟿*©-SAND {t₁} {s₁} {t₂} {.t₂} (⟿©-step p) ⟿©-refl = ⟿©-step (⟿©-SAND₁ p)
⟿*©-SAND {t₁} {s₁} {t₂} {s₂} p₁ (⟿©-trans {_}{t₃}{_} p₂ p₃) with ⟿*©-SAND p₁ p₂ | ⟿*©-SAND (⟿©-refl {s₁}) p₃
... | r₁ | r₂ = ⟿©-trans r₁ r₂
⟿*©-SAND {t₁} {.t₁} {t₂} {s₂} ⟿©-refl (⟿©-step p) = ⟿©-step (⟿©-SAND₂ p)
⟿*©-SAND {t₁} {.t₁} {t₂} {.t₂} ⟿©-refl ⟿©-refl = ⟿©-refl
⟿*©-SAND {t₁} {s₁} {t₂} {s₂} (⟿©-trans {_}{t₃}{_} p₁ p₂) p₃ with ⟿*©-SAND p₁ p₃ | ⟿*©-SAND {t₃}{s₁}{s₂}{s₂} p₂ ⟿©-refl
... | r₁ | r₂ = ⟿©-trans  r₁ r₂

⟿©-contracts : ∀{t} → t ⟿*© contract t
⟿*©-contract-same : ∀{t} → OR t t ⟿*© contract t

⟿©-contracts {NODE b} = ⟿©-refl
⟿©-contracts {AND t₁ t₂} with ⟿©-contracts {t₁} | ⟿©-contracts {t₂}
... | p₁ | p₂ = ⟿*©-AND p₁ p₂
⟿©-contracts {OR t₁ t₂} with t₁ ≅ t₂
⟿©-contracts {OR t₁ t₂} | inj₁ p rewrite p = ⟿*©-contract-same {t₂}
⟿©-contracts {OR t₁ t₂} | inj₂ _ with ⟿©-contracts {t₁} | ⟿©-contracts {t₂}
... | p₁ | p₂ = ⟿*©-OR p₁ p₂
⟿©-contracts {SAND t₁ t₂} with ⟿©-contracts {t₁} | ⟿©-contracts {t₂}
... | p₁ | p₂ = ⟿*©-SAND p₁ p₂

⟿*©-contract-same {NODE b} = ⟿©-step ⟿©-contract
⟿*©-contract-same {AND t₁ t₂} = ⟿©-trans (⟿©-step {OR (AND t₁ t₂) (AND t₁ t₂)}{AND t₁ t₂} ⟿©-contract) (⟿*©-AND (⟿©-contracts {t₁}) (⟿©-contracts {t₂}))
⟿*©-contract-same {OR t₁ t₂} with t₁ ≅ t₂
⟿*©-contract-same {OR t₁ t₂} | inj₁ p rewrite p with ⟿©-step {OR t₂ t₂}{t₂} ⟿©-contract
... | r₁ with ⟿*©-OR {OR t₂ t₂}{t₂}{OR t₂ t₂}{t₂} r₁ r₁
... | r₂ = ⟿©-trans {OR (OR t₂ t₂) (OR t₂ t₂)} {OR t₂ t₂} {contract t₂} r₂ ⟿*©-contract-same
⟿*©-contract-same {OR t₁ t₂} | inj₂ _ = ⟿©-trans (⟿©-step {OR (OR t₁ t₂) (OR t₁ t₂)}{OR t₁ t₂} ⟿©-contract) (⟿*©-OR (⟿©-contracts {t₁}) (⟿©-contracts {t₂}))
⟿*©-contract-same {SAND t₁ t₂} = ⟿©-trans (⟿©-step {OR (SAND t₁ t₂) (SAND t₁ t₂)}{SAND t₁ t₂} ⟿©-contract) (⟿*©-SAND (⟿©-contracts {t₁}) (⟿©-contracts {t₂}))

contract-refl : ∀{t} → contract (OR t t) ≡ contract t
contract-refl {t} with t ≅ t
contract-refl {t} | inj₁ eq = refl
contract-refl {t} | inj₂ neq with neq refl
... | ()

contract-neq : ∀{t₁ t₂} → ((t₁ ≡ t₂) → ⊥ {lzero}) → contract (OR t₁ t₂) ≡ OR (contract t₁) (contract t₂)
contract-neq {t₁}{t₂} p with t₁ ≅ t₂
contract-neq {t₁} {t₂} p | inj₁ refl with p refl
... | ()
contract-neq {t₁} {t₂} p | inj₂ y = refl

AND-neq₁ : ∀{t t₁ t₂} → ((AND t t₁ ≡ AND t t₂) → ⊥ {lzero}) → (t₁ ≡ t₂) → ⊥ {lzero}
AND-neq₁ {t}{t₁}{t₂} p refl = p refl

AND-neq₂ : ∀{t t₁ t₂} → ((AND t₁ t ≡ AND t₂ t) → ⊥ {lzero}) → (t₁ ≡ t₂) → ⊥ {lzero}
AND-neq₂ {t}{t₁}{t₂} p refl = p refl

↪-AND : ∀{t₁ s₁ t₂ s₂} → t₁ ↪ s₁ → t₂ ↪ s₂ → (AND t₁ t₂) ↪* (AND s₁ s₂)
↪-AND {t₁}{s₁}{t₂}{s₂} p₁ p₂ with ↪-AND₁ {t₁}{s₁}{t₂} p₁ | ↪-AND₂ {s₁}{t₂}{s₂} p₂
... | r₁ | r₂ = ↪-trans (↪-step r₁) (↪-step r₂)

↪*-AND : ∀{t₁ s₁ t₂ s₂} → t₁ ↪* s₁ → t₂ ↪* s₂ → (AND t₁ t₂) ↪* (AND s₁ s₂)
↪*-AND {t₁} {s₁} {t₂} {s₂} (↪-step p₁) (↪-step p₂) = ↪-AND p₁ p₂
↪*-AND {t₁} {s₁} {t₂} {.t₂} (↪-step p) ↪-refl = ↪-step (↪-AND₁ p)
↪*-AND {t₁} {s₁} {t₂} {s₂} p₁ (↪-trans {_}{t₃}{_} p₂ p₃) with ↪*-AND p₁ p₂ | ↪*-AND {s₁}{s₁}{t₃}{s₂} ↪-refl p₃
... | r₁ | r₂ = ↪-trans r₁ r₂
↪*-AND {t₁} {.t₁} {t₂} {s₂} ↪-refl (↪-step p) = ↪-step (↪-AND₂ p)
↪*-AND {t₁} {.t₁} {t₂} {.t₂} ↪-refl ↪-refl = ↪-refl
↪*-AND {t₁} {s₁} {t₂} {s₂} (↪-trans {_}{t₃}{_} p₁ p₂) p with ↪*-AND p₁ p | ↪*-AND {t₃}{s₁}{s₂}{s₂} p₂ ↪-refl
... | r₁ | r₂ = ↪-trans r₁ r₂

postulate CR : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿* s₁ → t₂ ⟿* s₂ → Σ[ s' ∈ ATree ]( (s₁ ⟿* s') × (s₂ ⟿* s') )

≈'-trans : ∀{t₁ t₂ t₃} → t₁ ≈' t₂ → t₂ ≈' t₃ → t₁ ≈' t₃
≈'-trans {t₁} {t₂} {t₃} (t₄ , p₁ , p₂) (t₅ , p₃ , p₄) with CR p₂ p₃
≈'-trans {t₁} {t₂} {t₃} (t₄ , p₁ , p₂) (t₅ , p₃ , p₄) | s , p₅ , p₆ = s , ((⟿-trans p₁ p₅) , (⟿-trans p₄ p₆))

≈-≈' : ∀{t₁ t₂} → t₁ ≈ t₂ → t₁ ≈' t₂
≈-≈' {t₁} {t₂} (≈-reduce p) = t₂ , ((⟿-step p) , ⟿-refl)
≈-≈' {t₁} {.t₁} ≈-refl = t₁ , (⟿-refl , ⟿-refl)
≈-≈' {t₁} {t₂} (≈-sym p) with ≈-≈' p
≈-≈' {t₁} {t₂} (≈-sym p) | t₃ , p₁ , p₂ = t₃ , (p₂ , p₁)
≈-≈' {t₁} {t₂} (≈-trans {_}{t₃}{_} p₁ p₂) with ≈-≈' p₁ | ≈-≈' p₂
≈-≈' {t₁} {t₂} (≈-trans {_}{t₅}{_} p₁ p₂) | r₁ | r₂ = ≈'-trans r₁ r₂

⟿*-≈ : ∀{t s} → t ⟿* s → t ≈ s
⟿*-≈ {t} {s} (⟿-step x) = ≈-reduce x
⟿*-≈ {t} {.t} ⟿-refl = ≈-refl
⟿*-≈ {t} {s} (⟿-trans {_}{t'}{_} p₁ p₂) with ⟿*-≈ p₁ | ⟿*-≈ p₂
... | r₁ | r₂ = ≈-trans r₁ r₂

≈'-≈ : ∀{t₁ t₂} → t₁ ≈' t₂ → t₁ ≈ t₂
≈'-≈ {t₁} {t₂} (s , p₁ , p₂) with ⟿*-≈ p₁ | ≈-sym (⟿*-≈ p₂)
... | r₁ | r₂ = ≈-trans r₁ r₂

-- -- infix 21 ⟦_⟧_

-- -- ⟦_⟧_ : ATree → (𝔹 → Obj) → Obj
-- -- ⟦ NODE b ⟧ α = α b
-- -- ⟦ AND t₁ t₂ ⟧ α = ⟦ t₁ ⟧ α ⊙ ⟦ t₂ ⟧ α
-- -- ⟦ OR t₁ t₂ ⟧ α = ⟦ t₁ ⟧ α ⊔ₒ ⟦ t₂ ⟧ α
-- -- ⟦ SAND t₁ t₂ ⟧ α = ⟦ t₁ ⟧ α ▷ ⟦ t₂ ⟧ α

-- -- ⟿©-interp : ∀{t₁ t₂ α} → t₁ ⟿© t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ⟿©-interp {.(OR t₂ t₂)} {t₂} ⟿©-contract = ⊔-contract
-- -- ⟿©-interp {.(AND _ _)} {.(AND _ _)} (⟿©-AND₁ p) = ⟿©-interp p ⊙ₐ id
-- -- ⟿©-interp {.(AND _ _)} {.(AND _ _)} (⟿©-AND₂ p) = id ⊙ₐ ⟿©-interp p
-- -- ⟿©-interp {.(OR _ _)} {.(OR _ _)} (⟿©-OR₁ p) = ⟿©-interp p ⊔ₐ id
-- -- ⟿©-interp {.(OR _ _)} {.(OR _ _)} (⟿©-OR₂ p) = id ⊔ₐ ⟿©-interp p
-- -- ⟿©-interp {.(SAND _ _)} {.(SAND _ _)} (⟿©-SAND₁ p) = ⟿©-interp p ▷ₐ id
-- -- ⟿©-interp {.(SAND _ _)} {.(SAND _ _)} (⟿©-SAND₂ p) = id ▷ₐ ⟿©-interp p

-- -- ⟿*©-interp : ∀{t₁ t₂ α} → t₁ ⟿*© t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ⟿*©-interp {t₁} {t₂} (⟿©-step p) = ⟿©-interp p
-- -- ⟿*©-interp {t₁} {.t₁} ⟿©-refl = id
-- -- ⟿*©-interp {t₁} {t₃} (⟿©-trans {_}{t₂}{_} p₁ p₂) = ⟿*©-interp p₁ ○ ⟿*©-interp p₂

-- -- ↪-interp : ∀{t₁ t₂ α} → t₁ ↪ t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ↪-interp ↪-OR-sym = ⊔-β
-- -- ↪-interp ↪-AND-sym = ⊙-β
-- -- ↪-interp ↪-OR-assoc = ⊔-α-inv
-- -- ↪-interp ↪-AND-assoc = ⊙-α-inv
-- -- ↪-interp ↪-SAND-assoc = ▷-α-inv
-- -- ↪-interp ↪-AND-distl = ⊔-⊙-distl
-- -- ↪-interp ↪-SAND-distl = ⊔-▷-distl
-- -- ↪-interp ↪-AND-distr = ⊔-⊙-distr
-- -- ↪-interp ↪-SAND-distr = ⊔-▷-distr
-- -- ↪-interp (↪-AND₁ p) = ↪-interp p ⊙ₐ id
-- -- ↪-interp (↪-AND₂ p) = id ⊙ₐ ↪-interp p
-- -- ↪-interp (↪-OR₁ p) = ↪-interp p ⊔ₐ id
-- -- ↪-interp (↪-OR₂ p) = id ⊔ₐ ↪-interp p
-- -- ↪-interp (↪-SAND₁ p) = ↪-interp p ▷ₐ id
-- -- ↪-interp (↪-SAND₂ p) = id ▷ₐ ↪-interp p

-- -- ↪-interp-inv : ∀{t₁ t₂ α} → t₁ ↪ t₂ → Hom (⟦ t₂ ⟧ α) (⟦ t₁ ⟧ α)
-- -- ↪-interp-inv {.(OR _ _)} {.(OR _ _)} ↪-OR-sym = ⊔-β
-- -- ↪-interp-inv {.(AND _ _)} {.(AND _ _)} ↪-AND-sym = ⊙-β
-- -- ↪-interp-inv {.(OR _ (OR _ _))} {.(OR (OR _ _) _)} ↪-OR-assoc = ⊔-α
-- -- ↪-interp-inv {.(AND _ (AND _ _))} {.(AND (AND _ _) _)} ↪-AND-assoc = ⊙-α
-- -- ↪-interp-inv {.(SAND _ (SAND _ _))} {.(SAND (SAND _ _) _)} ↪-SAND-assoc = ▷-α
-- -- ↪-interp-inv {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} ↪-AND-distl = ⊔-⊙-distl-inv
-- -- ↪-interp-inv {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} ↪-SAND-distl = ⊔-▷-distl-inv
-- -- ↪-interp-inv {.(AND (OR _ _) _)} {.(OR (AND _ _) (AND _ _))} ↪-AND-distr = ⊔-⊙-distr-inv
-- -- ↪-interp-inv {.(SAND (OR _ _) _)} {.(OR (SAND _ _) (SAND _ _))} ↪-SAND-distr = ⊔-▷-distr-inv
-- -- ↪-interp-inv {.(AND _ _)} {.(AND _ _)} (↪-AND₁ p) = ↪-interp-inv p ⊙ₐ id
-- -- ↪-interp-inv {.(AND _ _)} {.(AND _ _)} (↪-AND₂ p) = id ⊙ₐ ↪-interp-inv p
-- -- ↪-interp-inv {.(OR _ _)} {.(OR _ _)} (↪-OR₁ p) = ↪-interp-inv p ⊔ₐ id
-- -- ↪-interp-inv {.(OR _ _)} {.(OR _ _)} (↪-OR₂ p) = id ⊔ₐ ↪-interp-inv p
-- -- ↪-interp-inv {.(SAND _ _)} {.(SAND _ _)} (↪-SAND₁ p) = ↪-interp-inv p ▷ₐ id
-- -- ↪-interp-inv {.(SAND _ _)} {.(SAND _ _)} (↪-SAND₂ p) = id ▷ₐ ↪-interp-inv p

-- -- ↪*-interp : ∀{t₁ t₂ α} → t₁ ↪* t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ↪*-interp {t₁} {t₂} (↪-step p) = ↪-interp p
-- -- ↪*-interp {t₁} {.t₁} ↪-refl = id
-- -- ↪*-interp {t₁} {t₃} (↪-trans {_}{t₂}{_} p₁ p₂) = ↪*-interp p₁ ○ ↪*-interp p₂

-- -- ↪*-interp-inv : ∀{t₁ t₂ α} → t₁ ↪* t₂ → Hom (⟦ t₂ ⟧ α) (⟦ t₁ ⟧ α)
-- -- ↪*-interp-inv {t₁} {t₂} (↪-step p) = ↪-interp-inv p
-- -- ↪*-interp-inv {t₁} {.t₁} ↪-refl = id
-- -- ↪*-interp-inv {t₁} {t₂} (↪-trans p₁ p₂) = ↪*-interp-inv p₂ ○ ↪*-interp-inv p₁

-- -- ⟿-interp : ∀{t₁ t₂ α} → t₁ ⟿ t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ⟿-interp {t₁} {t₂} (↪-reduce p) = ↪-interp p
-- -- ⟿-interp {.(OR t₂ t₂)} {t₂} ⟿-contract = ⊔-contract

-- -- ⟿*-interp : ∀{t₁ t₂ α} → t₁ ⟿* t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ⟿*-interp {t₁} {t₂} (⟿-step p) = ⟿-interp p
-- -- ⟿*-interp {t₁} {.t₁} ⟿-refl = id
-- -- ⟿*-interp {t₁} {t₃} (⟿-trans {_}{t₂}{_} p₁ p₂) = ⟿*-interp p₁ ○ ⟿*-interp p₂

-- -- ≃-interp : ∀{t₁ t₂ α} → t₁ ≃ t₂ → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
-- -- ≃-interp-inv : ∀{t₁ t₂ α} → t₁ ≃ t₂ → Hom (⟦ t₂ ⟧ α) (⟦ t₁ ⟧ α)
-- -- ≃-interp {t₁} {t₂} (↪-reduce p) = ↪*-interp p
-- -- ≃-interp {t₁} {t₂} (≃-sym p) = ≃-interp-inv p
-- -- ≃-interp-inv {t₁} {t₂} (↪-reduce p) = ↪*-interp-inv p
-- -- ≃-interp-inv {t₁} {t₂} (≃-sym p) = ≃-interp p
