open import prelude

module attack-tree {𝔹 : Set} {pf : dec 𝔹} where

data ATree : Set where
  NODE : (b : 𝔹) → ATree
  AND  : ATree → ATree → ATree
  OR   : ATree → ATree → ATree
  SAND : ATree → ATree → ATree

mutual
  data STree : Set where
    S-NODE : (b : 𝔹) → STree
    S-SAND' : STree → CTree → STree

  data CTree : Set where
    C-NODE : (b : 𝔹) → CTree
    C-AND : CTree → STree → CTree    

data CSTree : Set where
  ct : CTree → CSTree
  st : STree → CSTree

data NATree : Set where
  NA-NODE : (b : 𝔹) → NATree
  NA-OR : NATree → CSTree → NATree
  NA-CSTree : CSTree → NATree
  
nf : NATree → ATree
nf-C : CTree → ATree
nf-S : STree → ATree
nf (NA-NODE b) = NODE b
nf (NA-OR t₁ (ct t₂)) = OR (nf t₁) (nf-C t₂)
nf (NA-OR t₁ (st t₂)) = OR (nf t₁) (nf-S t₂)
nf (NA-CSTree (ct t)) = nf-C t
nf (NA-CSTree (st t)) = nf-S t
nf-C (C-NODE b) = NODE b
nf-C (C-AND t₁ t₂) = AND (nf-C t₁) (nf-S t₂)
nf-S (S-NODE b) = NODE b
nf-S (S-SAND' t₁ t₂) = SAND (nf-S t₁) (nf-C t₂)

NODE-neq : ∀{b₁ b₂} → ((b₁ ≡ b₂) → ⊥ {lzero}) → NODE b₁ ≡ NODE b₂ → ⊥ {lzero}
NODE-neq x refl = x refl

AND-neq : ∀{t₁ t₂ t₃ t₄} → (((t₁ ≡ t₃) → ⊥ {lzero}) ⊎ ((t₂ ≡ t₄) → ⊥ {lzero})) → AND t₁ t₂ ≡ AND t₃ t₄ → ⊥ {lzero}
AND-neq (inj₁ x) refl = x refl
AND-neq (inj₂ y) refl = y refl

OR-AND-neq : ∀{t₁ t₂ t₃ t₄} → OR t₁ t₂ ≡ AND t₃ t₄ → ⊥ {lzero}
OR-AND-neq ()

AND-NODE-neq : ∀{t₁ t₂ b} → AND t₁ t₂ ≡ NODE b → ⊥ {lzero}
AND-NODE-neq ()

OR-neq : ∀{t₁ t₂ t₃ t₄} → (((t₁ ≡ t₃) → ⊥ {lzero}) ⊎ ((t₂ ≡ t₄) → ⊥ {lzero})) → OR t₁ t₂ ≡ OR t₃ t₄ → ⊥ {lzero}
OR-neq (inj₁ x) refl = x refl
OR-neq (inj₂ y) refl = y refl

OR-NODE-neq : ∀{t₁ t₂ b} → OR t₁ t₂ ≡ NODE b → ⊥ {lzero}
OR-NODE-neq ()

SAND-neq : ∀{t₁ t₂ t₃ t₄} → (((t₁ ≡ t₃) → ⊥ {lzero}) ⊎ ((t₂ ≡ t₄) → ⊥ {lzero})) → SAND t₁ t₂ ≡ SAND t₃ t₄ → ⊥ {lzero}
SAND-neq (inj₁ x) refl = x refl
SAND-neq (inj₂ y) refl = y refl

SAND-OR-neq : ∀{t₁ t₂ t₃ t₄} → SAND t₁ t₂ ≡ OR t₃ t₄ → ⊥ {lzero}
SAND-OR-neq ()

SAND-AND-neq : ∀{t₁ t₂ t₃ t₄} → SAND t₁ t₂ ≡ AND t₃ t₄ → ⊥ {lzero}
SAND-AND-neq ()

SAND-NODE-neq : ∀{t₁ t₂ b} → SAND t₁ t₂ ≡ NODE b → ⊥ {lzero}
SAND-NODE-neq ()
   
_≅_ : (t₁ : ATree) → (t₂ : ATree) → ((t₁ ≡ t₂) ⊎ (t₁ ≡ t₂ → ⊥ {lzero}))
NODE b₁ ≅ NODE b₂ with dec-pf pf {b₁}{b₂}
NODE b₁ ≅ NODE b₂ | inj₁ x = inj₁ (cong {A = 𝔹}{ATree} NODE {b₁}{b₂} x)
NODE b₁ ≅ NODE b₂ | inj₂ y = inj₂ (NODE-neq y) 
NODE b ≅ AND t₂ t₃ = inj₂ (λ x → AND-NODE-neq {t₂}{t₃}{b} (sym x))
NODE b ≅ OR t₂ t₃ = inj₂ (λ x → OR-NODE-neq (sym x))
NODE b ≅ SAND t₂ t₃ = inj₂ (λ x → SAND-NODE-neq (sym x))
AND t₁ t₂ ≅ NODE b = inj₂ AND-NODE-neq
AND t₁ t₂ ≅ AND t₃ t₄ with t₁ ≅ t₃ | t₂ ≅ t₄
AND t₁ t₂ ≅ AND t₃ t₄ | inj₁ refl | (inj₁ refl) = inj₁ refl
AND t₁ t₂ ≅ AND t₃ t₄ | inj₁ refl | (inj₂ y) = inj₂ (AND-neq (inj₂ y))
AND t₁ t₂ ≅ AND t₃ t₄ | inj₂ y | (inj₁ refl) = inj₂ (AND-neq (inj₁ y))
AND t₁ t₂ ≅ AND t₃ t₄ | inj₂ y₁ | (inj₂ y₂) = inj₂ (AND-neq (inj₁ y₁))
AND t₁ t₂ ≅ OR t₃ t₄ = inj₂ (λ x → OR-AND-neq (sym x))
AND t₁ t₂ ≅ SAND t₃ t₄ = inj₂ (λ x → SAND-AND-neq (sym x))
OR t₁ t₂ ≅ NODE b = inj₂ OR-NODE-neq
OR t₁ t₂ ≅ AND t₃ t₄ = inj₂ OR-AND-neq
OR t₁ t₂ ≅ OR t₃ t₄ with t₁ ≅ t₃ | t₂ ≅ t₄
OR t₁ t₂ ≅ OR t₃ t₄ | inj₁ refl | (inj₁ refl) = inj₁ refl
OR t₁ t₂ ≅ OR t₃ t₄ | inj₁ refl | (inj₂ y) = inj₂ (OR-neq (inj₂ y))
OR t₁ t₂ ≅ OR t₃ t₄ | inj₂ y | (inj₁ refl) = inj₂ (OR-neq (inj₁ y))
OR t₁ t₂ ≅ OR t₃ t₄ | inj₂ y₁ | (inj₂ y₂) = inj₂ (OR-neq (inj₁ y₁))
OR t₁ t₂ ≅ SAND t₃ t₄ = inj₂ (λ x → SAND-OR-neq (sym x)) 
SAND t₁ t₂ ≅ NODE b = inj₂ SAND-NODE-neq 
SAND t₁ t₂ ≅ AND t₃ t₄ = inj₂ (SAND-AND-neq {t₁}{t₂}{t₃}{t₄})  
SAND t₁ t₂ ≅ OR t₃ t₄ = inj₂ (SAND-OR-neq {t₁}{t₂}{t₃}{t₄})
SAND t₁ t₂ ≅ SAND t₃ t₄ with t₁ ≅ t₃ | t₂ ≅ t₄
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₁ refl | (inj₁ refl) = inj₁ refl
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₁ refl | (inj₂ y) = inj₂ (SAND-neq {t₁}{t₂}{t₁}{t₄} (inj₂ y))
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₂ y | (inj₁ refl) = inj₂ (SAND-neq {t₁}{t₂}{t₃}{t₂} (inj₁ y))
SAND t₁ t₂ ≅ SAND t₃ t₄ | inj₂ y₁ | (inj₂ y₂) = inj₂ (SAND-neq {t₁}{t₂}{t₃}{t₄} (inj₁ y₁))

_≠_ : ATree → ATree → Set
A ≠ B = (A ≡ B) → ⊥ {lzero}

-- Original equiality by Jahwar et al.:
data _≈ₒ_ : ATree → ATree → Set where
  ≈ₒ-refl : ∀{A : ATree} → A ≈ₒ A
  ≈ₒ-sym : ∀{A B : ATree} → A ≈ₒ B → B ≈ₒ A
  ≈ₒ-trans : ∀{A B C : ATree} → A ≈ₒ B → B ≈ₒ C → A ≈ₒ C
  ≈ₒ-contract : ∀{A : ATree} → (OR A A) ≈ₒ A
  ≈ₒ-OR-sym : ∀{A B : ATree} → (OR A B) ≈ₒ (OR B A)
  ≈ₒ-AND-sym : ∀{A B : ATree} → (AND A B) ≈ₒ (AND B A)
  ≈ₒ-OR-assoc : ∀{A B C : ATree} → (OR A (OR B C)) ≈ₒ (OR (OR A B) C)
  ≈ₒ-AND-assoc : ∀{A B C : ATree} → (AND A (AND B C)) ≈ₒ (AND (AND A B) C)
  ≈ₒ-SAND-assoc : ∀{A B C : ATree} → (SAND A (SAND B C)) ≈ₒ (SAND (SAND A B) C)
  ≈ₒ-AND-distl : ∀{A B C : ATree} → (AND A (OR B C)) ≈ₒ (OR (AND A B) (AND A C))
  ≈ₒ-SAND-distl : ∀{A B C : ATree} → (SAND A (OR B C)) ≈ₒ (OR (SAND A B) (SAND A C))
  ≈ₒ-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ≈ₒ A₂ → (AND A₁ B) ≈ₒ (AND A₂ B)
  ≈ₒ-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ≈ₒ B₂ → (AND A B₁) ≈ₒ (AND A B₂)
  ≈ₒ-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ≈ₒ A₂ → (OR A₁ B) ≈ₒ (OR A₂ B)
  ≈ₒ-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ≈ₒ B₂ → (OR A B₁) ≈ₒ (OR A B₂)
  ≈ₒ-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ≈ₒ A₂ → (SAND A₁ B) ≈ₒ (SAND A₂ B)
  ≈ₒ-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ≈ₒ B₂ → (SAND A B₁) ≈ₒ (SAND A B₂)

notOR : ATree → Set
notOR (OR _ _) = ⊥
notOR _ = ⊤

notAND : ATree → Set
notAND (AND _ _) = ⊥
notAND _ = ⊤

notSAND : ATree → Set
notSAND (SAND _ _) = ⊥
notSAND _ = ⊤

data _⟿_ : ATree → ATree → Set where
  ⟿-AND-distl-assoc₁ : ∀{A B B' C : ATree} → notAND C → (AND A (OR (AND B B') C)) ⟿ (OR (AND (AND A B) B') (AND A C))
  ⟿-AND-distl-assoc₂ : ∀{A B C C' : ATree} → notAND B → (AND A (OR B (AND C C'))) ⟿ (OR (AND A B) (AND (AND A C) C'))
  ⟿-AND-distl-assoc₃ : ∀{A B B' C C' : ATree} → (AND A (OR (AND B B') (AND C C'))) ⟿ (OR (AND (AND A B) B') (AND (AND A C) C'))  
  ⟿-AND-distl : ∀{A B C : ATree} → notAND B → notAND C → (AND A (OR B C)) ⟿ (OR (AND A B) (AND A C))

  ⟿-SAND-distl-assoc₁ : ∀{A B B' C : ATree} → notSAND C → (SAND A (OR (SAND B B') C)) ⟿ (OR (SAND (SAND A B) B') (SAND A C))
  ⟿-SAND-distl-assoc₂ : ∀{A B C C' : ATree} → notSAND B → (SAND A (OR B (SAND C C'))) ⟿ (OR (SAND A B) (SAND (SAND A C) C'))
  ⟿-SAND-distl-assoc₃ : ∀{A B B' C C' : ATree} → (SAND A (OR (SAND B B') (SAND C C'))) ⟿ (OR (SAND (SAND A B) B') (SAND (SAND A C) C'))  
  ⟿-SAND-distl : ∀{A B C : ATree} → notSAND B → notSAND C → (SAND A (OR B C)) ⟿ (OR (SAND A B) (SAND A C))

  ⟿-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (AND A₁ B) ⟿ (AND A₂ B)
  ⟿-AND₂-assoc : ∀{A B C D : ATree} → B ⟿ (AND C D) → (AND A B) ⟿ (AND (AND A C) D)
  ⟿-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → notAND B₂ → (AND A B₁) ⟿ (AND A B₂)

  ⟿-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (OR A₁ B) ⟿ (OR A₂ B)
  ⟿-OR₂-assoc-contract : ∀{A B C : ATree} → B ⟿ (OR A C) → (OR A B) ⟿ (OR A C)
  ⟿-OR₂-assoc : ∀{A B C D : ATree} → B ⟿ (OR C D) → A ≠ C → (OR A B) ⟿ (OR (OR A C) D)
  ⟿-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → notOR B₂ → (OR A B₁) ⟿ (OR A B₂)

  ⟿-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (SAND A₁ B) ⟿ (SAND A₂ B)
  ⟿-SAND₂-assoc : ∀{A B C D : ATree} → B ⟿ (SAND C D) → (SAND A B) ⟿ (SAND (SAND A C) D)
  ⟿-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → notSAND B₂ → (SAND A B₁) ⟿ (SAND A B₂)

data _⟿*_ : ATree → ATree → Set where
  ⟿-step : ∀{A B : ATree} → A ⟿ B → A ⟿* B
  ⟿-refl : ∀{A : ATree} → A ⟿* A
  ⟿-trans : ∀{A B C : ATree} → A ⟿* B → B ⟿* C → A ⟿* C

data _≈-sym_ : ATree → ATree → Set where
  ≈-sym-refl : ∀{A : ATree} → A ≈-sym A
  ≈-sym-sym : ∀{A B : ATree} → A ≈-sym B → B ≈-sym A
  ≈-sym-trans : ∀{A B C : ATree} → A ≈-sym B → B ≈-sym C → A ≈-sym C
  ≈-sym-OR-sym : ∀{A B : ATree} → (OR A B) ≈-sym (OR B A)
  ≈-sym-AND-sym : ∀{A B : ATree} → (AND A B) ≈-sym (AND B A)
  ≈-sym-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ≈-sym A₂ → (AND A₁ B) ≈-sym (AND A₂ B)
  ≈-sym-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ≈-sym B₂ → (AND A B₁) ≈-sym (AND A B₂)
  ≈-sym-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ≈-sym A₂ → (OR A₁ B) ≈-sym (OR A₂ B)
  ≈-sym-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ≈-sym B₂ → (OR A B₁) ≈-sym (OR A B₂)
  ≈-sym-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ≈-sym A₂ → (SAND A₁ B) ≈-sym (SAND A₂ B)
  ≈-sym-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ≈-sym B₂ → (SAND A B₁) ≈-sym (SAND A B₂)

--------------------------------------------------------------------------------------------
--                                                                                        --
-- Termination of ⟿                                                                      --
--                                                                                        --
--------------------------------------------------------------------------------------------

W : ATree → ℕ
W (NODE b) = 1
W (AND A B) = (W A * W B) * 2
W (SAND A B) = (W A * W B) * 2
W (OR A B) = W A + W B + 2

postulate aux₁ : ∀{m n} → 0 < m ≡ tt → 0 < n ≡ tt → 0 < m * n * 2 ≡ tt
postulate aux₂ : ∀{m n} → m + n + 2 > 0 ≡ tt
--   m * n * 2 + m * r * 2 + 2
-- = (m * n + m * r) * 2 + 2
-- = m * (n + r) * 2 + 2
-- < m * (n + r + 2) * 2
postulate aux₃ : ∀{m n r} → m * (n + r + 2) * 2 > m * n * 2 + m * r * 2 + 2 ≡ tt
postulate aux₄ : ∀{m n r} → r < m ≡ tt → r * n * 2 < m * n * 2 ≡ tt
--   m * r * 2 * s * 2
-- = m * (r * s * 2) * 2
-- < m * n * 2
postulate aux₅ : ∀{m n r s} → r * s * 2 < n ≡ tt → m * r * 2 * s * 2 < m * n * 2 ≡ tt
postulate aux₆ : ∀{m n r} → n > r ≡ tt → m * n * 2 > m * r * 2 ≡ tt
postulate aux₇ : ∀{m n r} → r < m ≡ tt → r + n + 2 < m + n + 2 ≡ tt
postulate aux₈ : ∀{m n r} → m + r + 2 < n ≡ tt → m + r + 2 < m + n + 2 ≡ tt
postulate aux₉ : ∀{m n r s} → r + s + 2 < n ≡ tt → m + r + 2 + s + 2 < m + n + 2 ≡ tt
postulate aux₁₀ : ∀{m n r} → n < r ≡ tt → m + n + 2 < m + r + 2 ≡ tt

W>0 : ∀{A} → W A > 0 ≡ tt
W>0 {NODE b} = refl
W>0 {AND A B} with W>0 {A} | W>0 {B}
... | r₁ | r₂ = aux₁ {W A}{W B} r₁ r₂
W>0 {SAND A B} with W>0 {A} | W>0 {B}
... | r₁ | r₂ = aux₁ {W A}{W B} r₁ r₂
W>0 {OR A B} = aux₂ {W A}

-- ⟿-decreasing : ∀{t₁ t₂} → t₁ ⟿ t₂ → W t₁ > W t₂ ≡ tt
-- ⟿-decreasing {AND A (OR B C)} {.(OR (AND _ _) (AND _ _))} ⟿-AND-distl = aux₃ {W A}{W B}{W C} 
-- ⟿-decreasing {SAND A (OR B C)} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-distl = aux₃ {W A}{W B}{W C} 
-- ⟿-decreasing {AND A B} {AND C .B} (⟿-AND₁ d) with ⟿-decreasing d
-- ... | r = aux₄ {W A}{W B}{W C} r
-- ⟿-decreasing {AND A B} {AND (AND C D) E} (⟿-AND₂-assoc d) with ⟿-decreasing d
-- ... | r = aux₅ {W A} {W B} {W D} {W E} r
-- ⟿-decreasing {AND A B} {AND .A D} (⟿-AND₂ d x) with ⟿-decreasing d
-- ... | r = aux₆ {W A}{W B}{W D} r
-- ⟿-decreasing {SAND A B} {SAND C .B} (⟿-SAND₁ d) with ⟿-decreasing d
-- ... | r = aux₄ {W A}{W B}{W C} r
-- ⟿-decreasing {SAND A B} {SAND (SAND C D) E} (⟿-SAND₂-assoc d) with ⟿-decreasing d
-- ... | r = aux₅ {W A} {W B} {W D} {W E} r
-- ⟿-decreasing {SAND A B} {SAND .A D} (⟿-SAND₂ d x) with ⟿-decreasing d
-- ... | r = aux₆ {W A}{W B}{W D} r
-- ⟿-decreasing {OR A B} {OR C _} (⟿-OR₁ d) with ⟿-decreasing d
-- ... | r = aux₇ {W A} {W B} {W C} r
-- ⟿-decreasing {OR A B} {OR .A C} (⟿-OR₂-assoc-contract d) with ⟿-decreasing d
-- ... | r = aux₈ {W A} {W B} {W C} r
-- ⟿-decreasing {OR A B} {OR (OR C D) E} (⟿-OR₂-assoc d x) with ⟿-decreasing d
-- ... | r = aux₉ {W A} {W B} {W D} {W E} r
-- ⟿-decreasing {OR A B} {OR _ D} (⟿-OR₂ d x) with ⟿-decreasing d
-- ... | r = aux₁₀ {W A} {W D} {W B} r

-- --------------------------------------------------------------------------------------------
-- --                                                                                        --
-- -- Confluence of ⟿                                                                       --
-- --                                                                                        --
-- --------------------------------------------------------------------------------------------

-- ⟿*-AND₁ : ∀{A A' B} → A ⟿* A' → AND A B ⟿* AND A' B
-- ⟿*-AND₁ {A} {A'} {B} (⟿-step x) = ⟿-step (⟿-AND₁ x)
-- ⟿*-AND₁ {A} {.A} {B} ⟿-refl = ⟿-refl
-- ⟿*-AND₁ {A} {A'} {B} (⟿-trans {_}{B'}{_} p₁ p₂) = ⟿-trans (⟿*-AND₁ p₁) (⟿*-AND₁ p₂)

-- ⟿*-SAND₁ : ∀{A A' B} → A ⟿* A' → SAND A B ⟿* SAND A' B
-- ⟿*-SAND₁ {A} {A'} {B} (⟿-step x) = ⟿-step (⟿-SAND₁ x)
-- ⟿*-SAND₁ {A} {.A} {B} ⟿-refl = ⟿-refl
-- ⟿*-SAND₁ {A} {A'} {B} (⟿-trans {_}{B'}{_} p₁ p₂) = ⟿-trans (⟿*-SAND₁ p₁) (⟿*-SAND₁ p₂)

-- ⟿*-OR₁ : ∀{A A' B} → A ⟿* A' → OR A B ⟿* OR A' B
-- ⟿*-OR₁ {A} {A'} {B} (⟿-step x) = ⟿-step (⟿-OR₁ x)
-- ⟿*-OR₁ {A} {.A} {B} ⟿-refl = ⟿-refl
-- ⟿*-OR₁ {A} {A'} {B} (⟿-trans {_}{B'}{_} p₁ p₂) = ⟿-trans (⟿*-OR₁ p₁) (⟿*-OR₁ p₂)

-- ⟿*-NODE-left : ∀{A b} → NODE b ⟿* A → A ≡ NODE b
-- ⟿*-NODE-left {A} {b} (⟿-step ())
-- ⟿*-NODE-left {.(NODE b)} {b} ⟿-refl = refl
-- ⟿*-NODE-left {A} {b} (⟿-trans d₁ d₂) rewrite ⟿*-NODE-left d₁ = ⟿*-NODE-left d₂

-- ⟿*-NODE : ∀{A b} → A ⟿* NODE b → A ≡ NODE b
-- ⟿*-NODE {A} {b} (⟿-step ())
-- ⟿*-NODE {.(NODE b)} {b} ⟿-refl = refl
-- ⟿*-NODE {A} {b} (⟿-trans {_}{B} p₁ p₂) rewrite ⟿*-NODE p₂ = ⟿*-NODE p₁

-- ⟿*-AND-node : ∀{A B b} → AND A B ⟿* NODE b → ⊥ {lzero}
-- ⟿*-AND-node {A} {B} {b} (⟿-step ())
-- ⟿*-AND-node {A} {B} {b} (⟿-trans {_}{B'}{_} p₁ p₂) rewrite ⟿*-NODE p₂ = ⟿*-AND-node p₁

-- ⟿*-AND₂ : ∀{A B B'} → B ⟿* B' → notAND B' → AND A B ⟿* AND A B'
-- ⟿*-AND₂ {A} {B} {B'} (⟿-step x) p = ⟿-step (⟿-AND₂ x p)
-- ⟿*-AND₂ {A} {B} {.B} ⟿-refl p = ⟿-refl
-- ⟿*-AND₂ {A} {B} {B'} (⟿-trans {_}{C} d₁ d₂) p with ⟿*-AND₂ {A} d₂ p
-- ... | r₁ = {!!}

-- ⟿-local-cf : ∀{A B C} → A ⟿ B → A ⟿ C → Σ[ D ∈ ATree ]( (B ⟿* D) × (C ⟿* D) )
-- ⟿-local-cf {AND A (OR B C)} {.(OR (AND _ _) (AND _ _))} {.(OR (AND _ _) (AND _ _))} ⟿-AND-distl ⟿-AND-distl = (OR (AND A B) (AND A C)) , (⟿-refl , ⟿-refl)
-- ⟿-local-cf {AND A (OR B C)} {OR (AND _ _) (AND _ _)} {AND A' (OR _ _)} ⟿-AND-distl (⟿-AND₁ d₂) = OR (AND A' B) (AND A' C) , {!⟿*-OR!} , {!!}
-- ⟿-local-cf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND (AND _ _) _)} ⟿-AND-distl (⟿-AND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ _)} ⟿-AND-distl (⟿-AND₂ d₂ x) = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-distl ⟿-SAND-distl = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ (OR _ _))} ⟿-SAND-distl (⟿-SAND₁ d₂) = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND (SAND _ _) _)} ⟿-SAND-distl (⟿-SAND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ _)} ⟿-SAND-distl (⟿-SAND₂ d₂ x) = {!!}
-- ⟿-local-cf {.(AND _ (OR _ _))} {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} (⟿-AND₁ d₁) ⟿-AND-distl = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₁ d₁) (⟿-AND₁ d₂) = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND _ _)} {.(AND (AND _ _) _)} (⟿-AND₁ d₁) (⟿-AND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₁ d₁) (⟿-AND₂ d₂ x) = {!!}
-- ⟿-local-cf {.(AND _ (OR _ _))} {.(AND (AND _ _) _)} {.(OR (AND _ _) (AND _ _))} (⟿-AND₂-assoc d₁) ⟿-AND-distl = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND (AND _ _) _)} {.(AND _ _)} (⟿-AND₂-assoc d₁) (⟿-AND₁ d₂) = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND (AND _ _) _)} {.(AND (AND _ _) _)} (⟿-AND₂-assoc d₁) (⟿-AND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND (AND _ _) _)} {.(AND _ _)} (⟿-AND₂-assoc d₁) (⟿-AND₂ d₂ x) = {!!}
-- ⟿-local-cf {.(AND _ (OR _ _))} {.(AND _ _)} {.(OR (AND _ _) (AND _ _))} (⟿-AND₂ d₁ x) ⟿-AND-distl = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₂ d₁ x) (⟿-AND₁ d₂) = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND _ _)} {.(AND (AND _ _) _)} (⟿-AND₂ d₁ x) (⟿-AND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₂ d₁ x) (⟿-AND₂ d₂ x₁) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ d₁) (⟿-OR₁ d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ d₁) (⟿-OR₂-assoc-contract d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR (OR _ _) _)} (⟿-OR₁ d₁) (⟿-OR₂-assoc d₂ x) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ d₁) (⟿-OR₂ d₂ x) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂-assoc-contract d₁) (⟿-OR₁ d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂-assoc-contract d₁) (⟿-OR₂-assoc-contract d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR (OR _ _) _)} (⟿-OR₂-assoc-contract d₁) (⟿-OR₂-assoc d₂ x) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂-assoc-contract d₁) (⟿-OR₂ d₂ x) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR _ _)} (⟿-OR₂-assoc d₁ x) (⟿-OR₁ d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR _ _)} (⟿-OR₂-assoc d₁ x) (⟿-OR₂-assoc-contract d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR (OR _ _) _)} (⟿-OR₂-assoc d₁ x) (⟿-OR₂-assoc d₂ x₁) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR _ _)} (⟿-OR₂-assoc d₁ x) (⟿-OR₂ d₂ x₁) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ d₁ x) (⟿-OR₁ d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ d₁ x) (⟿-OR₂-assoc-contract d₂) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR (OR _ _) _)} (⟿-OR₂ d₁ x) (⟿-OR₂-assoc d₂ x₁) = {!!}
-- ⟿-local-cf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ d₁ x) (⟿-OR₂ d₂ x₁) = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} (⟿-SAND₁ d₁) ⟿-SAND-distl = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₁ d₁) (⟿-SAND₁ d₂) = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND _ _)} {.(SAND (SAND _ _) _)} (⟿-SAND₁ d₁) (⟿-SAND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₁ d₁) (⟿-SAND₂ d₂ x) = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(SAND (SAND _ _) _)} {.(OR (SAND _ _) (SAND _ _))} (⟿-SAND₂-assoc d₁) ⟿-SAND-distl = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND (SAND _ _) _)} {.(SAND _ _)} (⟿-SAND₂-assoc d₁) (⟿-SAND₁ d₂) = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND (SAND _ _) _)} {.(SAND (SAND _ _) _)} (⟿-SAND₂-assoc d₁) (⟿-SAND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND (SAND _ _) _)} {.(SAND _ _)} (⟿-SAND₂-assoc d₁) (⟿-SAND₂ d₂ x) = {!!}
-- ⟿-local-cf {.(SAND _ (OR _ _))} {.(SAND _ _)} {.(OR (SAND _ _) (SAND _ _))} (⟿-SAND₂ d₁ x) ⟿-SAND-distl = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₂ d₁ x) (⟿-SAND₁ d₂) = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND _ _)} {.(SAND (SAND _ _) _)} (⟿-SAND₂ d₁ x) (⟿-SAND₂-assoc d₂) = {!!}
-- ⟿-local-cf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₂ d₁ x) (⟿-SAND₂ d₂ x₁) = {!!}

-- --------------------------------------------------------------------------------------------
-- --                                                                                        --
-- -- Full Rewrite System                                                                    --
-- --                                                                                        --
-- --------------------------------------------------------------------------------------------

-- rm-cts : ATree → ATree
-- rm-cts (NODE b) = NODE b
-- rm-cts (AND A B) = AND (rm-cts A) (rm-cts B) 
-- rm-cts (OR A B) with A ≅ B
-- rm-cts (OR A _) | inj₁ x = (rm-cts A)
-- rm-cts (OR A B) | inj₂ y with (rm-cts A) | (rm-cts B)
-- ... | T₁ | T₂ with T₁ ≅ T₂
-- rm-cts (OR A B) | inj₂ y | T₁ | T₂ | (inj₁ x) = T₁
-- rm-cts (OR A B) | inj₂ y₁ | T₁ | T₂ | (inj₂ y) = OR T₁ T₂
-- rm-cts (SAND A B) = SAND (rm-cts A) (rm-cts B) 

-- -- _≈_ : ATree → ATree → Set
-- -- t₁ ≈ t₂ with (rm-cts t₁) | (rm-cts t₂)
-- -- ... | s₁ | s₂ = Σ[ s₃ ∈ ATree ]( Σ[ s₄ ∈ ATree ](
-- --              (s₁ ⟿ᵣ* s₃) × (s₂ ⟿ᵣ* s₄) -- Put both into proper form.
-- --         × (let s₅ = rm-cts s₃
-- --                s₆ = rm-cts s₄
-- --             in s₅ ≈-sym s₆ )))

-- -- ⟿©*-contracts : ∀{t} → t ⟿©* (rm-cts t)
-- -- ⟿©*-contracts {OR A B} with A ≅ B
-- -- ... | inj₁ refl = let d = ⟿©*-contracts {A} in ⟿©-trans (⟿©-step ⟿©-contract) d
-- -- ... | inj₂ ⊥-pf₁ with (rm-cts A) ≅ (rm-cts B)
-- -- ... | inj₁ p = ⟿©-trans (⟿©*-OR (⟿©*-contracts {A}) (⟿©*-contracts {B})) (aux p)
-- --   where
-- --     aux : (rm-cts A) ≡ (rm-cts B) → OR (rm-cts A) (rm-cts B) ⟿©* rm-cts A
-- --     aux p rewrite p = ⟿©-step ⟿©-contract
-- -- ... | inj₂ ⊥-pf₂ = ⟿©*-OR (⟿©*-contracts {A}) ⟿©*-contracts
-- -- ⟿©*-contracts {NODE b} = ⟿©-refl
-- -- ⟿©*-contracts {AND A B} = ⟿©*-AND ⟿©*-contracts ⟿©*-contracts
-- -- ⟿©*-contracts {SAND A B} = ⟿©*-SAND ⟿©*-contracts ⟿©*-contracts

-- -- aux₁ : ∀{t₁ s₁ s₂} → (rm-cts t₁) ≈-sym s₂ → t₁ ⟿ᵣ* s₁ → (rm-cts s₁) ≈-sym s₂
-- -- aux₁ {t₁}{s₁}{s₂} p₁ p₂ = {!!}

-- -- ≈trans : ∀{t₂ t₁ t₃} → t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
-- -- ≈trans {t₂} {t₁} {t₃} (s₁ , s₂ , c₁ , c₂ , p₁-sym) (s₃ , s₄ , c'₁ , c'₂ , p₂-sym) with ⟿ᵣ-CR c₂ c'₁
-- -- ... | (s , r₁ , r₂) = s₁ , (s , (c₁ , ({!!} , ≈-sym-sym (aux₁ {s₂}{s}{rm-cts s₁} (≈-sym-sym p₁-sym) r₁))))

-- -- ⟿©*-≈© : ∀{t s} → t ⟿©* s → t ≈© s
-- -- ⟿©*-≈© {t} {s} (⟿©-step x) = ≈©-reduce x
-- -- ⟿©*-≈© {t} {.t} ⟿©-refl = ≈©-refl
-- -- ⟿©*-≈© {t} {s} (⟿©-trans {_}{t'}{_} p₁ p₂) with ⟿©*-≈© p₁ | ⟿©*-≈© p₂
-- -- ... | r₁ | r₂ = ≈©-trans r₁ r₂

-- -- postulate CR-⟿© : ∀{t s₁ s₂} → t ⟿©* s₁ → t ⟿©* s₂ → Σ[ s' ∈ ATree ]( (s₁ ⟿©* s') × (s₂ ⟿©* s') )
-- -- postulate CR-⟿ : ∀{t s₁ s₂} → t ⟿* s₁ → t ⟿* s₂ → Σ[ s' ∈ ATree ]( (s₁ ⟿* s') × (s₂ ⟿* s') )

-- -- _⟱_ : ∀(t₁ t₂ : ATree) → Set
-- -- t₁ ⟱ t₂ = Σ[ s ∈ ATree ]( t₁ ⟿* s × t₂ ⟿* s )

-- -- _≃ⱼ_ : ∀(t₁ t₂ : ATree) → Set
-- -- t₁ ≃ⱼ t₂ = Σ[ s₁ ∈ ATree ](Σ[ s₂ ∈ ATree ](t₁ ⟿©* s₁ × t₂ ⟿©* s₂ × s₁ ⟱ s₂))

-- -- _≃_ : ∀(t₁ t₂ : ATree) → Set
-- -- t₁ ≃ t₂ = Σ[ s₁ ∈ ATree ](Σ[ s₂ ∈ ATree ](t₁ ⟿©* s₁ × t₂ ⟿©* s₂ × s₁ ≈ s₂))

-- -- ⟱-refl : ∀{t} → t ⟱ t
-- -- ⟱-refl {t} = t , (⟿-refl , ⟿-refl)

-- -- ⟱-sym : ∀{t₁ t₂} → t₁ ⟱ t₂ → t₂ ⟱ t₁
-- -- ⟱-sym {t₁} {t₂} (s₁ , p₁ , p₂) = s₁ , (p₂ , p₁)

-- -- ⟱-trans : ∀{t₁ t₂ t₃} → t₁ ⟱ t₂ → t₂ ⟱ t₃ → t₁ ⟱ t₃
-- -- ⟱-trans {t₁}{t₂}{t₃} (s₁ , p₁ , p₂) (s₂ , p₃ , p₄) with CR-⟿ p₂ p₃
-- -- ... | (s₃ , p₅ , p₆) = s₃ , ((⟿-trans p₁ p₅) , ⟿-trans p₄ p₆)

-- -- ⟿-⟿© : ∀{t₁ t₂} → t₁ ⟿ t₂ → t₁ ⟿© t₂
-- -- ⟿-⟿© {NODE b} {NODE b₁} ()
-- -- ⟿-⟿© {NODE b} {AND t₄ t₅} ()
-- -- ⟿-⟿© {NODE b} {OR t₄ t₅} ()
-- -- ⟿-⟿© {NODE b} {SAND t₄ t₅} ()
-- -- ⟿-⟿© {AND t₄ t₅} {NODE b} ()
-- -- ⟿-⟿© {AND t₄ t₅} {AND .t₅ .t₄} ⟿-AND-sym = ⟿©-AND-sym
-- -- ⟿-⟿© {AND t₄ .(AND _ t₇)} {AND .(AND t₄ _) t₇} ⟿-AND-assoc = ⟿©-AND-assoc
-- -- ⟿-⟿© {AND t₄ t₅} {AND t₆ .t₅} (⟿-AND₁ p) = ⟿©-AND₁ (⟿-⟿© p)
-- -- ⟿-⟿© {AND t₄ t₅} {AND .t₄ t₇} (⟿-AND₂ p) = ⟿©-AND₂ (⟿-⟿© p)
-- -- ⟿-⟿© {AND t₄ .(OR _ _)} {OR .(AND t₄ _) .(AND t₄ _)} ⟿-AND-distl = ⟿©-AND-distl
-- -- ⟿-⟿© {AND .(OR _ _) t₅} {OR .(AND _ t₅) .(AND _ t₅)} ⟿-AND-distr = ⟿©-AND-distr
-- -- ⟿-⟿© {AND t₄ t₅} {SAND t₆ t₇} ()
-- -- ⟿-⟿© {OR t₄ t₅} {NODE b} ()
-- -- ⟿-⟿© {OR t₄ t₅} {AND t₆ t₇} ()
-- -- ⟿-⟿© {OR t₄ t₅} {OR .t₅ .t₄} ⟿-OR-sym = ⟿©-OR-sym
-- -- ⟿-⟿© {OR t₄ .(OR _ t₇)} {OR .(OR t₄ _) t₇} ⟿-OR-assoc = ⟿©-OR-assoc
-- -- ⟿-⟿© {OR t₄ t₅} {OR t₆ .t₅} (⟿-OR₁ p) = ⟿©-OR₁ (⟿-⟿© p)
-- -- ⟿-⟿© {OR t₄ t₅} {OR .t₄ t₇} (⟿-OR₂ p) = ⟿©-OR₂ (⟿-⟿© p)
-- -- ⟿-⟿© {OR t₄ t₅} {SAND t₆ t₇} ()
-- -- ⟿-⟿© {SAND t₄ t₅} {NODE b} ()
-- -- ⟿-⟿© {SAND t₄ t₅} {AND t₆ t₇} ()
-- -- ⟿-⟿© {SAND t₄ .(OR _ _)} {OR .(SAND t₄ _) .(SAND t₄ _)} ⟿-SAND-distl = ⟿©-SAND-distl
-- -- ⟿-⟿© {SAND .(OR _ _) t₅} {OR .(SAND _ t₅) .(SAND _ t₅)} ⟿-SAND-distr = ⟿©-SAND-distr
-- -- ⟿-⟿© {SAND t₄ .(SAND _ t₇)} {SAND .(SAND t₄ _) t₇} ⟿-SAND-assoc = ⟿©-SAND-assoc
-- -- ⟿-⟿© {SAND t₄ t₅} {SAND t₆ .t₅} (⟿-SAND₁ p) = ⟿©-SAND₁ (⟿-⟿© p)
-- -- ⟿-⟿© {SAND t₄ t₅} {SAND .t₄ t₇} (⟿-SAND₂ p) = ⟿©-SAND₂ (⟿-⟿© p)

-- -- ⟿*-⟿©* : ∀{t₁ t₂} → t₁ ⟿* t₂ → t₁ ⟿©* t₂
-- -- ⟿*-⟿©* (⟿-step x) = ⟿©-step (⟿-⟿© x)
-- -- ⟿*-⟿©* ⟿-refl = ⟿©-refl
-- -- ⟿*-⟿©* (⟿-trans p₁ p₂) = ⟿©-trans (⟿*-⟿©* p₁) (⟿*-⟿©* p₂)

-- -- ≃ⱼ-refl : ∀{t} → t ≃ⱼ t
-- -- ≃ⱼ-refl {t} = t , (t , (⟿©-refl , (⟿©-refl , (t , (⟿-refl , ⟿-refl)))))

-- -- ≃ⱼ-sym : ∀{t₁ t₂} → t₁ ≃ⱼ t₂ → t₂ ≃ⱼ t₁
-- -- ≃ⱼ-sym {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , s₃ , p₄ , p₅) = s₂ , (s₁ , (p₂ , (p₁ , (s₃ , (p₅ , p₄)))))

-- -- ≃ⱼ-trans : ∀{t₁ t₂ t₃} → t₁ ≃ⱼ t₂ → t₂ ≃ⱼ t₃ → t₁ ≃ⱼ t₃
-- -- ≃ⱼ-trans {t₁}{t₂}{t₃} (s₁ , s₂ , p₁ , p₂ , s₃ , p₄ , p₅) (s₄ , s₅ , p₆ , p₇ , s₆ , p₈ , p₉) with CR-⟿© p₂ p₆
-- -- ... | (s₁' , r₁ , r₂) with CR-⟿© (⟿*-⟿©* p₅) r₁
-- -- ... | (s₂' , r₃ , r₄) with CR-⟿© r₂ (⟿*-⟿©* p₈)
-- -- ... | (s₃' , r₅ , r₆) with CR-⟿© r₄ r₅
-- -- ... | (s₄' , r₇ , r₈) = s₄' , (s₄' , (⟿©-trans p₁ (⟿©-trans (⟿*-⟿©* p₄) (⟿©-trans r₃ r₇)) , (⟿©-trans p₇ (⟿©-trans (⟿*-⟿©* p₉) (⟿©-trans r₆ r₈)) , (s₄' , (⟿-refl , ⟿-refl)))))

-- -- ≈-≈© : ∀{t₁ t₂} → t₁ ≈ t₂ → t₁ ≈© t₂
-- -- ≈-≈© (≈-reduce x) = ≈©-reduce (⟿-⟿© x)
-- -- ≈-≈© ≈-refl = ≈©-refl
-- -- ≈-≈© (≈-sym p) = ≈©-sym (≈-≈© p)
-- -- ≈-≈© (≈-trans p₁ p₂) = ≈©-trans (≈-≈© p₁) (≈-≈© p₂)

-- -- ⟿*-≈ : ∀{t₁ t₂} → t₁ ⟿* t₂ → t₁ ≈ t₂
-- -- ⟿*-≈ (⟿-step x) = ≈-reduce x
-- -- ⟿*-≈ ⟿-refl = ≈-refl
-- -- ⟿*-≈ (⟿-trans p₁ p₂) with ⟿*-≈ p₁ | ⟿*-≈ p₂
-- -- ... | r₁ | r₂ = ≈-trans r₁ r₂

-- -- ⟱-≈ : ∀{t₁ t₂} → t₁ ⟱ t₂ → t₁ ≈ t₂
-- -- ⟱-≈ {t₁}{t₂} (s , p₁ , p₂) with ⟿*-≈ p₁ | ⟿*-≈ p₂
-- -- ... | r₁ | r₂ = ≈-trans r₁ (≈-sym r₂)

-- -- ≃ⱼ-≃ : ∀{t₁ t₂} → t₁ ≃ⱼ t₂ → t₁ ≃ t₂
-- -- ≃ⱼ-≃ {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , p₃) = s₁ , (s₂ , (p₁ , (p₂ , ⟱-≈ p₃)))

-- -- ≈-⟱ : ∀{t₁ t₂} → t₁ ≈ t₂ → t₁ ⟱ t₂
-- -- ≈-⟱ {t₁} {t₂} (≈-reduce x) = t₂ , ((⟿-step x) , ⟿-refl)
-- -- ≈-⟱ {t₁} {.t₁} ≈-refl = t₁ , (⟿-refl , ⟿-refl)
-- -- ≈-⟱ {t₁} {t₂} (≈-sym p) with ≈-⟱ p
-- -- ... | (s , p₁ , p₂) = s , (p₂ , p₁)
-- -- ≈-⟱ {t₁} {t₂} (≈-trans p₁ p₂) with ≈-⟱ p₁ | ≈-⟱ p₂
-- -- ... | r₁ | r₂ = ⟱-trans r₁ r₂

-- -- ≃-≃ⱼ : ∀{t₁ t₂} → t₁ ≃ t₂ → t₁ ≃ⱼ t₂
-- -- ≃-≃ⱼ {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , p₃) = s₁ , (s₂ , (p₁ , (p₂ , ≈-⟱ p₃)))

-- -- ≃-refl : ∀{t} → t ≃ t
-- -- ≃-refl {t} = ≃ⱼ-≃ (≃ⱼ-refl {t})

-- -- ≃-sym : ∀{t₁ t₂} → t₁ ≃ t₂ → t₂ ≃ t₁
-- -- ≃-sym p = ≃ⱼ-≃ (≃ⱼ-sym (≃-≃ⱼ p))

-- -- ≃-trans : ∀{t₁ t₂ t₃} → t₁ ≃ t₂ → t₂ ≃ t₃ → t₁ ≃ t₃
-- -- ≃-trans p₁ p₂ = ≃ⱼ-≃ (≃ⱼ-trans (≃-≃ⱼ p₁) (≃-≃ⱼ p₂))

-- -- ≈©-≃ : ∀{t₁ t₂} → t₁ ≈© t₂ → t₁ ≃ t₂
-- -- ≈©-≃ {t₁} {t₂} (≈©-reduce x) = t₂ , (t₂ , ((⟿©-step x) , (⟿©-refl , ≈-refl)))
-- -- ≈©-≃ {t₁} {.t₁} ≈©-refl = ≃-refl
-- -- ≈©-≃ {t₁} {t₂} (≈©-sym p) = ≃-sym (≈©-≃ p)
-- -- ≈©-≃ {t₁} {t₂} (≈©-trans p₁ p₂) = ≃-trans (≈©-≃ p₁) (≈©-≃ p₂)

-- -- ≈©-≃-inv : ∀{t₁ t₂} → t₁ ≃ t₂ → t₁ ≈© t₂
-- -- ≈©-≃-inv {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , p₃) = ≈©-trans (⟿©*-≈© p₁) (≈©-trans (≈-≈© p₃) (≈©-sym (⟿©*-≈© p₂)))

-- -- open import nat

-- -- ∣_∣ : ATree → nat
-- -- ∣ NODE b ∣ = 1
-- -- ∣ AND t₁ t₂ ∣ = 2 * (∣ t₁ ∣ * ∣ t₂ ∣)
-- -- ∣ OR t₁ t₂ ∣ = 2 + (∣ t₁ ∣ + ∣ t₂ ∣)
-- -- ∣ SAND t₁ t₂ ∣ = 2 * (∣ t₁ ∣ * ∣ t₂ ∣)

-- -- at₁ : ∀(b : 𝔹) → bool
-- -- at₁ b = ∣ SAND (OR (NODE b) (NODE b)) (NODE b) ∣ > ∣ (OR (SAND (NODE b) (NODE b)) (SAND (NODE b) (NODE b))) ∣
