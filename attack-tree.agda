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

⟿-decreasing : ∀{t₁ t₂} → t₁ ⟿ t₂ → W t₁ > W t₂ ≡ tt
⟿-decreasing {t₁}{t₂} p = {!!}

-- --------------------------------------------------------------------------------------------
-- --                                                                                        --
-- -- Confluence of ⟿                                                                       --
-- --                                                                                        --
-- --------------------------------------------------------------------------------------------

isNorm : ATree → Set
isNorm (NODE b) = ⊤
isNorm (AND _ (AND _ _)) = ⊥
isNorm (AND _ (OR _ _)) = ⊥
isNorm (AND A B) = isNorm A × isNorm B
isNorm (OR A B) with A ≅ B
isNorm (OR _ _) | inj₁ _ = ⊥
isNorm (OR _ (OR _ _)) | inj₂ _ = ⊥
isNorm (OR A B) | inj₂ _ = isNorm A × isNorm B
isNorm (SAND _ (OR _ _)) = ⊥
isNorm (SAND _ (SAND _ _)) = ⊥
isNorm (SAND A B) = isNorm A × isNorm B

unique-normf : ∀{A N₁ N₂} → isNorm N₁ → isNorm N₂ → A ⟿ N₁ → A ⟿ N₂ → N₁ ≡ N₂
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(OR (AND (AND _ _) _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₁ x) (⟿-AND-distl-assoc₁ x₁) = refl
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND _ (AND _ _)))} {.(OR (AND _ (AND _ _)) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₁ ()) (⟿-AND-distl-assoc₂ x₁)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND _ (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₁ ()) ⟿-AND-distl-assoc₃
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(OR (AND _ (AND _ _)) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₁ x) (⟿-AND-distl () x₂)
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(AND _ (OR (AND _ _) _))} n-pf₁ () (⟿-AND-distl-assoc₁ x) (⟿-AND₁ d₂)
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₁ x) (⟿-AND₂-assoc ())
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl-assoc₁ x) (⟿-AND₂ (⟿-OR₁ d₂) x₁)
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(AND _ (OR (AND _ _) _))} n-pf₁ () (⟿-AND-distl-assoc₁ x) (⟿-AND₂ (⟿-OR₂-assoc-contract d₂) x₁)
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(AND _ (OR (OR (AND _ _) _) _))} n-pf₁ () (⟿-AND-distl-assoc₁ x) (⟿-AND₂ (⟿-OR₂-assoc d₂ x₁) x₂)
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} {.(AND _ (OR (AND _ _) _))} n-pf₁ () (⟿-AND-distl-assoc₁ x) (⟿-AND₂ (⟿-OR₂ d₂ x₁) x₂)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND _ (AND _ _)) (AND (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ (AND _ _)))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₂ ()) (⟿-AND-distl-assoc₁ x₁)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(OR (AND _ _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₂ x) (⟿-AND-distl-assoc₂ x₁) = refl
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND _ (AND _ _)) (AND (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₂ ()) ⟿-AND-distl-assoc₃
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(OR (AND _ _) (AND _ (AND _ _)))} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₂ x) (⟿-AND-distl x₁ ())
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(AND _ (OR _ (AND _ _)))} n-pf₁ () (⟿-AND-distl-assoc₂ x) (⟿-AND₁ d₂)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ (⟿-AND-distl-assoc₂ x) (⟿-AND₂-assoc ())
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(AND _ (OR _ (AND _ _)))} n-pf₁ () (⟿-AND-distl-assoc₂ x) (⟿-AND₂ (⟿-OR₁ d₂) x₁)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl-assoc₂ x) (⟿-AND₂ (⟿-OR₂-assoc-contract d₂) x₁)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(AND _ (OR (OR _ _) _))} n-pf₁ () (⟿-AND-distl-assoc₂ x) (⟿-AND₂ (⟿-OR₂-assoc d₂ x₁) x₂)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl-assoc₂ x) (⟿-AND₂ (⟿-OR₂ d₂ x₁) x₂)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ (AND _ _)))} n-pf₁ n-pf₂ ⟿-AND-distl-assoc₃ (⟿-AND-distl-assoc₁ ())
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(OR (AND _ (AND _ _)) (AND (AND _ _) _))} n-pf₁ n-pf₂ ⟿-AND-distl-assoc₃ (⟿-AND-distl-assoc₂ ())
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} n-pf₁ n-pf₂ ⟿-AND-distl-assoc₃ ⟿-AND-distl-assoc₃ = refl
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(OR (AND _ (AND _ _)) (AND _ (AND _ _)))} n-pf₁ n-pf₂ ⟿-AND-distl-assoc₃ (⟿-AND-distl () x₁)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND _ (OR (AND _ _) (AND _ _)))} n-pf₁ () ⟿-AND-distl-assoc₃ (⟿-AND₁ d₂)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ ⟿-AND-distl-assoc₃ (⟿-AND₂-assoc ())
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND _ (OR _ (AND _ _)))} n-pf₁ () ⟿-AND-distl-assoc₃ (⟿-AND₂ (⟿-OR₁ d₂) x)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND _ (OR (AND _ _) _))} n-pf₁ () ⟿-AND-distl-assoc₃ (⟿-AND₂ (⟿-OR₂-assoc-contract d₂) x)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND _ (OR (OR (AND _ _) _) _))} n-pf₁ () ⟿-AND-distl-assoc₃ (⟿-AND₂ (⟿-OR₂-assoc d₂ x) x₁)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND _ (OR (AND _ _) _))} n-pf₁ () ⟿-AND-distl-assoc₃ (⟿-AND₂ (⟿-OR₂ d₂ x) x₁)
unique-normf {.(AND _ (OR (AND _ _) _))} {.(OR (AND _ (AND _ _)) (AND _ _))} {.(OR (AND (AND _ _) _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND-distl () x₁) (⟿-AND-distl-assoc₁ x₂)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND-distl x ()) (⟿-AND-distl-assoc₂ x₂)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND _ (AND _ _)) (AND _ (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND-distl () x₁) ⟿-AND-distl-assoc₃
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(OR (AND _ _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND-distl x x₁) (⟿-AND-distl x₂ x₃) = refl
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl x x₁) (⟿-AND₁ d₂)
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ (⟿-AND-distl x x₁) (⟿-AND₂-assoc ())
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl x x₁) (⟿-AND₂ (⟿-OR₁ d₂) x₂)
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl x x₁) (⟿-AND₂ (⟿-OR₂-assoc-contract d₂) x₂)
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ (OR (OR _ _) _))} n-pf₁ () (⟿-AND-distl x x₁) (⟿-AND₂ (⟿-OR₂-assoc d₂ x₂) x₃)
unique-normf {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ (OR _ _))} n-pf₁ () (⟿-AND-distl x x₁) (⟿-AND₂ (⟿-OR₂ d₂ x₂) x₃)
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₁ x) (⟿-SAND-distl-assoc₁ x₁) = refl
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND _ (SAND _ _)))} {.(OR (SAND _ (SAND _ _)) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₁ ()) (⟿-SAND-distl-assoc₂ x₁)
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND _ (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₁ ()) ⟿-SAND-distl-assoc₃
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} {.(OR (SAND _ (SAND _ _)) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₁ x) (⟿-SAND-distl () x₂)
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} {.(SAND _ (OR (SAND _ _) _))} n-pf₁ () (⟿-SAND-distl-assoc₁ x) (⟿-SAND₁ d₂)
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₁ x) (⟿-SAND₂-assoc ())
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₁ x) (⟿-SAND₂ d₂ x₁) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND _ (SAND _ _)) (SAND (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ (SAND _ _)))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₂ ()) (⟿-SAND-distl-assoc₁ x₁)
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₂ x) (⟿-SAND-distl-assoc₂ x₁) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND _ (SAND _ _)) (SAND (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₂ ()) ⟿-SAND-distl-assoc₃
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} {.(OR (SAND _ _) (SAND _ (SAND _ _)))} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₂ x) (⟿-SAND-distl x₁ ())
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} {.(SAND _ (OR _ (SAND _ _)))} n-pf₁ () (⟿-SAND-distl-assoc₂ x) (⟿-SAND₁ d₂)
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₂ x) (⟿-SAND₂-assoc d₂) = {!!}
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND-distl-assoc₂ x) (⟿-SAND₂ d₂ x₁) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ (SAND _ _)))} n-pf₁ n-pf₂ ⟿-SAND-distl-assoc₃ (⟿-SAND-distl-assoc₁ ())
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(OR (SAND _ (SAND _ _)) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ ⟿-SAND-distl-assoc₃ (⟿-SAND-distl-assoc₂ ())
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ ⟿-SAND-distl-assoc₃ ⟿-SAND-distl-assoc₃ = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(OR (SAND _ (SAND _ _)) (SAND _ (SAND _ _)))} n-pf₁ n-pf₂ ⟿-SAND-distl-assoc₃ (⟿-SAND-distl () x₁)
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(SAND _ (OR (SAND _ _) (SAND _ _)))} n-pf₁ () ⟿-SAND-distl-assoc₃ (⟿-SAND₁ d₂)
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ ⟿-SAND-distl-assoc₃ (⟿-SAND₂-assoc d₂) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(SAND _ _)} n-pf₁ n-pf₂ ⟿-SAND-distl-assoc₃ (⟿-SAND₂ d₂ x) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND _ (SAND _ _)) (SAND _ _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND-distl () x₁) (⟿-SAND-distl-assoc₁ x₂)
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND-distl x ()) (⟿-SAND-distl-assoc₂ x₂)
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND _ (SAND _ _)) (SAND _ (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND-distl () x₁) ⟿-SAND-distl-assoc₃
unique-normf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(OR (SAND _ _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND-distl x x₁) (⟿-SAND-distl x₂ x₃) = {!!}
unique-normf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ (OR _ _))} n-pf₁ () (⟿-SAND-distl x x₁) (⟿-SAND₁ d₂)
unique-normf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ (⟿-SAND-distl x x₁) (⟿-SAND₂-assoc d₂) = {!!}
unique-normf {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND-distl x x₁) (⟿-SAND₂ d₂ x₂) = {!!}
unique-normf {.(AND _ (OR (AND _ _) _))} {.(AND _ (OR (AND _ _) _))} {.(OR (AND (AND _ _) _) (AND _ _))} () n-pf₂ (⟿-AND₁ d₁) (⟿-AND-distl-assoc₁ x)
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(AND _ (OR _ (AND _ _)))} {.(OR (AND _ _) (AND (AND _ _) _))} () n-pf₂ (⟿-AND₁ d₁) (⟿-AND-distl-assoc₂ x)
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(AND _ (OR (AND _ _) (AND _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} () n-pf₂ (⟿-AND₁ d₁) ⟿-AND-distl-assoc₃
unique-normf {.(AND _ (OR _ _))} {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} () n-pf₂ (⟿-AND₁ d₁) (⟿-AND-distl x x₁)
unique-normf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} n-pf₁ n-pf₂ (⟿-AND₁ d₁) (⟿-AND₁ d₂) = {!!}
unique-normf {.(AND _ _)} {.(AND _ _)} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ (⟿-AND₁ d₁) (⟿-AND₂-assoc d₂) = {!!}
unique-normf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} n-pf₁ n-pf₂ (⟿-AND₁ d₁) (⟿-AND₂ d₂ x) = {!!}
unique-normf {.(AND _ (OR (AND _ _) _))} {.(AND (AND _ _) _)} {.(OR (AND (AND _ _) _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) (⟿-AND-distl-assoc₁ x) = {!!}
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(AND (AND _ _) _)} {.(OR (AND _ _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) (⟿-AND-distl-assoc₂ x) = {!!}
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(AND (AND _ _) _)} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) ⟿-AND-distl-assoc₃ = {!!}
unique-normf {.(AND _ (OR _ _))} {.(AND (AND _ _) _)} {.(OR (AND _ _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) (⟿-AND-distl x x₁) = {!!}
unique-normf {.(AND _ _)} {.(AND (AND _ _) _)} {.(AND _ _)} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) (⟿-AND₁ d₂) = {!!}
unique-normf {.(AND _ _)} {.(AND (AND _ _) _)} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) (⟿-AND₂-assoc d₂) = {!!}
unique-normf {.(AND _ _)} {.(AND (AND _ _) _)} {.(AND _ _)} n-pf₁ n-pf₂ (⟿-AND₂-assoc d₁) (⟿-AND₂ d₂ x) = {!!}
unique-normf {.(AND _ (OR (AND _ _) _))} {.(AND _ _)} {.(OR (AND (AND _ _) _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) (⟿-AND-distl-assoc₁ x₁) = {!!}
unique-normf {.(AND _ (OR _ (AND _ _)))} {.(AND _ _)} {.(OR (AND _ _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) (⟿-AND-distl-assoc₂ x₁) = {!!}
unique-normf {.(AND _ (OR (AND _ _) (AND _ _)))} {.(AND _ _)} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) ⟿-AND-distl-assoc₃ = {!!}
unique-normf {.(AND _ (OR _ _))} {.(AND _ _)} {.(OR (AND _ _) (AND _ _))} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) (⟿-AND-distl x₁ x₂) = {!!}
unique-normf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) (⟿-AND₁ d₂) = {!!}
unique-normf {.(AND _ _)} {.(AND _ _)} {.(AND (AND _ _) _)} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) (⟿-AND₂-assoc d₂) = {!!}
unique-normf {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} n-pf₁ n-pf₂ (⟿-AND₂ d₁ x) (⟿-AND₂ d₂ x₁) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₁ d₁) (⟿-OR₁ d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₁ d₁) (⟿-OR₂-assoc-contract d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR (OR _ _) _)} n-pf₁ n-pf₂ (⟿-OR₁ d₁) (⟿-OR₂-assoc d₂ x) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₁ d₁) (⟿-OR₂ d₂ x) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc-contract d₁) (⟿-OR₁ d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc-contract d₁) (⟿-OR₂-assoc-contract d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR (OR _ _) _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc-contract d₁) (⟿-OR₂-assoc d₂ x) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc-contract d₁) (⟿-OR₂ d₂ x) = {!!}
unique-normf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc d₁ x) (⟿-OR₁ d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc d₁ x) (⟿-OR₂-assoc-contract d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR (OR _ _) _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc d₁ x) (⟿-OR₂-assoc d₂ x₁) = {!!}
unique-normf {.(OR _ _)} {.(OR (OR _ _) _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂-assoc d₁ x) (⟿-OR₂ d₂ x₁) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂ d₁ x) (⟿-OR₁ d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂ d₁ x) (⟿-OR₂-assoc-contract d₂) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR (OR _ _) _)} n-pf₁ n-pf₂ (⟿-OR₂ d₁ x) (⟿-OR₂-assoc d₂ x₁) = {!!}
unique-normf {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} n-pf₁ n-pf₂ (⟿-OR₂ d₁ x) (⟿-OR₂ d₂ x₁) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(SAND _ (OR (SAND _ _) _))} {.(OR (SAND (SAND _ _) _) (SAND _ _))} () n-pf₂ (⟿-SAND₁ d₁) (⟿-SAND-distl-assoc₁ x)
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(SAND _ (OR _ (SAND _ _)))} {.(OR (SAND _ _) (SAND (SAND _ _) _))} () n-pf₂ (⟿-SAND₁ d₁) (⟿-SAND-distl-assoc₂ x)
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} () n-pf₂ (⟿-SAND₁ d₁) ⟿-SAND-distl-assoc₃
unique-normf {.(SAND _ (OR _ _))} {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} () n-pf₂ (⟿-SAND₁ d₁) (⟿-SAND-distl x x₁)
unique-normf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND₁ d₁) (⟿-SAND₁ d₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND _ _)} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ (⟿-SAND₁ d₁) (⟿-SAND₂-assoc d₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND₁ d₁) (⟿-SAND₂ d₂ x) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(SAND (SAND _ _) _)} {.(OR (SAND (SAND _ _) _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) (⟿-SAND-distl-assoc₁ x) = {!!}
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(SAND (SAND _ _) _)} {.(OR (SAND _ _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) (⟿-SAND-distl-assoc₂ x) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(SAND (SAND _ _) _)} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) ⟿-SAND-distl-assoc₃ = {!!}
unique-normf {.(SAND _ (OR _ _))} {.(SAND (SAND _ _) _)} {.(OR (SAND _ _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) (⟿-SAND-distl x x₁) = {!!}
unique-normf {.(SAND _ _)} {.(SAND (SAND _ _) _)} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) (⟿-SAND₁ d₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND (SAND _ _) _)} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) (⟿-SAND₂-assoc d₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND (SAND _ _) _)} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND₂-assoc d₁) (⟿-SAND₂ d₂ x) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) _))} {.(SAND _ _)} {.(OR (SAND (SAND _ _) _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) (⟿-SAND-distl-assoc₁ x₁) = {!!}
unique-normf {.(SAND _ (OR _ (SAND _ _)))} {.(SAND _ _)} {.(OR (SAND _ _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) (⟿-SAND-distl-assoc₂ x₁) = {!!}
unique-normf {.(SAND _ (OR (SAND _ _) (SAND _ _)))} {.(SAND _ _)} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) ⟿-SAND-distl-assoc₃ = {!!}
unique-normf {.(SAND _ (OR _ _))} {.(SAND _ _)} {.(OR (SAND _ _) (SAND _ _))} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) (⟿-SAND-distl x₁ x₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) (⟿-SAND₁ d₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND _ _)} {.(SAND (SAND _ _) _)} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) (⟿-SAND₂-assoc d₂) = {!!}
unique-normf {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} n-pf₁ n-pf₂ (⟿-SAND₂ d₁ x) (⟿-SAND₂ d₂ x₁) = {!!}
