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

notCT : ATree → Set
notCT (OR A B) with A ≅ B
... | inj₁ _ = ⊥
... | inj₂ _ = ⊤
notCT _ = ⊤

CP : (A : ATree) → Σ[ B ∈ ATree ](A ≡ OR B B) ⊎ (Σ[ B ∈ ATree ](A ≡ OR B B) → ⊥ {lzero})
CP (OR A B) with A ≅ B
... | inj₁ refl = inj₁ (A , refl)
... | inj₂ p = inj₂ aux
 where
   aux : Σ ATree (λ B₁ → OR A B ≡ OR B₁ B₁) → ⊥ {lzero}
   aux (B , refl) = p refl
CP (NODE b) = inj₂ aux
 where
   aux : Σ-syntax ATree (λ B → NODE b ≡ OR B B) → ⊥ {lzero}
   aux (_ , ())
CP (AND A B) = inj₂ aux
 where
  aux : Σ-syntax ATree (λ B₁ → AND A B ≡ OR B₁ B₁) → ⊥ {lzero}
  aux (_ , ())
CP (SAND A B) = inj₂ aux
 where
  aux : Σ-syntax ATree (λ B₁ → SAND A B ≡ OR B₁ B₁) → ⊥ {lzero}
  aux (_ , ())

data _⟿_ : ATree → ATree → Set where
  ⟿-OR-assoc : ∀{A B C} → OR (OR A B) C ⟿ OR A (OR B C)
  ⟿-AND-assoc : ∀{A B C} → AND (AND A B) C ⟿ AND A (AND B C)
  ⟿-SAND-assoc : ∀{A B C} → SAND (SAND A B) C ⟿ SAND A (SAND B C)  

  ⟿-AND-dist : ∀{A B C : ATree} → (AND A (OR B C)) ⟿ (OR (AND A B) (AND A C))
  ⟿-SAND-dist : ∀{A B C : ATree} → (SAND A (OR B C)) ⟿ (OR (SAND A B) (SAND A C))

  ⟿-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (AND A₁ B) ⟿ (AND A₂ B)
  ⟿-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (AND A B₁) ⟿ (AND A B₂)

  ⟿-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (OR A₁ B) ⟿ (OR A₂ B)
  ⟿-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (OR A B₁) ⟿ (OR A B₂)

  ⟿-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (SAND A₁ B) ⟿ (SAND A₂ B)
  ⟿-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (SAND A B₁) ⟿ (SAND A B₂)

-- Equations:
postulate OR-sym : ∀{A B} → (OR A B) ≡ (OR B A)
postulate AND-sym : ∀{A B} → (AND A B) ≡ (AND B A)
postulate SAND-sym : ∀{A B} → (SAND A B) ≡ (SAND B A)

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

⟿*-AND₁ : ∀{A A' B} → A ⟿* A' → AND A B ⟿* AND A' B
⟿*-AND₁ {A} {A'} {B} (⟿-step d) = ⟿-step (⟿-AND₁ d)
⟿*-AND₁ {A} {.A} {B} ⟿-refl = ⟿-refl
⟿*-AND₁ {A} {A'} {B} (⟿-trans d₁ d₂) = ⟿-trans (⟿*-AND₁ d₁) (⟿*-AND₁ d₂)

⟿*-AND₂ : ∀{A B B'} → B ⟿* B' → AND A B ⟿* AND A B'
⟿*-AND₂ {A} {B} {B'} (⟿-step d) = ⟿-step (⟿-AND₂ d)
⟿*-AND₂ {A} {B} {.B} ⟿-refl = ⟿-refl
⟿*-AND₂ {A} {B} {B'} (⟿-trans d₁ d₂) = ⟿-trans (⟿*-AND₂ d₁) (⟿*-AND₂ d₂)

⟿*-OR₁ : ∀{A A' B} → A ⟿* A' → OR A B ⟿* OR A' B
⟿*-OR₁ {A} {A'} {B} (⟿-step d) = ⟿-step (⟿-OR₁ d)
⟿*-OR₁ {A} {.A} {B} ⟿-refl = ⟿-refl
⟿*-OR₁ {A} {A'} {B} (⟿-trans d₁ d₂) = ⟿-trans (⟿*-OR₁ d₁) (⟿*-OR₁ d₂)

⟿*-OR₂ : ∀{A B B'} → B ⟿* B' → OR A B ⟿* OR A B'
⟿*-OR₂ {A} {B} {B'} (⟿-step d) = ⟿-step (⟿-OR₂ d)
⟿*-OR₂ {A} {B} {.B} ⟿-refl = ⟿-refl
⟿*-OR₂ {A} {B} {B'} (⟿-trans d₁ d₂) = ⟿-trans (⟿*-OR₂ d₁) (⟿*-OR₂ d₂)


--------------------------------------------------------------------------------------------
--                                                                                        --
-- Termination of ⟿                                                                      --
--                                                                                        --
--------------------------------------------------------------------------------------------

data ATSig : Set where
  node : ATSig
  and : ATSig
  sand : ATSig
  or : ATSig

∣_∣ : ATree → ATSig
∣ NODE b ∣ = node
∣ AND A A₁ ∣ = and
∣ OR A A₁ ∣ = or
∣ SAND A A₁ ∣ = sand

_>AS_ : ATSig → ATSig → Set
x >AS node = ⊤
and >AS or = ⊤
sand >AS or = ⊤
s >AS t = ⊥

isNODE : ATree → Set
isNODE (NODE b) = ⊤
isNODE _ = ⊥

notNODE : ATree → Set
notNODE (NODE _) = ⊥
notNODE _ = ⊤

fstAT : (A : ATree) → notNODE A → ATree
fstAT (NODE b) ()
fstAT (AND A _) _ = A
fstAT (OR A _) _ = A
fstAT (SAND A _) _ = A

sndAT : (A : ATree) → notNODE A → ATree
sndAT (NODE b) ()
sndAT (AND _ B) p = B
sndAT (OR _ B) p = B
sndAT (SAND _ B) p = B

data _>lpo_ (s : ATree) (t : ATree) : Set where
  lpo1 : isNODE t → notNODE s → s >lpo t
  lpo2a : (p₁ : notNODE s) → (p₂ : notNODE t) → (((fstAT s p₁) ≡ t) ⊎ (fstAT s p₁) >lpo t) ⊎ ((sndAT s p₁) ≡ t) ⊎ ((sndAT s p₁) >lpo t) → s >lpo t
  lpo2b : (p₁ : notNODE s) → (p₂ : notNODE t) → ∣ s ∣ >AS ∣ t ∣ → s >lpo (fstAT t p₂) → s >lpo (sndAT t p₂) → s >lpo t
  lpo2c : (p₁ : notNODE s) → (p₂ : notNODE t) → ∣ s ∣ ≡ ∣ t ∣ → s >lpo (fstAT t p₂) → s >lpo (sndAT t p₂) → (fstAT s p₁) >lpo (fstAT t p₂) ⊎ (((fstAT s p₁) ≡ (fstAT t p₂)) × (sndAT s p₁) >lpo (sndAT t p₂)) → s >lpo t

>lpo-OR₁ : ∀{A B} → (OR A B) >lpo A
>lpo-OR₁ {NODE b} {B₁} = lpo1 triv triv
>lpo-OR₁ {AND A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))
>lpo-OR₁ {OR A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))
>lpo-OR₁ {SAND A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))

>lpo-OR₂ : ∀{A B} → (OR A B) >lpo B
>lpo-OR₂ {A} {NODE b} = lpo1 triv triv
>lpo-OR₂ {A} {AND B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))
>lpo-OR₂ {A} {OR B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))
>lpo-OR₂ {A} {SAND B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))

>lpo-AND₁ : ∀{A B} → (AND A B) >lpo A
>lpo-AND₁ {NODE b} {B₁} = lpo1 triv triv
>lpo-AND₁ {AND A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))
>lpo-AND₁ {OR A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))
>lpo-AND₁ {SAND A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))

>lpo-AND₂ : ∀{A B} → (AND A B) >lpo B
>lpo-AND₂ {A} {NODE b} = lpo1 triv triv
>lpo-AND₂ {A} {AND B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))
>lpo-AND₂ {A} {OR B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))
>lpo-AND₂ {A} {SAND B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))

>lpo-SAND₁ : ∀{A B} → (SAND A B) >lpo A
>lpo-SAND₁ {NODE b} {B₁} = lpo1 triv triv
>lpo-SAND₁ {AND A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))
>lpo-SAND₁ {OR A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))
>lpo-SAND₁ {SAND A₁ A₂} {B₁} = lpo2a triv triv (inj₁ (inj₁ refl))

>lpo-SAND₂ : ∀{A B} → (SAND A B) >lpo B
>lpo-SAND₂ {A} {NODE b} = lpo1 triv triv
>lpo-SAND₂ {A} {AND B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))
>lpo-SAND₂ {A} {OR B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))
>lpo-SAND₂ {A} {SAND B B₁} = lpo2a triv triv (inj₂ (inj₁ refl))

>lpo-contract : ∀{A} → (OR A A) >lpo A
>lpo-contract = >lpo-OR₁

>lpo-OR-assoc : ∀{A B C} → (OR (OR A B) C) >lpo (OR A (OR B C))
>lpo-OR-assoc {A}{B}{C} = lpo2c triv triv refl aux₁ (lpo2c triv triv refl aux₂ aux₃ (inj₁ >lpo-OR₂)) (inj₁ >lpo-OR₁)
 where
  aux₁ : ∀{A B C} → OR (OR A B) C >lpo A
  aux₁ {NODE b} {B} {C} = lpo1 triv triv
  aux₁ {AND A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {OR A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {SAND A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))

  aux₂ : ∀{A B C} → OR (OR A B) C >lpo B
  aux₂ {A₁} {NODE b} {C₁} = lpo1 triv triv
  aux₂ {A₁} {AND B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))
  aux₂ {A₁} {OR B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))
  aux₂ {A₁} {SAND B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))

  aux₃ : ∀{A B C} → OR (OR A B) C >lpo C
  aux₃ {A₁} {B₁} {NODE b} = lpo1 triv triv
  aux₃ {A₁} {B₁} {AND C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))
  aux₃ {A₁} {B₁} {OR C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))
  aux₃ {A₁} {B₁} {SAND C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))

>lpo-AND-assoc : ∀{A B C} → (AND (AND A B) C) >lpo (AND A (AND B C))
>lpo-AND-assoc {A}{B}{C} = lpo2c triv triv refl aux₁ (lpo2c triv triv refl aux₂ aux₃ (inj₁ >lpo-AND₂)) (inj₁ >lpo-AND₁)
 where
  aux₁ : ∀{A B C} → AND (AND A B) C >lpo A
  aux₁ {NODE b} {B} {C} = lpo1 triv triv
  aux₁ {AND A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {OR A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {SAND A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))

  aux₂ : ∀{A B C} → AND (AND A B) C >lpo B
  aux₂ {A₁} {NODE b} {C₁} = lpo1 triv triv
  aux₂ {A₁} {AND B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))
  aux₂ {A₁} {OR B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))
  aux₂ {A₁} {SAND B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))

  aux₃ : ∀{A B C} → AND (AND A B) C >lpo C
  aux₃ {A₁} {B₁} {NODE b} = lpo1 triv triv
  aux₃ {A₁} {B₁} {AND C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))
  aux₃ {A₁} {B₁} {OR C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))
  aux₃ {A₁} {B₁} {SAND C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))

>lpo-SAND-assoc : ∀{A B C} → (SAND (SAND A B) C) >lpo (SAND A (SAND B C))
>lpo-SAND-assoc {A}{B}{C} = lpo2c triv triv refl aux₁ (lpo2c triv triv refl aux₂ aux₃ (inj₁ >lpo-SAND₂)) (inj₁ >lpo-SAND₁)
 where
  aux₁ : ∀{A B C} → SAND (SAND A B) C >lpo A
  aux₁ {NODE b} {B} {C} = lpo1 triv triv
  aux₁ {AND A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {OR A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {SAND A₁ A₂} {B} {C} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))

  aux₂ : ∀{A B C} → SAND (SAND A B) C >lpo B
  aux₂ {A₁} {NODE b} {C₁} = lpo1 triv triv
  aux₂ {A₁} {AND B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))
  aux₂ {A₁} {OR B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))
  aux₂ {A₁} {SAND B₁ B₂} {C₁} = lpo2a triv triv (inj₁ (inj₂ (lpo2a triv triv (inj₂ (inj₁ refl)))))

  aux₃ : ∀{A B C} → SAND (SAND A B) C >lpo C
  aux₃ {A₁} {B₁} {NODE b} = lpo1 triv triv
  aux₃ {A₁} {B₁} {AND C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))
  aux₃ {A₁} {B₁} {OR C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))
  aux₃ {A₁} {B₁} {SAND C₁ C₂} = lpo2a triv triv (inj₂ (inj₁ refl))

>lpo-AND-dist : ∀{A B C} → AND A (OR B C) >lpo OR (AND A B) (AND A C)
>lpo-AND-dist {A}{B}{C} = lpo2b triv triv triv (lpo2c triv triv refl >lpo-AND₁ aux₁ (inj₂ (refl , >lpo-OR₁))) (lpo2c triv triv refl >lpo-AND₁ aux₂ (inj₂ (refl , >lpo-OR₂)))
 where
  aux₁ : ∀{A B C} → AND A (OR B C) >lpo B
  aux₁ {A} {NODE b} {C} = lpo1 triv triv
  aux₁ {A} {AND B₁ B₂} {C} = lpo2a triv triv (inj₂ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {A} {OR B₁ B₂} {C} = lpo2a triv triv (inj₂ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {A} {SAND B₁ B₂} {C} = lpo2a triv triv (inj₂ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))

  aux₂ : ∀{A B C} → AND A (OR B C) >lpo C
  aux₂ {A} {B} {NODE _} = lpo1 triv triv
  aux₂ {A} {B} {AND C₁ C₂} = lpo2a triv triv (inj₂ (inj₂ >lpo-OR₂))
  aux₂ {A} {B} {OR C₁ C₂} = lpo2a triv triv (inj₂ (inj₂ >lpo-OR₂))
  aux₂ {A} {B} {SAND C₁ C₂} = lpo2a triv triv (inj₂ (inj₂ >lpo-OR₂))

>lpo-SAND-dist : ∀{A B C} → SAND A (OR B C) >lpo OR (SAND A B) (SAND A C)
>lpo-SAND-dist {A}{B}{C} = lpo2b triv triv triv (lpo2c triv triv refl >lpo-SAND₁ aux₁ (inj₂ (refl , >lpo-OR₁))) (lpo2c triv triv refl >lpo-SAND₁ aux₂ (inj₂ (refl , >lpo-OR₂)))
 where
  aux₁ : ∀{A B C} → SAND A (OR B C) >lpo B
  aux₁ {A} {NODE b} {C} = lpo1 triv triv
  aux₁ {A} {AND B₁ B₂} {C} = lpo2a triv triv (inj₂ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {A} {OR B₁ B₂} {C} = lpo2a triv triv (inj₂ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))
  aux₁ {A} {SAND B₁ B₂} {C} = lpo2a triv triv (inj₂ (inj₂ (lpo2a triv triv (inj₁ (inj₁ refl)))))

  aux₂ : ∀{A B C} → SAND A (OR B C) >lpo C
  aux₂ {A} {B} {NODE _} = lpo1 triv triv
  aux₂ {A} {B} {AND C₁ C₂} = lpo2a triv triv (inj₂ (inj₂ >lpo-OR₂))
  aux₂ {A} {B} {OR C₁ C₂} = lpo2a triv triv (inj₂ (inj₂ >lpo-OR₂))
  aux₂ {A} {B} {SAND C₁ C₂} = lpo2a triv triv (inj₂ (inj₂ >lpo-OR₂))
  
>lpo-OR₁-cong : ∀{A A' B} → A >lpo A' → (OR A B) >lpo (OR A' B)
>lpo-OR₁-cong {A} {NODE b} {B} p = lpo2c triv triv refl (lpo1 triv triv) >lpo-OR₂ (inj₁ p)
>lpo-OR₁-cong {A} {AND A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-OR₂ (inj₁ p)
>lpo-OR₁-cong {A} {OR A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-OR₂ (inj₁ p)
>lpo-OR₁-cong {A} {SAND A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-OR₂ (inj₁ p)

>lpo-OR₂-cong : ∀{A B B'} → B >lpo B' → (OR A B) >lpo (OR A B')
>lpo-OR₂-cong {A} {B} {NODE b} p = lpo2c triv triv refl >lpo-OR₁ (lpo1 triv triv) (inj₂ (refl , p))
>lpo-OR₂-cong {A} {B} {AND B' B''} p = lpo2c triv triv refl >lpo-OR₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))
>lpo-OR₂-cong {A} {B} {OR B' B''} p = lpo2c triv triv refl >lpo-OR₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))
>lpo-OR₂-cong {A} {B} {SAND B' B''} p = lpo2c triv triv refl >lpo-OR₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))

>lpo-AND₁-cong : ∀{A A' B} → A >lpo A' → (AND A B) >lpo (AND A' B)
>lpo-AND₁-cong {A} {NODE b} {B} p = lpo2c triv triv refl (lpo1 triv triv) >lpo-AND₂ (inj₁ p)
>lpo-AND₁-cong {A} {AND A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-AND₂ (inj₁ p)
>lpo-AND₁-cong {A} {OR A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-AND₂ (inj₁ p)
>lpo-AND₁-cong {A} {SAND A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-AND₂ (inj₁ p)

>lpo-AND₂-cong : ∀{A B B'} → B >lpo B' → (AND A B) >lpo (AND A B')
>lpo-AND₂-cong {A} {B} {NODE b} p = lpo2c triv triv refl >lpo-AND₁ (lpo1 triv triv) (inj₂ (refl , p))
>lpo-AND₂-cong {A} {B} {AND B' B''} p = lpo2c triv triv refl >lpo-AND₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))
>lpo-AND₂-cong {A} {B} {OR B' B''} p = lpo2c triv triv refl >lpo-AND₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))
>lpo-AND₂-cong {A} {B} {SAND B' B''} p = lpo2c triv triv refl >lpo-AND₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))

>lpo-SAND₁-cong : ∀{A A' B} → A >lpo A' → (SAND A B) >lpo (SAND A' B)
>lpo-SAND₁-cong {A} {NODE b} {B} p = lpo2c triv triv refl (lpo1 triv triv) >lpo-SAND₂ (inj₁ p)
>lpo-SAND₁-cong {A} {AND A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-SAND₂ (inj₁ p)
>lpo-SAND₁-cong {A} {OR A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-SAND₂ (inj₁ p)
>lpo-SAND₁-cong {A} {SAND A' A''} {B} p = lpo2c triv triv refl (lpo2a triv triv (inj₁ (inj₂ p))) >lpo-SAND₂ (inj₁ p)

>lpo-SAND₂-cong : ∀{A B B'} → B >lpo B' → (SAND A B) >lpo (SAND A B')
>lpo-SAND₂-cong {A} {B} {NODE b} p = lpo2c triv triv refl >lpo-SAND₁ (lpo1 triv triv) (inj₂ (refl , p))
>lpo-SAND₂-cong {A} {B} {AND B' B''} p = lpo2c triv triv refl >lpo-SAND₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))
>lpo-SAND₂-cong {A} {B} {OR B' B''} p = lpo2c triv triv refl >lpo-SAND₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))
>lpo-SAND₂-cong {A} {B} {SAND B' B''} p = lpo2c triv triv refl >lpo-SAND₁ (lpo2a triv triv (inj₂ (inj₂ p))) (inj₂ (refl , p))

-- The following implies termination.
⟿-decreasing : ∀{A B} → A ⟿ B → A >lpo B
⟿-decreasing {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} ⟿-AND-dist = >lpo-AND-dist
⟿-decreasing {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-dist = >lpo-SAND-dist
⟿-decreasing {.(AND _ _)} {.(AND _ _)} (⟿-AND₁ d) with ⟿-decreasing d
... | r = >lpo-AND₁-cong r
⟿-decreasing {.(AND _ _)} {.(AND _ _)} (⟿-AND₂ d) with ⟿-decreasing d
... | r = >lpo-AND₂-cong r
⟿-decreasing {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ d) with ⟿-decreasing d
... | r = >lpo-OR₁-cong r
⟿-decreasing {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ d) with ⟿-decreasing d
... | r = >lpo-OR₂-cong r
⟿-decreasing {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₁ d) with ⟿-decreasing d
... | r = >lpo-SAND₁-cong r
⟿-decreasing {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₂ d) with ⟿-decreasing d
... | r = >lpo-SAND₂-cong r
⟿-decreasing {.(OR (OR _ _) _)} {.(OR _ (OR _ _))} ⟿-OR-assoc = >lpo-OR-assoc
⟿-decreasing {.(AND (AND _ _) _)} {.(AND _ (AND _ _))} ⟿-AND-assoc = >lpo-AND-assoc
⟿-decreasing {.(SAND (SAND _ _) _)} {.(SAND _ (SAND _ _))} ⟿-SAND-assoc = >lpo-SAND-assoc

--------------------------------------------------------------------------------------------
--                                                                                        --
-- Confluence of ⟿                                                                       --
--                                                                                        --
--------------------------------------------------------------------------------------------

≠-AND₁ : ∀{A A' B C : ATree} → A ≠ A' → (AND A B) ≠ (AND A' C)
≠-AND₁ p refl = p refl

≠-AND₂ : ∀{A A' B C : ATree} → B ≠ C → (AND A B) ≠ (AND A' C)
≠-AND₂ p refl = p refl

≠-SAND₁ : ∀{A A' B C : ATree} → A ≠ A' → (SAND A B) ≠ (SAND A' C)
≠-SAND₁ p refl = p refl

≠-SAND₂ : ∀{A A' B C : ATree} → B ≠ C → (SAND A B) ≠ (SAND A' C)
≠-SAND₂ p refl = p refl

⟿-refl-⊥ : ∀{A} → A ⟿ A → ⊥ {lzero}
⟿-refl-⊥ {.(AND _ _)} (⟿-AND₁ d) = ⟿-refl-⊥ d
⟿-refl-⊥ {.(AND _ _)} (⟿-AND₂ d) = ⟿-refl-⊥ d
⟿-refl-⊥ {.(OR _ _)} (⟿-OR₁ d) = ⟿-refl-⊥ d
⟿-refl-⊥ {.(OR _ _)} (⟿-OR₂ d) = ⟿-refl-⊥ d
⟿-refl-⊥ {.(SAND _ _)} (⟿-SAND₁ d) = ⟿-refl-⊥ d
⟿-refl-⊥ {.(SAND _ _)} (⟿-SAND₂ d) = ⟿-refl-⊥ d

isNorm : ATree → Set
isNorm (NODE b) = ⊤
isNorm (AND (AND _ _) _) = ⊥
isNorm (AND _ (OR _ _)) = ⊥
isNorm (AND A B) = isNorm A × isNorm B
isNorm (OR (OR _ _) _) = ⊥
isNorm (OR A B) = isNorm A × isNorm B
isNorm (SAND _ (OR _ _)) = ⊥
isNorm (SAND (SAND _ _) _) = ⊥
isNorm (SAND A B) = isNorm A × isNorm B

isNorm-AND₁ : ∀{A B} → isNorm (AND A B) → isNorm A × isNorm B × notAND A × notOR B
isNorm-AND₁ {NODE b} {NODE b₁} nf-p = triv , (triv , (triv , triv))
isNorm-AND₁ {NODE b} {AND B B₁} nf-p = triv , ((snd nf-p) , (triv , triv))
isNorm-AND₁ {NODE b} {OR B B₁} ()
isNorm-AND₁ {NODE b} {SAND B B₁} nf-p = triv , ((snd nf-p) , (triv , triv))
isNorm-AND₁ {AND A A₁} {NODE b} ()
isNorm-AND₁ {AND A A₁} {AND B B₁} ()
isNorm-AND₁ {AND A A₁} {OR B B₁} ()
isNorm-AND₁ {AND A A₁} {SAND B B₁} ()
isNorm-AND₁ {OR A A₁} {NODE b} nf-p = (fst nf-p) , (triv , (triv , triv))
isNorm-AND₁ {OR A A₁} {AND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-AND₁ {OR A A₁} {OR B B₁} ()
isNorm-AND₁ {OR A A₁} {SAND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-AND₁ {SAND A A₁} {NODE b} nf-p = (fst nf-p) , (triv , (triv , triv))
isNorm-AND₁ {SAND A A₁} {AND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-AND₁ {SAND A A₁} {OR B B₁} ()
isNorm-AND₁ {SAND A A₁} {SAND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))

isNorm-AND₂ : ∀{A B} → isNorm A → isNorm B → notAND A → notOR B → isNorm (AND A B)
isNorm-AND₂ {NODE b} {NODE b₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = triv , triv
isNorm-AND₂ {NODE b} {AND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = triv , nf-p₂
isNorm-AND₂ {NODE b} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-AND₂ {NODE b} {SAND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = triv , nf-p₂
isNorm-AND₂ {AND A A₁} {NODE b} nf-p₁ nf-p₂ () n-p₂
isNorm-AND₂ {AND A A₁} {AND B B₁} nf-p₁ nf-p₂ () n-p₂
isNorm-AND₂ {AND A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-AND₂ {AND A A₁} {SAND B B₁} nf-p₁ nf-p₂ () n-p₂
isNorm-AND₂ {OR A A₁} {NODE b} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , triv
isNorm-AND₂ {OR A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-AND₂ {OR A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-AND₂ {OR A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-AND₂ {SAND A A₁} {NODE b} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , triv
isNorm-AND₂ {SAND A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-AND₂ {SAND A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-AND₂ {SAND A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂

isNorm-SAND₁ : ∀{A B} → isNorm (SAND A B) → isNorm A × isNorm B × notSAND A × notOR B
isNorm-SAND₁ {NODE b} {NODE b₁} nf-p = triv , (triv , (triv , triv))
isNorm-SAND₁ {NODE b} {AND B B₁} nf-p = triv , ((snd nf-p) , (triv , triv))
isNorm-SAND₁ {NODE b} {OR B B₁} ()
isNorm-SAND₁ {NODE b} {SAND B B₁} nf-p = triv , ((snd nf-p) , (triv , triv))
isNorm-SAND₁ {AND A A₁} {NODE b} nf-p = (fst nf-p) , (triv , (triv , triv))
isNorm-SAND₁ {AND A A₁} {AND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-SAND₁ {AND A A₁} {OR B B₁} ()
isNorm-SAND₁ {AND A A₁} {SAND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-SAND₁ {OR A A₁} {NODE b} nf-p = (fst nf-p) , (triv , (triv , triv))
isNorm-SAND₁ {OR A A₁} {AND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-SAND₁ {OR A A₁} {OR B B₁} ()
isNorm-SAND₁ {OR A A₁} {SAND B B₁} nf-p = (fst nf-p) , ((snd nf-p) , (triv , triv))
isNorm-SAND₁ {SAND A A₁} {NODE b} ()
isNorm-SAND₁ {SAND A A₁} {AND B B₁} ()
isNorm-SAND₁ {SAND A A₁} {OR B B₁} ()
isNorm-SAND₁ {SAND A A₁} {SAND B B₁} ()

isNorm-SAND₂ : ∀{A B} → isNorm A → isNorm B → notSAND A → notOR B → isNorm (SAND A B)
isNorm-SAND₂ {NODE b} {NODE b₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = triv , triv
isNorm-SAND₂ {NODE b} {AND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = triv , nf-p₂
isNorm-SAND₂ {NODE b} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-SAND₂ {NODE b} {SAND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = triv , nf-p₂
isNorm-SAND₂ {AND A A₁} {NODE b} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , triv
isNorm-SAND₂ {AND A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-SAND₂ {AND A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-SAND₂ {AND A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-SAND₂ {OR A A₁} {NODE b} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , triv
isNorm-SAND₂ {OR A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-SAND₂ {OR A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-SAND₂ {OR A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p₁ n-p₂ = nf-p₁ , nf-p₂
isNorm-SAND₂ {SAND A A₁} {NODE b} nf-p₁ nf-p₂ () n-p₂
isNorm-SAND₂ {SAND A A₁} {AND B B₁} nf-p₁ nf-p₂ () n-p₂
isNorm-SAND₂ {SAND A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p₁ ()
isNorm-SAND₂ {SAND A A₁} {SAND B B₁} nf-p₁ nf-p₂ () n-p₂

≠-NODE : ∀{A b} → notNODE A → NODE b ≠ A
≠-NODE {NODE b} {b₁} ()
≠-NODE {AND A A₁} {b} p ()
≠-NODE {OR A A₁} {b} p ()
≠-NODE {SAND A A₁} {b} p ()

isNorm-OR₁ : ∀{A B} → isNorm (OR A B) → isNorm A × isNorm B × notOR A
isNorm-OR₁ {NODE b} {NODE b₁} (a , b₂) = triv , (triv , triv)
isNorm-OR₁ {NODE b} {AND B B₁} (a , b₁) = triv , (b₁ , triv)
isNorm-OR₁ {NODE b} {OR B B₁} (a , b₁) = triv , (b₁ , triv)
isNorm-OR₁ {NODE b} {SAND B B₁} (a , b₁) = triv , (b₁ , triv)
isNorm-OR₁ {AND A A₁} {NODE b} (a , b₁) = a , (triv , triv)
isNorm-OR₁ {AND A A₁} {AND B B₁} (a , b) = a , (b , triv)
isNorm-OR₁ {AND A A₁} {OR B B₁} (a , b) = a , (b , triv)
isNorm-OR₁ {AND A A₁} {SAND B B₁} (a , b) = a , (b , triv)
isNorm-OR₁ {OR A A₁} {NODE b} ()
isNorm-OR₁ {OR A A₁} {AND B B₁} ()
isNorm-OR₁ {OR A A₁} {OR B B₁} ()
isNorm-OR₁ {OR A A₁} {SAND B B₁} ()
isNorm-OR₁ {SAND A A₁} {NODE b} (a , b₁) = a , (triv , triv)
isNorm-OR₁ {SAND A A₁} {AND B B₁} (a , b) = a , (b , triv)
isNorm-OR₁ {SAND A A₁} {OR B B₁} (a , b) = a , (b , triv)
isNorm-OR₁ {SAND A A₁} {SAND B B₁} (a , b) = a , (b , triv)

isNorm-OR₂ : ∀{A B} → isNorm A → isNorm B → notOR A → isNorm (OR A B)
isNorm-OR₂ {NODE b} {NODE b₁} nf-p₁ nf-p₂ n-p = triv , triv
isNorm-OR₂ {NODE b} {AND B B₁} nf-p₁ nf-p₂ n-p = triv , nf-p₂
isNorm-OR₂ {NODE b} {OR B B₁} nf-p₁ nf-p₂ n-p = triv , nf-p₂
isNorm-OR₂ {NODE b} {SAND B B₁} nf-p₁ nf-p₂ n-p = triv , nf-p₂
isNorm-OR₂ {AND A A₁} {NODE b} nf-p₁ nf-p₂ n-p = nf-p₁ , triv
isNorm-OR₂ {AND A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p = nf-p₁ , nf-p₂
isNorm-OR₂ {AND A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p = nf-p₁ , nf-p₂
isNorm-OR₂ {AND A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p = nf-p₁ , nf-p₂
isNorm-OR₂ {OR A A₁} {NODE b} nf-p₁ nf-p₂ n-p = ⊥-elim n-p
isNorm-OR₂ {OR A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p = ⊥-elim n-p
isNorm-OR₂ {OR A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p = ⊥-elim n-p
isNorm-OR₂ {OR A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p = ⊥-elim n-p
isNorm-OR₂ {SAND A A₁} {NODE b} nf-p₁ nf-p₂ n-p = nf-p₁ , triv
isNorm-OR₂ {SAND A A₁} {AND B B₁} nf-p₁ nf-p₂ n-p = nf-p₁ , nf-p₂
isNorm-OR₂ {SAND A A₁} {OR B B₁} nf-p₁ nf-p₂ n-p = nf-p₁ , nf-p₂
isNorm-OR₂ {SAND A A₁} {SAND B B₁} nf-p₁ nf-p₂ n-p = nf-p₁ , nf-p₂

⟿-isNorm : ∀{A N} → isNorm N → N ⟿ A → ⊥ {lzero}
⟿-isNorm {OR A (OR B C)} {.(OR (OR _ _) _)} nf-p ⟿-OR-assoc with OR A B ≅ C
... | inj₁ refl = ⊥-elim nf-p
... | inj₂ p = ⊥-elim nf-p
⟿-isNorm {.(AND _ (AND _ _))} {.(AND (AND _ _) _)} () ⟿-AND-assoc
⟿-isNorm {SAND A (SAND B (NODE b))} {.(SAND (SAND A B) (NODE b))} nf-p ⟿-SAND-assoc = ⊥-elim nf-p
⟿-isNorm {SAND A (SAND B (AND C C₁))} {.(SAND (SAND A B) (AND C C₁))} nf-p ⟿-SAND-assoc = ⊥-elim nf-p
⟿-isNorm {SAND A (SAND B (OR C C₁))} {.(SAND (SAND A B) (OR C C₁))} nf-p ⟿-SAND-assoc = ⊥-elim nf-p
⟿-isNorm {SAND A (SAND B (SAND C C₁))} {.(SAND (SAND A B) (SAND C C₁))} nf-p ⟿-SAND-assoc = ⊥-elim nf-p
⟿-isNorm {OR (AND (NODE b) B) (AND .(NODE b) D)} {.(AND (NODE b) (OR B D))} nf-p ⟿-AND-dist = ⊥-elim nf-p
⟿-isNorm {OR (AND (AND A A₁) B) (AND .(AND A A₁) D)} {.(AND (AND A A₁) (OR B D))} nf-p ⟿-AND-dist = ⊥-elim nf-p
⟿-isNorm {OR (AND (OR A A₁) B) (AND .(OR A A₁) D)} {.(AND (OR A A₁) (OR B D))} nf-p ⟿-AND-dist = ⊥-elim nf-p
⟿-isNorm {OR (AND (SAND A A₁) B) (AND .(SAND A A₁) D)} {.(AND (SAND A A₁) (OR B D))} nf-p ⟿-AND-dist = ⊥-elim nf-p
⟿-isNorm {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ (OR _ _))} nf-p ⟿-SAND-dist = ⊥-elim nf-p
⟿-isNorm {AND A B} {AND A' _} nf-p (⟿-AND₁ d) with isNorm-AND₁ {A'}{B} nf-p
... | r₁ , r₂ , r₃ , r₄ = ⟿-isNorm {A}{A'} r₁ d
⟿-isNorm {AND A B} {AND _ B'} nf-p (⟿-AND₂ d) with isNorm-AND₁ {A}{B'} nf-p
... | r₁ , r₂ , r₃ , r₄ = ⟿-isNorm {B}{B'} r₂ d
⟿-isNorm {OR A B} {OR A' _} nf-p (⟿-OR₁ d) with isNorm-OR₁ {A'}{B} nf-p
... | r₁ , r₂ , r₃ = ⟿-isNorm {A}{A'} r₁ d
⟿-isNorm {OR A B} {OR _ B'} nf-p (⟿-OR₂ d) with isNorm-OR₁ {A}{B'} nf-p
... | r₁ , r₂ , r₃ = ⟿-isNorm {B}{B'} r₂ d
⟿-isNorm {SAND A B} {SAND A' _} nf-p (⟿-SAND₁ d) with isNorm-SAND₁ {A'}{B} nf-p
... | r₁ , r₂ , r₃ , r₄ = ⟿-isNorm {A}{A'} r₁ d
⟿-isNorm {SAND A B} {SAND _ B'} nf-p (⟿-SAND₂ d) with isNorm-SAND₁ {A}{B'} nf-p
... | r₁ , r₂ , r₃ , r₄ = ⟿-isNorm {B}{B'} r₂ d

local-CF : ∀{A B C} → A ⟿ B → A ⟿ C → Σ[ D ∈ ATree ]( B ⟿* D × C ⟿* D )
local-CF {OR (OR A B) C} {.(OR _ (OR _ _))} {.(OR _ (OR _ _))} ⟿-OR-assoc ⟿-OR-assoc = (OR A (OR B C)) , (⟿-refl , ⟿-refl)
local-CF {OR (OR (OR A B) C) D} {.(OR (OR _ _) (OR _ _))} {OR .(OR _ (OR _ _)) _} ⟿-OR-assoc (⟿-OR₁ ⟿-OR-assoc) = (OR A (OR B (OR C D))) , ((⟿-step (⟿-OR-assoc {A}{B})) , ⟿-trans (⟿-step ⟿-OR-assoc) (⟿-step (⟿-OR₂ ⟿-OR-assoc)))
local-CF {OR (OR A B) C} {.(OR A (OR B C))} {OR (OR A' .B) .C} ⟿-OR-assoc (⟿-OR₁ (⟿-OR₁ d)) = (OR A' (OR B C)) , ((⟿-step (⟿-OR₁ d)) , (⟿-step ⟿-OR-assoc))
local-CF {OR (OR A B) C} {.(OR A (OR B C))} {OR (OR .A B') .C} ⟿-OR-assoc (⟿-OR₁ (⟿-OR₂ d)) = (OR A (OR B' C)) , ((⟿-step (⟿-OR₂ (⟿-OR₁ d))) , (⟿-step ⟿-OR-assoc))
local-CF {OR (OR A B) C} {.(OR _ (OR _ _))} {OR (OR _ _) C'} ⟿-OR-assoc (⟿-OR₂ d₂) = (OR A (OR B C')) , ((⟿-step (⟿-OR₂ (⟿-OR₂ d₂))) , (⟿-step ⟿-OR-assoc))

local-CF {AND (AND A B) C} {.(AND _ (AND _ _))} {.(AND _ (AND _ _))} ⟿-AND-assoc ⟿-AND-assoc = (AND A (AND B C)) , (⟿-refl , ⟿-refl)
local-CF {AND (AND (AND A B) C) D} {.(AND (AND _ _) (AND _ _))} {AND .(AND _ (AND _ _)) _} ⟿-AND-assoc (⟿-AND₁ ⟿-AND-assoc) = (AND A (AND B (AND C D))) , ((⟿-step (⟿-AND-assoc {A}{B})) , ⟿-trans (⟿-step ⟿-AND-assoc) (⟿-step (⟿-AND₂ ⟿-AND-assoc)))
local-CF {AND (AND A B) C} {.(AND A (AND B C))} {AND (AND A' .B) .C} ⟿-AND-assoc (⟿-AND₁ (⟿-AND₁ d)) = (AND A' (AND B C)) , ((⟿-step (⟿-AND₁ d)) , (⟿-step ⟿-AND-assoc))
local-CF {AND (AND A B) C} {.(AND A (AND B C))} {AND (AND .A B') .C} ⟿-AND-assoc (⟿-AND₁ (⟿-AND₂ d)) = (AND A (AND B' C)) , ((⟿-step (⟿-AND₂ (⟿-AND₁ d))) , (⟿-step ⟿-AND-assoc))
local-CF {AND (AND A B) C} {.(AND _ (AND _ _))} {AND (AND _ _) C'} ⟿-AND-assoc (⟿-AND₂ d₂) = (AND A (AND B C')) , ((⟿-step (⟿-AND₂ (⟿-AND₂ d₂))) , (⟿-step ⟿-AND-assoc))

local-CF {SAND (SAND A B) C} {.(SAND _ (SAND _ _))} {.(SAND _ (SAND _ _))} ⟿-SAND-assoc ⟿-SAND-assoc = (SAND A (SAND B C)) , (⟿-refl , ⟿-refl)
local-CF {SAND (SAND (SAND A B) C) D} {.(SAND (SAND _ _) (SAND _ _))} {SAND .(SAND _ (SAND _ _)) _} ⟿-SAND-assoc (⟿-SAND₁ ⟿-SAND-assoc) = (SAND A (SAND B (SAND C D))) , ((⟿-step (⟿-SAND-assoc {A}{B})) , ⟿-trans (⟿-step ⟿-SAND-assoc) (⟿-step (⟿-SAND₂ ⟿-SAND-assoc)))
local-CF {SAND (SAND A B) C} {.(SAND A (SAND B C))} {SAND (SAND A' .B) .C} ⟿-SAND-assoc (⟿-SAND₁ (⟿-SAND₁ d)) = (SAND A' (SAND B C)) , ((⟿-step (⟿-SAND₁ d)) , (⟿-step ⟿-SAND-assoc))
local-CF {SAND (SAND A B) C} {.(SAND A (SAND B C))} {SAND (SAND .A B') .C} ⟿-SAND-assoc (⟿-SAND₁ (⟿-SAND₂ d)) = (SAND A (SAND B' C)) , ((⟿-step (⟿-SAND₂ (⟿-SAND₁ d))) , (⟿-step ⟿-SAND-assoc))
local-CF {SAND (SAND A B) C} {.(SAND _ (SAND _ _))} {SAND (SAND _ _) C'} ⟿-SAND-assoc (⟿-SAND₂ d₂) = (SAND A (SAND B C')) , ((⟿-step (⟿-SAND₂ (⟿-SAND₂ d₂))) , (⟿-step ⟿-SAND-assoc))

local-CF {AND (AND A B) (OR C D)} {.(AND _ (AND _ (OR _ _)))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} ⟿-AND-assoc ⟿-AND-dist = (OR (AND A (AND B C)) (AND A (AND B D))) , ((⟿-trans (⟿-step (⟿-AND₂ ⟿-AND-dist)) (⟿-step ⟿-AND-dist)) , ⟿-trans (⟿*-OR₁ (⟿-step ⟿-AND-assoc)) (⟿*-OR₂ (⟿-step ⟿-AND-assoc)))

local-CF {SAND (SAND A B) (OR C D)} {.(SAND _ (SAND _ (OR _ _)))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} ⟿-SAND-assoc ⟿-SAND-dist = (OR (SAND A (SAND B C)) (SAND A (SAND B D))) , ((⟿-trans (⟿-step (⟿-SAND₂ ⟿-SAND-dist)) (⟿-step ⟿-SAND-dist)) , ⟿-trans (⟿*-OR₁ (⟿-step ⟿-SAND-assoc)) (⟿*-OR₂ (⟿-step ⟿-SAND-assoc)))

--  AND A (AND (OR B C) D)
--  AND (OR (AND A B) (AND A C)) D
local-CF {AND (AND A (OR B C)) D} {AND .A (AND (OR _ _) .D)} {AND .(OR (AND A _) (AND A _)) .D} ⟿-AND-assoc (⟿-AND₁ ⟿-AND-dist) = {!!} , ({!!} , {!!})

local-CF {SAND (SAND A B) C} {.(SAND _ (SAND _ _))} {SAND A' _} ⟿-SAND-assoc (⟿-SAND₁ d) = {!!}

local-CF {.(AND (AND _ _) _)} {.(AND _ _)} {.(AND _ (AND _ _))} (⟿-AND₁ d₁) ⟿-AND-assoc = {!!}
local-CF {.(OR (OR _ _) _)} {.(OR _ _)} {.(OR _ (OR _ _))} (⟿-OR₁ d₁) ⟿-OR-assoc = {!!}
local-CF {.(SAND (SAND _ _) _)} {.(SAND _ _)} {.(SAND _ (SAND _ _))} (⟿-SAND₁ d₁) ⟿-SAND-assoc = {!!}

local-CF {.(AND (AND _ _) _)} {.(AND (AND _ _) _)} {.(AND _ (AND _ _))} (⟿-AND₂ d₁) ⟿-AND-assoc = {!!}
local-CF {.(OR (OR _ _) _)} {.(OR (OR _ _) _)} {.(OR _ (OR _ _))} (⟿-OR₂ d₁) ⟿-OR-assoc = {!!}
local-CF {.(SAND (SAND _ _) _)} {.(SAND (SAND _ _) _)} {.(SAND _ (SAND _ _))} (⟿-SAND₂ d₁) ⟿-SAND-assoc = {!!}

local-CF {.(AND (AND _ _) (OR _ _))} {.(OR (AND (AND _ _) _) (AND (AND _ _) _))} {.(AND _ (AND _ (OR _ _)))} ⟿-AND-dist ⟿-AND-assoc = {!!}
local-CF {.(SAND (SAND _ _) (OR _ _))} {.(OR (SAND (SAND _ _) _) (SAND (SAND _ _) _))} {.(SAND _ (SAND _ (OR _ _)))} ⟿-SAND-dist ⟿-SAND-assoc = {!!}

local-CF {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(OR (AND _ _) (AND _ _))} ⟿-AND-dist ⟿-AND-dist = {!!}
local-CF {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-dist ⟿-SAND-dist = {!!}

local-CF {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ (OR _ _))} ⟿-AND-dist (⟿-AND₁ d₂) = {!!}
local-CF {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ (OR _ _))} ⟿-SAND-dist (⟿-SAND₁ d₂) = {!!}

local-CF {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} {.(AND _ _)} ⟿-AND-dist (⟿-AND₂ d₂) = {!!}
local-CF {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} {.(SAND _ _)} ⟿-SAND-dist (⟿-SAND₂ d₂) = {!!}

local-CF {.(AND _ (OR _ _))} {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} (⟿-AND₁ d₁) ⟿-AND-dist = {!!}
local-CF {.(SAND _ (OR _ _))} {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} (⟿-SAND₁ d₁) ⟿-SAND-dist = {!!}

local-CF {.(AND _ (OR _ _))} {.(AND _ _)} {.(OR (AND _ _) (AND _ _))} (⟿-AND₂ d₁) ⟿-AND-dist = {!!}
local-CF {.(SAND _ (OR _ _))} {.(SAND _ _)} {.(OR (SAND _ _) (SAND _ _))} (⟿-SAND₂ d₁) ⟿-SAND-dist = {!!}

local-CF {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₁ d₁) (⟿-AND₁ d₂) = {!!}
local-CF {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ d₁) (⟿-OR₁ d₂) = {!!}
local-CF {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₁ d₁) (⟿-SAND₁ d₂) = {!!}

local-CF {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₁ d₁) (⟿-AND₂ d₂) = {!!}
local-CF {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ d₁) (⟿-OR₂ d₂) = {!!}
local-CF {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₁ d₁) (⟿-SAND₂ d₂) = {!!}

local-CF {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₂ d₁) (⟿-AND₁ d₂) = {!!}
local-CF {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ d₁) (⟿-OR₁ d₂) = {!!}
local-CF {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₂ d₁) (⟿-SAND₁ d₂) = {!!}

local-CF {.(AND _ _)} {.(AND _ _)} {.(AND _ _)} (⟿-AND₂ d₁) (⟿-AND₂ d₂) = {!!}
local-CF {.(OR _ _)} {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ d₁) (⟿-OR₂ d₂) = {!!}
local-CF {.(SAND _ _)} {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₂ d₁) (⟿-SAND₂ d₂) = {!!}
