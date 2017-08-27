open import prelude

module attack-tree {𝔹 : Set} {pf : dec 𝔹} where

data ATree : Set where
  NODE : (b : 𝔹) → ATree
  AND  : ATree → ATree → ATree
  OR   : ATree → ATree → ATree
  SAND : ATree → ATree → ATree

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

data _⟿©_ : ATree → ATree → Set where
  ⟿©-OR-sym : ∀{A B : ATree} → (OR A B) ⟿© (OR B A)
  ⟿©-AND-sym : ∀{A B : ATree} → (AND A B) ⟿© (AND B A)
  ⟿©-OR-assoc : ∀{A B C : ATree} → (OR A (OR B C)) ⟿© (OR (OR A B) C)
  ⟿©-AND-assoc : ∀{A B C : ATree} → (AND A (AND B C)) ⟿© (AND (AND A B) C)
  ⟿©-SAND-assoc : ∀{A B C : ATree} → (SAND A (SAND B C)) ⟿© (SAND (SAND A B) C)
  ⟿©-AND-distl : ∀{A B C : ATree} → (AND A (OR B C)) ⟿© (OR (AND A B) (AND A C))
  ⟿©-SAND-distl : ∀{A B C : ATree} → (SAND A (OR B C)) ⟿© (OR (SAND A B) (SAND A C))
  ⟿©-AND-distr : ∀{A B C : ATree} → (AND (OR A B) C) ⟿© (OR (AND A C) (AND B C))
  ⟿©-SAND-distr : ∀{A B C : ATree} → (SAND (OR A B) C) ⟿© (OR (SAND A C) (SAND B C))    
  ⟿©-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿© A₂ → (AND A₁ B) ⟿© (AND A₂ B)
  ⟿©-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿© B₂ → (AND A B₁) ⟿© (AND A B₂)
  ⟿©-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿© A₂ → (OR A₁ B) ⟿© (OR A₂ B)
  ⟿©-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿© B₂ → (OR A B₁) ⟿© (OR A B₂)
  ⟿©-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿© A₂ → (SAND A₁ B) ⟿© (SAND A₂ B)
  ⟿©-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿© B₂ → (SAND A B₁) ⟿© (SAND A B₂)
  ⟿©-contract : ∀{A : ATree} → (OR A A) ⟿© A

data _⟿©*_ : ATree → ATree → Set where
  ⟿©-step : ∀{A B : ATree} → A ⟿© B → A ⟿©* B
  ⟿©-refl : ∀{A : ATree} → A ⟿©* A
  ⟿©-trans : ∀{A B C : ATree} → A ⟿©* B → B ⟿©* C → A ⟿©* C

data _⟿_ : ATree → ATree → Set where
  ⟿-OR-sym : ∀{A B : ATree} → (OR A B) ⟿ (OR B A)
  ⟿-AND-sym : ∀{A B : ATree} → (AND A B) ⟿ (AND B A)
  ⟿-OR-assoc : ∀{A B C : ATree} → (OR A (OR B C)) ⟿ (OR (OR A B) C)
  ⟿-AND-assoc : ∀{A B C : ATree} → (AND A (AND B C)) ⟿ (AND (AND A B) C)
  ⟿-SAND-assoc : ∀{A B C : ATree} → (SAND A (SAND B C)) ⟿ (SAND (SAND A B) C)
  ⟿-AND-distl : ∀{A B C : ATree} → (AND A (OR B C)) ⟿ (OR (AND A B) (AND A C))
  ⟿-SAND-distl : ∀{A B C : ATree} → (SAND A (OR B C)) ⟿ (OR (SAND A B) (SAND A C))
  ⟿-AND-distr : ∀{A B C : ATree} → (AND (OR A B) C) ⟿ (OR (AND A C) (AND B C))
  ⟿-SAND-distr : ∀{A B C : ATree} → (SAND (OR A B) C) ⟿ (OR (SAND A C) (SAND B C))    
  ⟿-AND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (AND A₁ B) ⟿ (AND A₂ B)
  ⟿-AND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (AND A B₁) ⟿ (AND A B₂)
  ⟿-OR₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (OR A₁ B) ⟿ (OR A₂ B)
  ⟿-OR₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (OR A B₁) ⟿ (OR A B₂)
  ⟿-SAND₁ : ∀{A₁ A₂ B : ATree} → A₁ ⟿ A₂ → (SAND A₁ B) ⟿ (SAND A₂ B)
  ⟿-SAND₂ : ∀{A B₁ B₂ : ATree} → B₁ ⟿ B₂ → (SAND A B₁) ⟿ (SAND A B₂)

data _⟿*_ : ATree → ATree → Set where
  ⟿-step : ∀{A B : ATree} → A ⟿ B → A ⟿* B
  ⟿-refl : ∀{A : ATree} → A ⟿* A
  ⟿-trans : ∀{A B C : ATree} → A ⟿* B → B ⟿* C → A ⟿* C

data _≈©_ : ATree → ATree → Set where
  ≈©-reduce : ∀{A B : ATree} → A ⟿© B → A ≈© B
  ≈©-refl : ∀{A : ATree} → A ≈© A
  ≈©-sym : ∀{A B : ATree} → A ≈© B → B ≈© A
  ≈©-trans : ∀{A B C : ATree} → A ≈© B → B ≈© C → A ≈© C

data _≈_ : ATree → ATree → Set where
  ≈-reduce : ∀{A B : ATree} → A ⟿ B → A ≈ B
  ≈-refl : ∀{A : ATree} → A ≈ A
  ≈-sym : ∀{A B : ATree} → A ≈ B → B ≈ A
  ≈-trans : ∀{A B C : ATree} → A ≈ B → B ≈ C → A ≈ C

⟿©*-≈© : ∀{t s} → t ⟿©* s → t ≈© s
⟿©*-≈© {t} {s} (⟿©-step x) = ≈©-reduce x
⟿©*-≈© {t} {.t} ⟿©-refl = ≈©-refl
⟿©*-≈© {t} {s} (⟿©-trans {_}{t'}{_} p₁ p₂) with ⟿©*-≈© p₁ | ⟿©*-≈© p₂
... | r₁ | r₂ = ≈©-trans r₁ r₂

postulate CR-⟿© : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿©* s₁ → t₂ ⟿©* s₂ → Σ[ s' ∈ ATree ]( (s₁ ⟿©* s') × (s₂ ⟿©* s') )

postulate CR-⟿ : ∀{t₁ s₁ t₂ s₂} → t₁ ⟿* s₁ → t₂ ⟿* s₂ → Σ[ s' ∈ ATree ]( (s₁ ⟿* s') × (s₂ ⟿* s') )

_⟱_ : ∀(t₁ t₂ : ATree) → Set
t₁ ⟱ t₂ = Σ[ s ∈ ATree ]( t₁ ⟿* s × t₂ ⟿* s )

_≃ⱼ_ : ∀(t₁ t₂ : ATree) → Set
t₁ ≃ⱼ t₂ = Σ[ s₁ ∈ ATree ](Σ[ s₂ ∈ ATree ](t₁ ⟿©* s₁ × t₂ ⟿©* s₂ × s₁ ⟱ s₂))

_≃_ : ∀(t₁ t₂ : ATree) → Set
t₁ ≃ t₂ = Σ[ s₁ ∈ ATree ](Σ[ s₂ ∈ ATree ](t₁ ⟿©* s₁ × t₂ ⟿©* s₂ × s₁ ≈ s₂))

⟱-refl : ∀{t} → t ⟱ t
⟱-refl {t} = t , (⟿-refl , ⟿-refl)

⟱-sym : ∀{t₁ t₂} → t₁ ⟱ t₂ → t₂ ⟱ t₁
⟱-sym {t₁} {t₂} (s₁ , p₁ , p₂) = s₁ , (p₂ , p₁)

⟱-trans : ∀{t₁ t₂ t₃} → t₁ ⟱ t₂ → t₂ ⟱ t₃ → t₁ ⟱ t₃
⟱-trans {t₁}{t₂}{t₃} (s₁ , p₁ , p₂) (s₂ , p₃ , p₄) with CR-⟿ p₂ p₃
... | (s₃ , p₅ , p₆) = s₃ , ((⟿-trans p₁ p₅) , ⟿-trans p₄ p₆)

⟿-⟿© : ∀{t₁ t₂} → t₁ ⟿ t₂ → t₁ ⟿© t₂
⟿-⟿© {NODE b} {NODE b₁} ()
⟿-⟿© {NODE b} {AND t₄ t₅} ()
⟿-⟿© {NODE b} {OR t₄ t₅} ()
⟿-⟿© {NODE b} {SAND t₄ t₅} ()
⟿-⟿© {AND t₄ t₅} {NODE b} ()
⟿-⟿© {AND t₄ t₅} {AND .t₅ .t₄} ⟿-AND-sym = ⟿©-AND-sym
⟿-⟿© {AND t₄ .(AND _ t₇)} {AND .(AND t₄ _) t₇} ⟿-AND-assoc = ⟿©-AND-assoc
⟿-⟿© {AND t₄ t₅} {AND t₆ .t₅} (⟿-AND₁ p) = ⟿©-AND₁ (⟿-⟿© p)
⟿-⟿© {AND t₄ t₅} {AND .t₄ t₇} (⟿-AND₂ p) = ⟿©-AND₂ (⟿-⟿© p)
⟿-⟿© {AND t₄ .(OR _ _)} {OR .(AND t₄ _) .(AND t₄ _)} ⟿-AND-distl = ⟿©-AND-distl
⟿-⟿© {AND .(OR _ _) t₅} {OR .(AND _ t₅) .(AND _ t₅)} ⟿-AND-distr = ⟿©-AND-distr
⟿-⟿© {AND t₄ t₅} {SAND t₆ t₇} ()
⟿-⟿© {OR t₄ t₅} {NODE b} ()
⟿-⟿© {OR t₄ t₅} {AND t₆ t₇} ()
⟿-⟿© {OR t₄ t₅} {OR .t₅ .t₄} ⟿-OR-sym = ⟿©-OR-sym
⟿-⟿© {OR t₄ .(OR _ t₇)} {OR .(OR t₄ _) t₇} ⟿-OR-assoc = ⟿©-OR-assoc
⟿-⟿© {OR t₄ t₅} {OR t₆ .t₅} (⟿-OR₁ p) = ⟿©-OR₁ (⟿-⟿© p)
⟿-⟿© {OR t₄ t₅} {OR .t₄ t₇} (⟿-OR₂ p) = ⟿©-OR₂ (⟿-⟿© p)
⟿-⟿© {OR t₄ t₅} {SAND t₆ t₇} ()
⟿-⟿© {SAND t₄ t₅} {NODE b} ()
⟿-⟿© {SAND t₄ t₅} {AND t₆ t₇} ()
⟿-⟿© {SAND t₄ .(OR _ _)} {OR .(SAND t₄ _) .(SAND t₄ _)} ⟿-SAND-distl = ⟿©-SAND-distl
⟿-⟿© {SAND .(OR _ _) t₅} {OR .(SAND _ t₅) .(SAND _ t₅)} ⟿-SAND-distr = ⟿©-SAND-distr
⟿-⟿© {SAND t₄ .(SAND _ t₇)} {SAND .(SAND t₄ _) t₇} ⟿-SAND-assoc = ⟿©-SAND-assoc
⟿-⟿© {SAND t₄ t₅} {SAND t₆ .t₅} (⟿-SAND₁ p) = ⟿©-SAND₁ (⟿-⟿© p)
⟿-⟿© {SAND t₄ t₅} {SAND .t₄ t₇} (⟿-SAND₂ p) = ⟿©-SAND₂ (⟿-⟿© p)

⟿*-⟿©* : ∀{t₁ t₂} → t₁ ⟿* t₂ → t₁ ⟿©* t₂
⟿*-⟿©* (⟿-step x) = ⟿©-step (⟿-⟿© x)
⟿*-⟿©* ⟿-refl = ⟿©-refl
⟿*-⟿©* (⟿-trans p₁ p₂) = ⟿©-trans (⟿*-⟿©* p₁) (⟿*-⟿©* p₂)

≃ⱼ-refl : ∀{t} → t ≃ⱼ t
≃ⱼ-refl {t} = t , (t , (⟿©-refl , (⟿©-refl , (t , (⟿-refl , ⟿-refl)))))

≃ⱼ-sym : ∀{t₁ t₂} → t₁ ≃ⱼ t₂ → t₂ ≃ⱼ t₁
≃ⱼ-sym {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , s₃ , p₄ , p₅) = s₂ , (s₁ , (p₂ , (p₁ , (s₃ , (p₅ , p₄)))))

≃ⱼ-trans : ∀{t₁ t₂ t₃} → t₁ ≃ⱼ t₂ → t₂ ≃ⱼ t₃ → t₁ ≃ⱼ t₃
≃ⱼ-trans {t₁}{t₂}{t₃} (s₁ , s₂ , p₁ , p₂ , s₃ , p₄ , p₅) (s₄ , s₅ , p₆ , p₇ , s₆ , p₈ , p₉) with CR-⟿© p₂ p₆
... | (s₁' , r₁ , r₂) with CR-⟿© (⟿*-⟿©* p₅) r₁
... | (s₂' , r₃ , r₄) with CR-⟿© r₂ (⟿*-⟿©* p₈)
... | (s₃' , r₅ , r₆) with CR-⟿© r₄ r₅
... | (s₄' , r₇ , r₈) = s₄' , (s₄' , (⟿©-trans p₁ (⟿©-trans (⟿*-⟿©* p₄) (⟿©-trans r₃ r₇)) , (⟿©-trans p₇ (⟿©-trans (⟿*-⟿©* p₉) (⟿©-trans r₆ r₈)) , (s₄' , (⟿-refl , ⟿-refl)))))

≈-≈© : ∀{t₁ t₂} → t₁ ≈ t₂ → t₁ ≈© t₂
≈-≈© (≈-reduce x) = ≈©-reduce (⟿-⟿© x)
≈-≈© ≈-refl = ≈©-refl
≈-≈© (≈-sym p) = ≈©-sym (≈-≈© p)
≈-≈© (≈-trans p₁ p₂) = ≈©-trans (≈-≈© p₁) (≈-≈© p₂)

⟿*-≈ : ∀{t₁ t₂} → t₁ ⟿* t₂ → t₁ ≈ t₂
⟿*-≈ (⟿-step x) = ≈-reduce x
⟿*-≈ ⟿-refl = ≈-refl
⟿*-≈ (⟿-trans p₁ p₂) with ⟿*-≈ p₁ | ⟿*-≈ p₂
... | r₁ | r₂ = ≈-trans r₁ r₂

⟱-≈ : ∀{t₁ t₂} → t₁ ⟱ t₂ → t₁ ≈ t₂
⟱-≈ {t₁}{t₂} (s , p₁ , p₂) with ⟿*-≈ p₁ | ⟿*-≈ p₂
... | r₁ | r₂ = ≈-trans r₁ (≈-sym r₂)

≃ⱼ-≃ : ∀{t₁ t₂} → t₁ ≃ⱼ t₂ → t₁ ≃ t₂
≃ⱼ-≃ {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , p₃) = s₁ , (s₂ , (p₁ , (p₂ , ⟱-≈ p₃)))

≈-⟱ : ∀{t₁ t₂} → t₁ ≈ t₂ → t₁ ⟱ t₂
≈-⟱ {t₁} {t₂} (≈-reduce x) = t₂ , ((⟿-step x) , ⟿-refl)
≈-⟱ {t₁} {.t₁} ≈-refl = t₁ , (⟿-refl , ⟿-refl)
≈-⟱ {t₁} {t₂} (≈-sym p) with ≈-⟱ p
... | (s , p₁ , p₂) = s , (p₂ , p₁)
≈-⟱ {t₁} {t₂} (≈-trans p₁ p₂) with ≈-⟱ p₁ | ≈-⟱ p₂
... | r₁ | r₂ = ⟱-trans r₁ r₂

≃-≃ⱼ : ∀{t₁ t₂} → t₁ ≃ t₂ → t₁ ≃ⱼ t₂
≃-≃ⱼ {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , p₃) = s₁ , (s₂ , (p₁ , (p₂ , ≈-⟱ p₃)))

≃-refl : ∀{t} → t ≃ t
≃-refl {t} = ≃ⱼ-≃ (≃ⱼ-refl {t})

≃-sym : ∀{t₁ t₂} → t₁ ≃ t₂ → t₂ ≃ t₁
≃-sym p = ≃ⱼ-≃ (≃ⱼ-sym (≃-≃ⱼ p))

≃-trans : ∀{t₁ t₂ t₃} → t₁ ≃ t₂ → t₂ ≃ t₃ → t₁ ≃ t₃
≃-trans p₁ p₂ = ≃ⱼ-≃ (≃ⱼ-trans (≃-≃ⱼ p₁) (≃-≃ⱼ p₂))

≈©-≃ : ∀{t₁ t₂} → t₁ ≈© t₂ → t₁ ≃ t₂
≈©-≃ {t₁} {t₂} (≈©-reduce x) = t₂ , (t₂ , ((⟿©-step x) , (⟿©-refl , ≈-refl)))
≈©-≃ {t₁} {.t₁} ≈©-refl = ≃-refl
≈©-≃ {t₁} {t₂} (≈©-sym p) = ≃-sym (≈©-≃ p)
≈©-≃ {t₁} {t₂} (≈©-trans p₁ p₂) = ≃-trans (≈©-≃ p₁) (≈©-≃ p₂)

≈©-≃-inv : ∀{t₁ t₂} → t₁ ≃ t₂ → t₁ ≈© t₂
≈©-≃-inv {t₁}{t₂} (s₁ , s₂ , p₁ , p₂ , p₃) = ≈©-trans (⟿©*-≈© p₁) (≈©-trans (≈-≈© p₃) (≈©-sym (⟿©*-≈© p₂)))
