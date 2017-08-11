module dialectica-at-ops where

open import prelude
open import lineale
open import lineale-thms

open import dialectica-cat

-----------------------------------------------------------------------
-- The Attack Tree Operators                                         --
-----------------------------------------------------------------------

_⊙ᵣ_ : ∀{U X V Y : Set} → (U → X → Four) → (V → Y → Four) → ((U × V) → (X × Y) → Four)
_⊙ᵣ_ α β (u , v) (x , y) = (α u x) ⊙₄ (β v y)

_⊙_ : (A B : Obj) → Obj
(U , X , α) ⊙ (V , Y , β) = ((U × V) , (X × Y) , α ⊙ᵣ β)
  
_⊙ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊙ B) (C ⊙ D)
_⊙ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , func-× F G , (λ {p₁}{p₂} → cond {p₁}{p₂})
 where
   cond : {u : U × V} {y : Z × T} → (α ⊙ᵣ β) u (func-× F G y) ≤₄ (γ ⊙ᵣ δ) (⟨ f , g ⟩ u) y
   cond {u , v}{z , t} with p₁ {u}{z} | p₂ {v}{t}
   ... | r₁ | r₂ = ⊙₄-func {α u (F z)}{γ (f u) z}{β v (G t)}{δ (g v) t} r₁ r₂

⊙-α : {A B C : Obj} → Hom ((A ⊙ B) ⊙ C) (A ⊙ (B ⊙ C))
⊙-α {U , X , α}{V , Y , β}{W , Z , γ} = lr-assoc-× , (rl-assoc-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
   cond : {u : (U × V) × W} {y : X × Y × Z} → ((α ⊙ᵣ β) ⊙ᵣ γ) u (rl-assoc-× y) ≤₄ (α ⊙ᵣ (β ⊙ᵣ γ)) (lr-assoc-× u) y
   cond {(u , v) , w}{x , y , z} = fst (iso₄-inv (⊙₄-assoc {α u x}{β v y}{γ w z}))

⊙-α-inv : {A B C : Obj} → Hom (A ⊙ (B ⊙ C)) ((A ⊙ B) ⊙ C)
⊙-α-inv {U , X , α}{V , Y , β}{W , Z , γ} = rl-assoc-× , (lr-assoc-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
   cond : {u : U × V × W} {y : (X × Y) × Z} → (α ⊙ᵣ (β ⊙ᵣ γ)) u (lr-assoc-× y) ≤₄ ((α ⊙ᵣ β) ⊙ᵣ γ) (rl-assoc-× u) y
   cond {u , v , w}{(x , y) , z} = snd (iso₄-inv (⊙₄-assoc {α u x}{β v y}{γ w z}))

⊙-α-iso₁ : {A B C : Obj} → ⊙-α {A}{B}{C} ○ ⊙-α-inv ≡h id {(A ⊙ B) ⊙ C}
⊙-α-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux) , ext-set aux
 where
  aux : {U V W : Set}{a : (U × V) × W} → (rl-assoc-× ∘ lr-assoc-×) a ≡ id-set a
  aux {a = (u , v) , w} = refl

⊙-α-iso₂ : {A B C : Obj} → ⊙-α-inv {A}{B}{C} ○ ⊙-α ≡h id {A ⊙ (B ⊙ C)}
⊙-α-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux) , (ext-set aux)
 where
  aux : {U V W : Set}{a : U × V × W} → (lr-assoc-× ∘ rl-assoc-×) a ≡ id-set a
  aux {a = u , v , w} = refl

⊙-α-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ⊙ₐ g) ⊙ₐ h) ○ ⊙-α ≡h ⊙-α ○ (f ⊙ₐ (g ⊙ₐ h))
⊙-α-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  {W , Z , γ} {W' , Z' , γ'}
  (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set aux₂
 where
  aux₁ : {a : (U × V) × W} → (lr-assoc-× ∘ ⟨ ⟨ f , g ⟩ , h ⟩) a ≡ (⟨ f , ⟨ g , h ⟩ ⟩ ∘ lr-assoc-×) a
  aux₁ {(u , v) , w} = refl

  aux₂ : {a : X' × Y' × Z'} → (func-× (func-× F G) H ∘ rl-assoc-×) a ≡ (rl-assoc-× ∘ func-× F (func-× G H)) a
  aux₂ {x' , y' , z'} = refl

⊙-β : {A B : Obj} → Hom (A ⊙ B) (B ⊙ A)
⊙-β {U , X , α}{V , Y , β} = twist-× , (twist-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
  cond : {u : U × V} {y : Y × X} → (α ⊙ᵣ β) u (twist-× y) ≤₄ (β ⊙ᵣ α) (twist-× u) y
  cond {u , v}{y , x} = fst (iso₄-inv (⊙₄-sym {α u x}{β v y}))

⊙-β-iso : {A B : Obj} → ⊙-β {A}{B} ○ ⊙-β ≡h id {A ⊙ B}
⊙-β-iso {U , X , α}{V , Y , β} = (ext-set aux) , ext-set aux
 where
   aux : {U V : Set}{a : U × V} → (twist-× ∘ twist-×) a ≡ id-set a
   aux {a = u , v} = refl

⊙-β-nat : {A A' B B' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (f ⊙ₐ g) ○ ⊙-β ≡h ⊙-β ○ (g ⊙ₐ f)
⊙-β-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  (f , F , F-pf) (g , G , G-pf) = (ext-set aux₁) , ext-set aux₂
 where
  aux₁ : {a : U × V} → (twist-× ∘ ⟨ f , g ⟩) a ≡ (⟨ g , f ⟩ ∘ twist-×) a
  aux₁ {u , v} = refl

  aux₂ : {a : Y' × X'} → (func-× F G ∘ twist-×) a ≡ (twist-× ∘ func-× G F) a
  aux₂ {y' , x'} = refl

_▷ᵣ_ : ∀{U X V Y : Set} → (U → X → Four) → (V → Y → Four) → (U × V) → (X × Y) → Four
_▷ᵣ_ α β (u , v) (x , y) = (α u x) ▷₄ (β v y)

_▷_ : Obj → Obj → Obj
(U , X , α) ▷ (V , Y , β) = (U × V) , (X × Y) , α ▷ᵣ β

_▷ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ▷ B) (C ▷ D)
_▷ₐ_ {U , X , α} {V , Y , β} {W , Z , γ} {M , T , φ} (f , F , p1) (g , G , p2) = (func-× f g) , (func-× F G , (λ {u : U × V}{y : Z × T} → aux {u}{y}))
 where  
   aux : {u : U × V} {y : Z × T} → _▷ᵣ_ α β u (func-× F G y) ≤₄ _▷ᵣ_ γ φ (func-× f g u) y
   aux {u , v}{z , t} = ▷₄-func {α u (F z)}{γ (f u) z}{β v (G t)}{φ (g v) t} (p1 {u}{z}) (p2 {v}{t})

▷-α : {A B C : Obj} → Hom ((A ▷ B) ▷ C) (A ▷ (B ▷ C))
▷-α {U , X , α}{V , Y , β}{W , Z , γ} = lr-assoc-× , (rl-assoc-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
   cond : {u : (U × V) × W} {y : X × Y × Z} → ((α ▷ᵣ β) ▷ᵣ γ) u (rl-assoc-× y) ≤₄ (α ▷ᵣ (β ▷ᵣ γ)) (lr-assoc-× u) y
   cond {(u , v) , w}{x , y , z} = snd (iso₄-inv (▷₄-assoc {α u x}{β v y}{γ w z}))

▷-α-inv : {A B C : Obj} → Hom (A ▷ (B ▷ C)) ((A ▷ B) ▷ C)
▷-α-inv {U , X , α}{V , Y , β}{W , Z , γ} = rl-assoc-× , (lr-assoc-× , (λ {p₁}{p₂} → cond {p₁}{p₂}))
 where
   cond : {u : U × V × W} {y : (X × Y) × Z} → (α ▷ᵣ (β ▷ᵣ γ)) u (lr-assoc-× y) ≤₄ ((α ▷ᵣ β) ▷ᵣ γ) (rl-assoc-× u) y
   cond {u , v , w}{(x , y) , z} = fst (iso₄-inv (▷₄-assoc {α u x}{β v y}{γ w z}))

▷-α-iso₁ : {A B C : Obj} → ▷-α {A}{B}{C} ○ ▷-α-inv ≡h id {(A ▷ B) ▷ C}
▷-α-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux) , ext-set aux
 where
  aux : {U V W : Set}{a : (U × V) × W} → (rl-assoc-× ∘ lr-assoc-×) a ≡ id-set a
  aux {a = (u , v) , w} = refl

▷-α-iso₂ : {A B C : Obj} → ▷-α-inv {A}{B}{C} ○ ▷-α ≡h id {A ▷ (B ▷ C)}
▷-α-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set aux) , (ext-set aux)
 where
  aux : {U V W : Set}{a : U × V × W} → (lr-assoc-× ∘ rl-assoc-×) a ≡ id-set a
  aux {a = u , v , w} = refl

▷-α-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ▷ₐ g) ▷ₐ h) ○ ▷-α ≡h ▷-α ○ (f ▷ₐ (g ▷ₐ h))
▷-α-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  {W , Z , γ} {W' , Z' , γ'}
  (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set aux₂
 where
  aux₁ : {a : (U × V) × W} → (lr-assoc-× ∘ func-× (func-× f g) h) a ≡ (func-× f (func-× g h) ∘ lr-assoc-×) a
  aux₁ {(u , v) , w} = refl

  aux₂ : {a : X' × Y' × Z'} → (func-× (func-× F G) H ∘ rl-assoc-×) a ≡ (rl-assoc-× ∘ func-× F (func-× G H)) a
  aux₂ {x' , y' , z'} = refl

_⊔ᵣ_ : {U V X Y : Set} → (U → X → Four) → (V → Y → Four) → U ⊎ V → X ⊎ Y → Four
_⊔ᵣ_ α β (inj₁ u) (inj₁ x) = α u x
_⊔ᵣ_ α β (inj₁ u) (inj₂ y) = zero
_⊔ᵣ_ α β (inj₂ v) (inj₁ x) = zero
_⊔ᵣ_ α β (inj₂ v) (inj₂ y) = β v y

_⊔ₒ_ : Obj → Obj → Obj
_⊔ₒ_ (U , X , α) (V , Y , β) = (U ⊎ V) , (X ⊎ Y) , α ⊔ᵣ β

_⊔ₐ_ : {A C B D : Obj} → Hom A C → Hom B D → Hom (A ⊔ₒ B) (C ⊔ₒ D)
_⊔ₐ_ {U , X , α} {V , Y , β} {W , Z , γ} {R , S , φ} (f , F , F-pf) (g , G , G-pf) = ⊎-map f g , (⊎-map F G , (λ {u}{v} → cond {u}{v}))
 where
   cond : {u : U ⊎ W} {y : Y ⊎ S} → (α ⊔ᵣ γ) u (⊎-map F G y) ≤₄ (β ⊔ᵣ φ) (⊎-map f g u) y
   cond {inj₁ u} {inj₁ y} = F-pf
   cond {inj₁ u} {inj₂ s} = triv
   cond {inj₂ w} {inj₁ y} = triv
   cond {inj₂ w} {inj₂ s} = G-pf

⊔-α : ∀{A B C} → Hom ((A ⊔ₒ B) ⊔ₒ C) (A ⊔ₒ (B ⊔ₒ C))
⊔-α {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc-inv , ⊎-assoc , (λ {u y} → cond {u}{y})
 where
   cond : {u : (U ⊎ V) ⊎ W} {y : X ⊎ Y ⊎ Z} →
     (_⊔ᵣ_ (_⊔ᵣ_ α β) γ u (⊎-assoc y)) ≤₄ (_⊔ᵣ_ α (_⊔ᵣ_ β γ) (⊎-assoc-inv u) y)
   cond {inj₁ (inj₁ x)} {inj₁ y} = refl₄ {α x y}
   cond {inj₁ (inj₁ x)} {inj₂ (inj₁ y)} = triv
   cond {inj₁ (inj₁ x)} {inj₂ (inj₂ y)} = triv
   cond {inj₁ (inj₂ x)} {inj₁ y} = triv
   cond {inj₁ (inj₂ x)} {inj₂ (inj₁ y)} = refl₄ {β x y}
   cond {inj₁ (inj₂ x)} {inj₂ (inj₂ y)} = triv
   cond {inj₂ x} {inj₁ y} = triv
   cond {inj₂ x} {inj₂ (inj₁ y)} = triv
   cond {inj₂ x} {inj₂ (inj₂ y)} = refl₄ {γ x y}
   
⊔-α-inv : ∀{A B C} → Hom (A ⊔ₒ (B ⊔ₒ C)) ((A ⊔ₒ B) ⊔ₒ C)
⊔-α-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-assoc , ⊎-assoc-inv , (λ {x y} → cond {x}{y})
 where
  cond : {u : U ⊎ V ⊎ W} {y : (X ⊎ Y) ⊎ Z} →      
      (_⊔ᵣ_ α (_⊔ᵣ_ β γ) u (⊎-assoc-inv y)) ≤₄ (_⊔ᵣ_ (α ⊔ᵣ β) γ (⊎-assoc u) y)
  cond {inj₁ x} {inj₁ (inj₁ y)} = refl₄ {α x y}
  cond {inj₁ x} {inj₁ (inj₂ y)} = triv
  cond {inj₁ x} {inj₂ y} = triv
  cond {inj₂ (inj₁ x)} {inj₁ (inj₁ y)} = triv
  cond {inj₂ (inj₁ x)} {inj₁ (inj₂ y)} = refl₄ {β x y}
  cond {inj₂ (inj₁ x)} {inj₂ y} = triv
  cond {inj₂ (inj₂ x)} {inj₁ (inj₁ y)} = triv
  cond {inj₂ (inj₂ x)} {inj₁ (inj₂ y)} = triv
  cond {inj₂ (inj₂ x)} {inj₂ y} = refl₄ {γ x y}

⊔-α-iso₁ : ∀{A B C} → ⊔-α {A}{B}{C} ○ ⊔-α-inv ≡h id
⊔-α-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₂ , ext-set ⊎-assoc-iso₂

⊔-α-iso₂ : ∀{A B C} → ⊔-α-inv {A}{B}{C} ○ ⊔-α ≡h id
⊔-α-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set ⊎-assoc-iso₁ , ext-set ⊎-assoc-iso₁

⊔-α-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ⊔ₐ g) ⊔ₐ h) ○ ⊔-α ≡h ⊔-α ○ (f ⊔ₐ (g ⊔ₐ h))
⊔-α-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  {W , Z , γ} {W' , Z' , γ'}
  (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set (λ {a} → aux₁ {a})) , ext-set (λ {a} → aux₂ {a})
 where
  aux₁ : {a : (U ⊎ V) ⊎ W} → (⊎-assoc-inv ∘ ⊎-map (⊎-map f g) h) a ≡ (⊎-map f (⊎-map g h) ∘ ⊎-assoc-inv) a
  aux₁ {inj₁ (inj₁ u)} = refl
  aux₁ {inj₁ (inj₂ v)} = refl
  aux₁ {inj₂ w} = refl

  aux₂ : {a : X' ⊎ Y' ⊎ Z'} → (⊎-map (⊎-map F G) H ∘ ⊎-assoc) a ≡ (⊎-assoc ∘ ⊎-map F (⊎-map G H)) a
  aux₂ {inj₁ x} = refl
  aux₂ {inj₂ (inj₁ y)} = refl
  aux₂ {inj₂ (inj₂ z)} = refl

⊔-β : ∀{A B} → Hom (A ⊔ₒ B) (B ⊔ₒ A)
⊔-β {U , X , α}{V , Y , β} = ⊎-sym , ⊎-sym , (λ {u y} → cond {u}{y})
 where
   cond : {u : U ⊎ V} {y : Y ⊎ X} → (_⊔ᵣ_ α β u (⊎-sym y)) ≤₄ (_⊔ᵣ_ β α (⊎-sym u) y)
   cond {inj₁ x} {inj₁ y} = triv
   cond {inj₁ x} {inj₂ y} = refl₄ {α x y}
   cond {inj₂ x} {inj₁ y} = refl₄ {β x y}
   cond {inj₂ x} {inj₂ y} = triv

⊔-β-iso : {A B : Obj} → ⊔-β {A}{B} ○ ⊔-β ≡h id {A ⊔ₒ B}
⊔-β-iso {U , X , α}{V , Y , β} = (ext-set aux) , ext-set aux
 where
  aux : {U V : Set}{a : U ⊎ V} → (⊎-sym ∘ ⊎-sym) a ≡ id-set a
  aux {a = inj₁ u} = refl
  aux {a = inj₂ v} = refl

⊔-β-nat : {A A' B B' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (f ⊔ₐ g) ○ ⊔-β ≡h ⊔-β ○ (g ⊔ₐ f)
⊔-β-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  (f , F , F-pf) (g , G , G-pf) = (ext-set aux₁) , (ext-set aux₂)
 where
  aux₁ : {a : U ⊎ V} → (⊎-sym ∘ ⊎-map f g) a ≡ (⊎-map g f ∘ ⊎-sym) a
  aux₁ {inj₁ u} = refl
  aux₁ {inj₂ v} = refl

  aux₂ : {a : Y' ⊎ X'} → (⊎-map F G ∘ ⊎-sym) a ≡ (⊎-sym ∘ ⊎-map G F) a
  aux₂ {inj₁ y} = refl
  aux₂ {inj₂ x} = refl

⊔-contract : ∀{A : Obj} → Hom (A ⊔ₒ A) A
⊔-contract {U , X , α} = ⊎-codiag , inj₁ , (λ {u y} → cond {u}{y})
 where
  cond : {u : U ⊎ U} {y : X} → (_⊔ᵣ_ α α u (inj₁ y)) ≤₄ (α (⊎-codiag u) y)
  cond {inj₁ u}{x} = refl₄ {α u x}
  cond {inj₂ u}{x} = triv

⊔-contract-nat : {A A' : Obj}
  → (f : Hom A A')
  → (f ⊔ₐ f) ○ ⊔-contract {A'} ≡h ⊔-contract {A} ○ f
⊔-contract-nat {U , X , α}{U' , X' , α'} (f , F , F-pf) = ext-set (λ {a} → aux₁ {a}) , ext-set aux₂
 where
  aux₁ : {a : U ⊎ U} → (⊎-codiag ∘ ⊎-map f f) a ≡ (f ∘ ⊎-codiag) a
  aux₁ {inj₁ u} = refl
  aux₁ {inj₂ u} = refl

  aux₂ : {a : X'} → (⊎-map F F ∘ inj₁) a ≡ (inj₁ ∘ F) a
  aux₂ {a} = refl

⊔-▷-distr : {A B C : Obj} → Hom ((A ⊔ₒ B) ▷ C) ((A ▷ C) ⊔ₒ (B ▷ C))
⊔-▷-distr {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distr , ⊎-×-distr-inv , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ (U ⊎ V) (λ x → W)}
      {y : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} →
      _▷ᵣ_ (_⊔ᵣ_ α β) γ u (⊎-×-distr-inv y)
      ≤₄
      _⊔ᵣ_ (_▷ᵣ_ α γ) (_▷ᵣ_ β γ) (⊎-×-distr u) y
  cond {inj₁ u , w} {inj₁ (a , b)} = refl₄ {α u a ▷₄ γ w b}
  cond {inj₁ u , w} {inj₂ (a , b)} = triv
  cond {inj₂ u , w} {inj₁ (a , b)} = triv
  cond {inj₂ u , w} {inj₂ (a , b)} = refl₄ {β u a ▷₄ γ w b}

⊔-▷-distr-inv-aux₁ : {U W V : Set} → Σ U (λ x → W) ⊎ Σ V (λ x → W) → Σ (U ⊎ V) (λ x → W)
⊔-▷-distr-inv-aux₁ (inj₁ (a , b)) = inj₁ a , b
⊔-▷-distr-inv-aux₁ (inj₂ (a , b)) = inj₂ a , b

⊔-▷-distr-inv-aux₂ : {X Y Z : Set} → Σ (X ⊎ Y) (λ x → Z) → Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)
⊔-▷-distr-inv-aux₂ (inj₁ x , z) = inj₁ (x , z)
⊔-▷-distr-inv-aux₂ (inj₂ y , z) = inj₂ (y , z)
  
⊔-▷-distr-inv : {A B C : Obj} → Hom ((A ▷ C) ⊔ₒ (B ▷ C)) ((A ⊔ₒ B) ▷ C)
⊔-▷-distr-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊔-▷-distr-inv-aux₁ , ⊔-▷-distr-inv-aux₂ , (λ {u y} → cond {u}{y})
 where  
  cond : {u : Σ U (λ x → W) ⊎ Σ V (λ x → W)}
      {y : Σ (X ⊎ Y) (λ x → Z)} →
      _⊔ᵣ_ (_▷ᵣ_ α γ) (_▷ᵣ_ β γ) u (⊔-▷-distr-inv-aux₂ y)
      ≤₄
      _▷ᵣ_
      (_⊔ᵣ_ α β) γ (⊔-▷-distr-inv-aux₁ u) y
  cond {inj₁ (a , b)} {inj₁ x , y} = refl₄ {α a x ▷₄ γ b y}
  cond {inj₁ (a , b)} {inj₂ x , y} = triv
  cond {inj₂ (a , b)} {inj₁ x , y} = triv
  cond {inj₂ (a , b)} {inj₂ x , y} = refl₄ {β a x ▷₄ γ b y}

⊔-▷-distr-iso₁ : {A B C : Obj} → ⊔-▷-distr {A}{B}{C} ○ ⊔-▷-distr-inv ≡h id {(A ⊔ₒ B) ▷ C}
⊔-▷-distr-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
  where
    aux₁ : {a : Σ (U ⊎ V) (λ x → W)} → ⊔-▷-distr-inv-aux₁ (⊎-×-distr a) ≡ a
    aux₁ {inj₁ x , b} = refl
    aux₁ {inj₂ y , b} = refl

    aux₂ : {a : Σ (X ⊎ Y) (λ x → Z)} → ⊎-×-distr-inv (⊔-▷-distr-inv-aux₂ a) ≡ a
    aux₂ {inj₁ x , b} = refl
    aux₂ {inj₂ y , b} = refl

⊔-▷-distr-iso₂ : {A B C : Obj} → ⊔-▷-distr-inv {A}{B}{C} ○ ⊔-▷-distr ≡h id {(A ▷ C) ⊔ₒ (B ▷ C)}
⊔-▷-distr-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → W) ⊎ Σ V (λ x → W)} → ⊎-×-distr (⊔-▷-distr-inv-aux₁ a) ≡ a
   aux₁ {inj₁ (a , b)} = refl
   aux₁ {inj₂ (a , b)} = refl

   aux₂ : {a : Σ X (λ x → Z) ⊎ Σ Y (λ x → Z)} → ⊔-▷-distr-inv-aux₂ (⊎-×-distr-inv a) ≡ a
   aux₂ {inj₁ (a , b)} = refl
   aux₂ {inj₂ (a , b)} = refl

⊔-▷-distr-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ⊔ₐ g) ▷ₐ h) ○ ⊔-▷-distr {A'}{B'}{C'} ≡h ⊔-▷-distr {A}{B}{C} ○ ((f ▷ₐ h) ⊔ₐ (g ▷ₐ h))
⊔-▷-distr-nat
  {U , X , α}  {U' , X' , α'}
  {V , Y , β}  {V' , Y' , β'}
  {W , Z , γ}  {W' , Z' , γ'} (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set (λ {a} → aux₂ {a})
 where
   aux₁ : {a : (U ⊎ V) × W} → (⊎-×-distr ∘ func-× (⊎-map f g) h) a ≡ (⊎-map (func-× f h) (func-× g h) ∘ ⊎-×-distr) a
   aux₁ {inj₁ u , w} = refl
   aux₁ {inj₂ v , w} = refl

   aux₂ : {a : X' × Z' ⊎ Y' × Z'} → (func-× (⊎-map F G) H ∘ ⊎-×-distr-inv) a ≡ (⊎-×-distr-inv ∘ ⊎-map (func-× F H) (func-× G H)) a
   aux₂ {inj₁ (x , z)} = refl
   aux₂ {inj₂ (y , z)} = refl

⊔-▷-distl : {A B C : Obj} → Hom (A ▷ (B ⊔ₒ C)) ((A ▷ B) ⊔ₒ (A ▷ C))
⊔-▷-distl {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distl , (⊎-×-distl-inv , ((λ {u}{v} → cond {u}{v})))
 where
   cond : {u : U × (V ⊎ W)} {y : X × Y ⊎ X × Z} → (α ▷ᵣ (β ⊔ᵣ γ)) u (⊎-×-distl-inv y) ≤₄ ((α ▷ᵣ β) ⊔ᵣ (α ▷ᵣ γ)) (⊎-×-distl u) y
   cond {u , inj₁ v} {inj₁ (x , y)} = refl₄ {α u x ▷₄ β v y}
   cond {u , inj₁ v} {inj₂ (x , z)} = ▷₄-zeror {α u x}
   cond {u , inj₂ w} {inj₁ (x , y)} = ▷₄-zeror {α u x}
   cond {u , inj₂ w} {inj₂ (x , z)} = refl₄ {α u x ▷₄ γ w z}

⊔-▷-distl-inv : {A B C : Obj} → Hom ((A ▷ B) ⊔ₒ (A ▷ C)) (A ▷ (B ⊔ₒ C)) 
⊔-▷-distl-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distl-inv , (⊎-×-distl , ((λ {u}{v} → cond {u}{v})))
 where   
   cond : {u : U × V ⊎ U × W} {y : X × (Y ⊎ Z)} → ((α ▷ᵣ β) ⊔ᵣ (α ▷ᵣ γ)) u (⊎-×-distl y) ≤₄ (α ▷ᵣ (β ⊔ᵣ γ)) (⊎-×-distl-inv u) y
   cond {inj₁ (u , v)} {x , inj₁ y} = refl₄ {α u x ▷₄ β v y}
   cond {inj₁ (u , v)} {x , inj₂ z} = triv
   cond {inj₂ (u , w)} {x , inj₁ y} = triv
   cond {inj₂ (u , w)} {x , inj₂ z} = refl₄ {α u x ▷₄ γ w z}

⊔-▷-distl-iso₁ : {A B C : Obj} → ⊔-▷-distl {A}{B}{C} ○ ⊔-▷-distl-inv {A}{B}{C} ≡h id {A ▷ (B ⊔ₒ C)}
⊔-▷-distl-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set ⊎-×-distl-iso₁) , ext-set ⊎-×-distl-iso₁    

⊔-▷-distl-iso₂ : {A B C : Obj} → ⊔-▷-distl-inv {A}{B}{C} ○ ⊔-▷-distl {A}{B}{C} ≡h id {(A ▷ B) ⊔ₒ (A ▷ C)}
⊔-▷-distl-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set ⊎-×-distl-iso₂) , ext-set ⊎-×-distl-iso₂

⊔-▷-distl-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → (f ▷ₐ (g ⊔ₐ h)) ○ ⊔-▷-distl {A'}{B'}{C'} ≡h ⊔-▷-distl {A}{B}{C} ○ ((f ▷ₐ g) ⊔ₐ (f ▷ₐ h))
⊔-▷-distl-nat
  {U , X , α}  {U' , X' , α'}
  {V , Y , β}  {V' , Y' , β'}
  {W , Z , γ}  {W' , Z' , γ'} (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set (λ {a} → aux₂ {a})
 where
   aux₁ : {a : U × (V ⊎ W)} → (⊎-×-distl ∘ func-× f (⊎-map g h)) a ≡ (⊎-map (func-× f g) (func-× f h) ∘ ⊎-×-distl) a
   aux₁ {u , inj₁ v} = refl
   aux₁ {u , inj₂ w} = refl

   aux₂ : {a : X' × Y' ⊎ X' × Z'} → (func-× F (⊎-map G H) ∘ ⊎-×-distl-inv) a ≡ (⊎-×-distl-inv ∘ ⊎-map (func-× F G) (func-× F H)) a
   aux₂ {inj₁ (x , y)} = refl
   aux₂ {inj₂ (x , z)} = refl

⊔-⊙-distr : {A B C : Obj} → Hom ((A ⊔ₒ B) ⊙ C) ((A ⊙ C) ⊔ₒ (B ⊙ C))
⊔-⊙-distr {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distr , (⊎-×-distr-inv , (λ {u y} → cond {u}{y}))
 where
  cond : {u : (U ⊎ V) × W} {y : X × Z ⊎ Y × Z} → ((α ⊔ᵣ β) ⊙ᵣ γ) u (⊎-×-distr-inv y) ≤₄ ((α ⊙ᵣ γ) ⊔ᵣ (β ⊙ᵣ γ)) (⊎-×-distr u) y
  cond {inj₁ u , w} {inj₁ (x , z)} =  refl₄ {α u x ⊙₄ γ w z} 
  cond {inj₁ u , w} {inj₂ (y , z)} = triv
  cond {inj₂ v , w} {inj₁ (x , z)} = triv
  cond {inj₂ v , w} {inj₂ (y , z)} = refl₄ {β v y ⊙₄ γ w z}

⊔-⊙-distr-inv : {A B C : Obj} → Hom ((A ⊙ C) ⊔ₒ (B ⊙ C)) ((A ⊔ₒ B) ⊙ C)
⊔-⊙-distr-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distr-inv , (⊎-×-distr , (λ {u y} → cond {u}{y}))
 where
   cond : {u : U × W ⊎ V × W} {y : (X ⊎ Y) × Z} → ((α ⊙ᵣ γ) ⊔ᵣ (β ⊙ᵣ γ)) u (⊎-×-distr y) ≤₄ ((α ⊔ᵣ β) ⊙ᵣ γ) (⊎-×-distr-inv u) y
   cond {inj₁ (u , w)} {inj₁ x , z} = refl₄ {α u x ⊙₄ γ w z} 
   cond {inj₁ (v , w)} {inj₂ y , z} = triv
   cond {inj₂ (u , w)} {inj₁ x , z} = triv
   cond {inj₂ (v , w)} {inj₂ y , z} = refl₄ {β v y ⊙₄ γ w z}

⊔-⊙-distr-iso₁ : {A B C : Obj} → ⊔-⊙-distr {A}{B}{C} ○ ⊔-⊙-distr-inv {A}{B}{C} ≡h id {(A ⊔ₒ B) ⊙ C}
⊔-⊙-distr-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set ⊎-×-distr-iso₁) , ext-set ⊎-×-distr-iso₁

⊔-⊙-distr-iso₂ : {A B C : Obj} → ⊔-⊙-distr-inv {A}{B}{C} ○ ⊔-⊙-distr {A}{B}{C} ≡h id {(A ⊙ C) ⊔ₒ (B ⊙ C)}
⊔-⊙-distr-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set ⊎-×-distr-iso₂) , ext-set ⊎-×-distr-iso₂

⊔-⊙-distr-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ⊔ₐ g) ⊙ₐ h) ○ ⊔-⊙-distr {A'}{B'}{C'} ≡h ⊔-⊙-distr {A}{B}{C} ○ ((f ⊙ₐ h) ⊔ₐ (g ⊙ₐ h))
⊔-⊙-distr-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  {W , Z , γ} {W' , Z' , γ'} (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set (λ {a} → aux₂ {a})
 where
  aux₁ : {a : (U ⊎ V) × W} → (⊎-×-distr ∘ ⟨ ⊎-map f g , h ⟩) a ≡ (⊎-map ⟨ f , h ⟩ ⟨ g , h ⟩ ∘ ⊎-×-distr) a
  aux₁ {inj₁ u , w} = refl
  aux₁ {inj₂ v , w} = refl

  aux₂ : {a : X' × Z' ⊎ Y' × Z'} → (func-× (⊎-map F G) H ∘ ⊎-×-distr-inv) a ≡ (⊎-×-distr-inv ∘ ⊎-map (func-× F H) (func-× G H)) a
  aux₂ {inj₁ (x' , z')} = refl
  aux₂ {inj₂ (y' , z')} = refl

⊔-⊙-distl : {A B C : Obj} → Hom (A ⊙ (B ⊔ₒ C)) ((A ⊙ B) ⊔ₒ (A ⊙ C))
⊔-⊙-distl {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distl , (⊎-×-distl-inv , (λ {u}{v} → cond {u}{v}))
 where
   cond : {u : U × (V ⊎ W)} {y : X × Y ⊎ X × Z} → (α ⊙ᵣ (β ⊔ᵣ γ)) u (⊎-×-distl-inv y) ≤₄ ((α ⊙ᵣ β) ⊔ᵣ (α ⊙ᵣ γ)) (⊎-×-distl u) y
   cond {u , inj₁ v} {inj₁ (x , y)} = refl₄ {α u x ⊙₄ β v y}
   cond {u , inj₁ v} {inj₂ (x , z)} = ⊙₄-zeror {α u x}
   cond {u , inj₂ w} {inj₁ (x , y)} = ⊙₄-zeror {α u x}
   cond {u , inj₂ w} {inj₂ (x , z)} = refl₄ {α u x ⊙₄ γ w z}

⊔-⊙-distl-inv : {A B C : Obj} → Hom ((A ⊙ B) ⊔ₒ (A ⊙ C)) (A ⊙ (B ⊔ₒ C)) 
⊔-⊙-distl-inv {U , X , α}{V , Y , β}{W , Z , γ} = ⊎-×-distl-inv , (⊎-×-distl , ((λ {u}{v} → cond {u}{v})))
 where   
   cond : {u : U × V ⊎ U × W} {y : X × (Y ⊎ Z)} → ((α ⊙ᵣ β) ⊔ᵣ (α ⊙ᵣ γ)) u (⊎-×-distl y) ≤₄ (α ⊙ᵣ (β ⊔ᵣ γ)) (⊎-×-distl-inv u) y
   cond {inj₁ (u , v)} {x , inj₁ y} = refl₄ {α u x ⊙₄ β v y}
   cond {inj₁ (u , v)} {x , inj₂ z} = triv
   cond {inj₂ (u , w)} {x , inj₁ y} = triv
   cond {inj₂ (u , w)} {x , inj₂ z} = refl₄ {α u x ⊙₄ γ w z}

⊔-⊙-distl-iso₁ : {A B C : Obj} → ⊔-⊙-distl {A}{B}{C} ○ ⊔-⊙-distl-inv {A}{B}{C} ≡h id {A ⊙ (B ⊔ₒ C)}
⊔-⊙-distl-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set ⊎-×-distl-iso₁) , ext-set ⊎-×-distl-iso₁    

⊔-⊙-distl-iso₂ : {A B C : Obj} → ⊔-⊙-distl-inv {A}{B}{C} ○ ⊔-⊙-distl {A}{B}{C} ≡h id {(A ⊙ B) ⊔ₒ (A ⊙ C)}
⊔-⊙-distl-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = (ext-set ⊎-×-distl-iso₂) , ext-set ⊎-×-distl-iso₂

⊔-⊙-distl-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → (f ⊙ₐ (g ⊔ₐ h)) ○ ⊔-⊙-distl {A'}{B'}{C'} ≡h ⊔-⊙-distl {A}{B}{C} ○ ((f ⊙ₐ g) ⊔ₐ (f ⊙ₐ h))
⊔-⊙-distl-nat
  {U , X , α}  {U' , X' , α'}
  {V , Y , β}  {V' , Y' , β'}
  {W , Z , γ}  {W' , Z' , γ'} (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set (λ {a} → aux₂ {a})
 where
  aux₁ : {a : U × (V ⊎ W)} → (⊎-×-distl ∘ ⟨ f , ⊎-map g h ⟩) a ≡ (⊎-map ⟨ f , g ⟩ ⟨ f , h ⟩ ∘ ⊎-×-distl) a
  aux₁ {u , inj₁ v} = refl
  aux₁ {u , inj₂ w} = refl

  aux₂ : {a : X' × Y' ⊎ X' × Z'} → (func-× F (⊎-map G H) ∘ ⊎-×-distl-inv) a ≡ (⊎-×-distl-inv ∘ ⊎-map (func-× F G) (func-× F H)) a
  aux₂ {inj₁ (x , y)} = refl
  aux₂ {inj₂ (x , z)} = refl

