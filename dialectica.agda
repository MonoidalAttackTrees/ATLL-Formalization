-----------------------------------------------------------------------
-- The definition of the dialectica category GC on Sets              --
-- parameterized by an arbitrary lineale.  GC is described in        --
-- Valeria de Paiva's thesis:                                        --
--   http://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf          --
-----------------------------------------------------------------------
module dialectica where

open import prelude
open import lineale
open import lineale-thms

-----------------------------------------------------------------------
-- Definition of the Category                                        --
-----------------------------------------------------------------------

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (U → X → Four))

obj-fst : Obj → Set
obj-fst (U , X , α) = U

obj-snd : Obj → Set
obj-snd (U , X , α) = X
  
-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (Y → X) ] (∀{u : U}{y : Y} → α u (F y) ≤₄ β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , F ∘ G , cond)
  where
   cond : {u : U} {y : Z} → (α u (F (G y))) ≤₄ (γ (g (f u)) y)
   cond {u}{z} = trans₄ {α u (F (G z))}{β (f u) (G z)} {γ (g (f u)) z} p₁ p₂

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , id-set , (λ {u} {y} → refl₄ {α u y}))

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

≡h-refl : {A B : Obj}{f : Hom A B} → f ≡h f
≡h-refl {U , X , α}{V , Y , β}{f , F , _} = refl , refl

≡h-trans : ∀{A B}{f g h : Hom A B} → f ≡h g → g ≡h h → f ≡h h
≡h-trans {U , X , α}{V , Y , β}{f , F , _}{g , G , _}{h , H , _} (p₁ , p₂) (p₃ , p₄) rewrite p₁ | p₂ | p₃ | p₄ = refl , refl

≡h-sym : ∀{A B}{f g : Hom A B} → f ≡h g → g ≡h f
≡h-sym {U , X , α}{V , Y , β}{f , F , _}{g , G , _} (p₁ , p₂) rewrite p₁ | p₂ = refl , refl

≡h-subst-○ : ∀{A B C}{f₁ f₂ : Hom A B}{g₁ g₂ : Hom B C}{j : Hom A C}
  → f₁ ≡h f₂
  → g₁ ≡h g₂
  → f₂ ○ g₂ ≡h j
  → f₁ ○ g₁ ≡h j
≡h-subst-○ {U , X , α}
           {V , Y , β}
           {W , Z , γ}
           {f₁ , F₁ , _}
           {f₂ , F₂ , _}
           {g₁ , G₁ , _}
           {g₂ , G₂ , _}
           {j , J , _}
           (p₅ , p₆) (p₇ , p₈) (p₉ , p₁₀) rewrite p₅ | p₆ | p₇ | p₈ | p₉ | p₁₀ = refl , refl

○-assoc : ∀{A B C D}{f : Hom A B}{g : Hom B C}{h : Hom C D}
  → f ○ (g ○ h) ≡h (f ○ g) ○ h
○-assoc {U , X , α}{V , Y , β}{W , Z , γ}{S , T , ι}
        {f , F , _}{g , G , _}{h , H , _} = refl , refl

○-idl : ∀{A B}{f : Hom A B} → id ○ f ≡h f
○-idl {U , X , _}{V , Y , _}{f , F , _} = refl , refl

○-idr : ∀{A B}{f : Hom A B} → f ○ id ≡h f
○-idr {U , X , _}{V , Y , _}{f , F , _} = refl , refl

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

-----------------------------------------------------------------------
-- The SMCC Structure                                                --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Four) → (V → Y → Four) → ((U × V) → ((V → X) × (U → Y)) → Four)
_⊗ᵣ_ α β (u , v) (f , g) = (α u (f v)) ⊗₄ (β v (g u))

_⊗_ : (A B : Obj) → Obj
(U , X , α) ⊗ (V , Y , β) = ((U × V) , ((V → X) × (U → Y)) , α ⊗ᵣ β)

F⊗ : ∀{S Z W T V X U Y : Set}{f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → (S → Z) × (W → T) → (V → X) × (U → Y)
F⊗ {f = f}{F}{g}{G} (h₁ , h₂) = (λ v → F(h₁ (g v))) , (λ u → G(h₂ (f u)))
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ B) (C ⊗ D)
_⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {f = f}{F}{g}{G} , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ U (λ x → V)} {y : Σ (S → Z) (λ x → W → T)} →
      ((α ⊗ᵣ β) u (F⊗ {f = f}{F}{g}{G} y)) ≤₄ ((γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y)
  cond {u , v}{h , j} = ⊗₄-func {α u (F (h (g v)))}{γ (f u) (h (g v))}{β v (G (j (f u)))}{δ (g v) (j (f u))} p₁ p₂

-- The unit for tensor:
ι : ⊤ {lzero} → ⊤ {lzero} → Four
ι triv triv = I₄

I : Obj
I = (⊤ , ⊤ , ι)

-- The left-unitor:   
⊗-λ : ∀{A : Obj} → Hom (I ⊗ A) A
⊗-λ {(U , X , α)} = snd , (λ x → (λ _ → triv) , (λ _ → x)) , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ ⊤ (λ x → U)} {y : X} →
      ((ι ⊗ᵣ α) u ((λ _ → triv) , (λ _ → y))) ≤₄ (α (snd u) y)
  cond {triv , u}{x} = fst (iso₄-inv (⊗₄-unitr {α u x}))

⊗-λ-inv : ∀{A : Obj} → Hom A (I ⊗ A)
⊗-λ-inv {(U , X , α)} = (λ u → triv , u) , ((λ x → snd x triv) , (λ {u y} → cond {u}{y}))
 where
  cond : {u : U} {y : Σ (U → ⊤) (λ x → ⊤ → X)} → (α u (snd y triv)) ≤₄ ((ι ⊗ᵣ α) (triv , u) y)
  cond {u}{t₁ , t₂} with t₁ u
  ... | triv = snd (iso₄-inv (⊗₄-unitr {α u (t₂ triv)}))

-- The right-unitor:
⊗-ρ : ∀{A : Obj} → Hom (A ⊗ I) A
⊗-ρ {(U , X , α)} = fst , (λ x → (λ x₁ → x) , (λ x₁ → triv)) , (λ {u y} → cond {u}{y})
 where
  cond : {u : Σ U (λ x → ⊤)} {y : X} → ((α ⊗ᵣ ι) u ((λ x₁ → y) , (λ x₁ → triv))) ≤₄ (α (fst u) y)
  cond {u , triv}{x} = fst (iso₄-inv (⊗₄-unitl {α u x}))

⊗-ρ-inv : ∀{A : Obj} → Hom A (A ⊗ I)
⊗-ρ-inv {(U , X , α)} = (λ x → x , triv) , (λ x → fst x triv) , (λ {u y} → cond {u}{y})
 where
  cond : {u : U} {y : Σ (⊤ → X) (λ x → U → ⊤)} → (α u (fst y triv)) ≤₄ ((α ⊗ᵣ ι) (u , triv) y)
  cond {u}{t₁ , t₂} with t₁ triv | t₂ u
  ... | x | triv = snd (iso₄-inv (⊗₄-unitl {α u x}))

-- Symmetry:
⊗-β : ∀{A B : Obj} → Hom (A ⊗ B) (B ⊗ A)
⊗-β {(U , X , α)}{(V , Y , β)} = twist-× , twist-× , (λ {u y} → cond {u}{y})
 where
   cond : {u : Σ U (λ x → V)} {y : Σ (U → Y) (λ x → V → X)} →
        ((α ⊗ᵣ β) u (twist-× y)) ≤₄ ((β ⊗ᵣ α) (twist-× u) y)
   cond {u , v}{t₁ , t₂} with t₁ u | t₂ v
   ... | x | y = fst (iso₄-inv (⊗₄-sym {α u y}{β v x}))

-- The associator:
Fα : ∀{V W X Y U V Z : Set} → Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))
       → Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)
Fα (f ,  g) = (λ x → (λ x₁ → f ((x₁ , x))) , (λ x₁ → fst (g x₁) x)) , (λ x → snd (g (fst x)) (snd x))

⊗-α : ∀{A B C : Obj} → Hom ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) 
⊗-α {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα {V} , (λ {u y} → cond {u}{y}))
 where
  cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}
      {y : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
      (((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα {V} y)) ≤₄ ((α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y)
  cond {(u , v) , w}{t₁ , t₂} with t₂ u
  ... | t₃ , t₄ with t₁ (v , w) | t₃ w | t₄ v
  ... | x | y | z rewrite ⊗₄-assoc {α u x}{β v y}{γ w z} = refl₄ {α u x ⊗₄ (β v y ⊗₄ γ w z)}
  
⊗-α-inv : ∀{A B C : Obj} → Hom (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
⊗-α-inv {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , (λ {u y} → cond {u}{y})
 where
   Fα-inv : (W → (V → X) × (U → Y)) × (U × V → Z) → (V × W → X) × (U → (W → Y) × (V → Z))
   Fα-inv = (λ p → (λ p' → fst ((fst p) (snd p')) (fst p')) , (λ u → (λ w → snd (fst p w) u) , (λ v → (snd p) (u , v))))
   cond : {u : Σ U (λ x → Σ V (λ x₁ → W))}
      {y : Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)} →        
      ((α ⊗ᵣ (β ⊗ᵣ γ)) u
       ((λ p' → fst (fst y (snd p')) (fst p')) ,
        (λ u₁ → (λ w → snd (fst y w) u₁) , (λ v → snd y (u₁ , v)))))
        ≤₄
      (((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y)
   cond {u , (v , w)}{t₁ , t₂} with t₁ w | t₂ (u , v)
   ... | t₃ , t₄ | z with t₃ v | t₄ u
   ... | x | y rewrite ⊗₄-assoc {α u x}{β v y}{γ w z} = refl₄ {α u x ⊗₄ (β v y ⊗₄ γ w z)}

⊗-α-iso₁ : ∀{A B C} → (⊗-α {A}{B}{C}) ○ ⊗-α-inv ≡h id
⊗-α-iso₁ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ (Σ U (λ x → V)) (λ x → W)} → rl-assoc-× (lr-assoc-× a) ≡ a
   aux {(u , v) , w} = refl

   aux' : {a : Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)}
     → ((λ x → (λ x₁ → fst (fst a x) x₁) , (λ x₁ → snd (fst a x) x₁)) , (λ x → snd a (fst x , snd x))) ≡ a
   aux' {j₁ , j₂} = eq-× (ext-set aux'') (ext-set aux''')
    where
      aux'' : {a : W} → (fst (j₁ a) , snd (j₁ a)) ≡ j₁ a
      aux'' {w} with j₁ w
      ... | h₁ , h₂ = refl

      aux''' : {a : Σ U (λ x₁ → V)} → j₂ (fst a , snd a) ≡ j₂ a
      aux''' {u , v} = refl

⊗-α-iso₂ : ∀{A B C} → (⊗-α-inv {A}{B}{C}) ○ ⊗-α ≡h id
⊗-α-iso₂ {U , X , α}{V , Y , β}{W , Z , γ} = ext-set aux , ext-set aux'
 where
   aux : {a : Σ U (λ x → Σ V (λ x₁ → W))} → lr-assoc-× (rl-assoc-× a) ≡ a
   aux {u , (v , w)} = refl
   aux' : {a
       : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
      ((λ p' → fst (fst (Fα {V} {W} {X} {Y} {U} {V} {Z} a) (snd p')) (fst p')) ,
       (λ u → (λ w → snd (fst (Fα {V} {W} {X} {Y} {U} {V} {Z} a) w) u) , (λ v → snd (Fα {V} {W} {X} {Y} {U} {V} {Z} a) (u , v))))
      ≡ a
   aux' {j₁ , j₂} = eq-× (ext-set aux'') (ext-set aux''')
     where
       aux'' : {a : Σ V (λ x → W)} → j₁ (fst a , snd a) ≡ j₁ a
       aux'' {v , w} = refl
       aux''' : {a : U} → ((λ w → fst (j₂ a) w) , (λ v → snd (j₂ a) v)) ≡ j₂ a
       aux''' {u} with j₂ u
       ... | h₁ , h₂ = refl

-- TODO:
--   β-iso
--   β-nat
--   λ-nat
--   λ-iso
--   ρ-nat
--   ρ-iso
--   α-nat
--   SMC diagrams

-- Internal hom:
⊸-cond : ∀{U V X Y : Set} → (U → X → Four) → (V → Y → Four) → (U → V) × (Y → X) → U × Y → Four
⊸-cond α β (f , g) (u , y) = α u (g y) ⊸₄ β (f u) y

_⊸_ : Obj → Obj → Obj
(U , X , α) ⊸ (V , Y , β) = ((U → V) × (Y → X)) , (U × Y) , ⊸-cond α β

_⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ B) (C ⊸ D)
_⊸ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , (λ {u y} → cond {u}{y})
  where
   h : Σ (U → V) (λ x → Y → X) → Σ (W → S) (λ x → T → Z)
   h (h₁ , h₂) = (λ w → g (h₁ (f w))) , (λ t → F (h₂ (G t)))
   H : Σ W (λ x → T) → Σ U (λ x → Y)
   H (w , t) = f w , G t
   cond : {u : Σ (U → V) (λ x → Y → X)} {y : Σ W (λ x → T)} →
        (⊸-cond α β u (H y)) ≤₄ (⊸-cond γ δ (h u) y)
   cond {t₁ , t₂}{w , t} with p₁ {w}{t₂ (G t)} | p₂ {t₁ (f w)}{t}
   ... | r₁ | r₂ with f w | G t
   ... | u | y with t₁ u | t₂ y
   ... | v | x with F x | g v
   ... | z | s = ⊸₄-func {γ w z}{α u x}{β v y}{δ s t} r₁ r₂

curry : {A B C : Obj}
  → Hom (A ⊗ B) C
  → Hom A (B ⊸ C)
curry {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ u → (λ v → f (u , v)) , (λ z → snd (F z) u)) , (λ p →  fst (F (snd p)) (fst p)) , (λ {u y} → cond {u}{y})
 where
   cond : {u : U} {y : Σ V (λ x → Z)} →
      (α u (fst (F (snd y)) (fst y))) ≤₄ (⊸-cond β γ ((λ v → f (u , v)) , (λ z → snd (F z) u)) y)
   cond {u}{v , z} with p₁ {u , v}{z}
   ... | p₂ with F z
   ... | t₁ , t₂ with t₁ v | t₂ u | f (u , v )
   ... | w | x | y = curry₄ {α u w}{β v x}{γ y z} p₂

curry-≡h : ∀{A B C}{f₁ f₂ : Hom (A ⊗ B) C}
  → f₁ ≡h f₂
  → curry f₁ ≡h curry f₂
curry-≡h {U , X , α}{V , Y , β}{W , Z , γ}
       {f₁ , F₁ , p₁}{f₂ , F₂ , p₂} (p₃ , p₄)
       rewrite p₃ | p₄ = refl , refl

uncurry : {A B C : Obj}
  → Hom A (B ⊸ C)
  → Hom (A ⊗ B) C
uncurry {U , X , α}{V , Y , β}{W , Z , γ} (f , F , p₁)
  = (λ p → fst (f (fst p)) (snd p)) , (λ z → (λ v → F (v , z)) , (λ u → snd (f u) z)) , (λ {u y} → cond {u}{y})
  where
    cond : {u : Σ U (λ x → V)} {y : Z} →
         ((α ⊗ᵣ β) u ((λ v → F (v , y)) , (λ u₁ → snd (f u₁) y))) ≤₄ (γ (fst (f (fst u)) (snd u)) y)
    cond {u , v}{z} with p₁ {u}{v , z}
    ... | p₂ with f u
    ... | t₁ , t₂ with t₁ v | t₂ z | F (v , z)
    ... | w | x | y = curry₄-inv {α u y}{β v x}{γ w z} p₂

curry-iso₁ : ∀{A B C}{f : Hom (A ⊗ B) C} → uncurry (curry f) ≡h f
curry-iso₁ {U , X , α}{V , Y , β}{W , Z , γ}{f , F , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : Σ U (λ x → V)} → f (fst a , snd a) ≡ f a
   aux₁ {u , v} = refl
   
   aux₂ : {a : Z} → ((λ v → fst (F a) v) , (λ u → snd (F a) u)) ≡ F a
   aux₂ {z} with F z
   ... | j₁ , j₂ = refl

curry-iso₂ : ∀{A B C}{g : Hom A (B ⊸ C)} → curry (uncurry g) ≡h g
curry-iso₂ {U , X , α}{V , Y , β}{W , Z , γ}{g , G , p₁} = ext-set aux₁ , ext-set aux₂
 where
   aux₁ : {a : U} → ((λ v → fst (g a) v) , (λ z → snd (g a) z)) ≡ g a
   aux₁ {u} with g u
   ... | (j₁ , j₂) = refl

   aux₂ : {a : Σ V (λ x → Z)} → G (fst a , snd a) ≡ G a
   aux₂ {v , z} = refl
