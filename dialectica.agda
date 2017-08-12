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

open import dialectica-cat
open import dialectica-at-ops

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

⊗-λ-nat : {A A' : Obj}
  → (f : Hom A A')
  → (id {I} ⊗ₐ f) ○ ⊗-λ ≡h ⊗-λ ○ f
⊗-λ-nat
  {U , X , α} {U' , X' , α'}
  (f , F , F-pf) = (ext-set (λ {a} → aux₁ {a})) , (ext-set aux₂)
 where
  aux₁ : {a : ⊤ {lzero} × U} → (snd ∘ ⟨ id-set , f ⟩) a ≡ (f ∘ snd) a
  aux₁ {triv , u} = refl

  aux₂ : {a : X'} → (F⊗ {f = id-set {lzero} {⊤ {lzero}}}{id-set {lzero} {⊤ {lzero}}}{f}{F}
                        ∘ (λ x → (λ _ → triv) , (λ _ → x))) a ≡ ((λ x → (λ _ → triv) , (λ _ → x)) ∘ F) a
  aux₂ {x} = refl

⊗-λ-iso : {A : Obj} → ⊗-λ {A} ○ ⊗-λ-inv ≡h id {I ⊗ A}
⊗-λ-iso {U , X , α} = (ext-set aux₁) , ext-set aux₂
 where
   aux₁ : {a : ⊤ {lzero} × U} → (_,_ triv ∘ snd) a ≡ id-set a
   aux₁ {triv , u} = refl

   aux₂ : {a : (U → ⊤ {lzero}) × (⊤ {lzero} → X)} → ((λ x → (λ _ → triv) , (λ _ → x)) ∘ (λ x → snd x triv)) a ≡ id-set a
   aux₂ {t₁ , t₂} = eq-× (ext-set aux₃) (ext-set aux₄)
    where
     aux₃ : {a : U} → triv ≡ t₁ a
     aux₃ {u} with t₁ u
     ... | triv = refl

     aux₄ : {a : ⊤} → t₂ triv ≡ t₂ a
     aux₄ {triv} = refl
     

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

⊗-ρ-nat : {A A' : Obj}
  → (f : Hom A A')
  → (f ⊗ₐ id {I}) ○ ⊗-ρ ≡h ⊗-ρ ○ f
⊗-ρ-nat
  {U , X , α} {U' , X' , α'}
  (f , F , F-pf) = (ext-set (λ {a} → aux₁ {a})) , ext-set aux₂
 where
   aux₁ : {a : U × ⊤ {lzero}} → (fst ∘ ⟨ f , id-set ⟩) a ≡ (f ∘ fst) a
   aux₁ {u , triv} = refl

   aux₂ : {a : X'} →
     ((F⊗ {f = f} {F} {id-set {lzero} {⊤ {lzero}}} {id-set {lzero} {⊤ {lzero}}})
     ∘ (λ x → (λ x₁ → x) , (λ x₁ → triv))) a ≡ ((λ x → (λ x₁ → x) , (λ x₁ → triv)) ∘ F) a
   aux₂ {x} = refl

⊗-ρ-iso : {A : Obj} → ⊗-ρ {A} ○ ⊗-ρ-inv ≡h id {A ⊗ I}
⊗-ρ-iso {U , X , α} = (ext-set aux₁) , ext-set aux₂
 where
   aux₁ : {a : U × (⊤ {lzero})} → ((λ x → x , triv) ∘ fst) a ≡ id-set a
   aux₁ {u , triv} = refl

   aux₂ : {a : ((⊤ {lzero}) → X) × (U → ⊤ {lzero})} → ((λ x → (λ x₁ → x) , (λ x₁ → triv)) ∘ (λ x → fst x triv)) a ≡ id-set a
   aux₂ {t₁ , t₂} = eq-× (ext-set aux₃) (ext-set aux₄)
     where
      aux₃ : {a : ⊤} → t₁ triv ≡ t₁ a
      aux₃ {triv} = refl

      aux₄ : {a : U} → triv ≡ t₂ a
      aux₄ {u} with t₂ u
      ... | triv = refl

-- Symmetry:
⊗-β : ∀{A B : Obj} → Hom (A ⊗ B) (B ⊗ A)
⊗-β {(U , X , α)}{(V , Y , β)} = twist-× , twist-× , (λ {u y} → cond {u}{y})
 where
   cond : {u : Σ U (λ x → V)} {y : Σ (U → Y) (λ x → V → X)} →
        ((α ⊗ᵣ β) u (twist-× y)) ≤₄ ((β ⊗ᵣ α) (twist-× u) y)
   cond {u , v}{t₁ , t₂} with t₁ u | t₂ v
   ... | x | y = fst (iso₄-inv (⊗₄-sym {α u y}{β v x}))

⊗-β-nat : {A A' B B' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (f ⊗ₐ g) ○ ⊗-β ≡h ⊗-β ○ (g ⊗ₐ f)
⊗-β-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  (f , F , F-pf) (g , G , G-pf) = (ext-set aux₁) , (ext-set aux₂)
 where
   aux₁ : {a : U × V} → (twist-× ∘ ⟨ f , g ⟩) a ≡ (⟨ g , f ⟩ ∘ twist-×) a
   aux₁ {u , v} = refl

   aux₂ : {a : (U' → Y') × (V' → X')} → (F⊗ {f = f}{F}{g}{G} ∘ twist-×) a ≡ (twist-× ∘ (F⊗ {f = g}{G}{f}{F})) a
   aux₂ {t₁ , t₂} = refl

⊗-β-iso : {A B : Obj} → ⊗-β {A}{B} ○ ⊗-β ≡h id {A ⊗ B}
⊗-β-iso {U , X , α}{V , Y , β} = (ext-set twist-×-iso) , ext-set twist-×-iso    

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

⊗-α-nat : {A A' B B' C C' : Obj}
  → (f : Hom A A')
  → (g : Hom B B')
  → (h : Hom C C')
  → ((f ⊗ₐ g) ⊗ₐ h) ○ ⊗-α ≡h ⊗-α ○ (f ⊗ₐ (g ⊗ₐ h))
⊗-α-nat
  {U , X , α} {U' , X' , α'}
  {V , Y , β} {V' , Y' , β'}
  {W , Z , γ} {W' , Z' , γ'}
  (f , F , F-pf) (g , G , G-pf) (h , H , H-pf) = (ext-set aux₁) , ext-set aux₂
 where
   aux₁ : {a : (U × V) × W} → (lr-assoc-× ∘ ⟨ ⟨ f , g ⟩ , h ⟩) a ≡ (⟨ f , ⟨ g , h ⟩ ⟩ ∘ lr-assoc-×) a
   aux₁ {(u , v) , w} = refl

   aux₂ : {a : (V' × W' → X') × (U' → (W' → Y') × (V' → Z'))} →
     (F⊗ {f = ⟨ f , g ⟩}
         {F⊗ {V'} {X'} {U'} {Y'} {V} {X} {U} {Y} {f} {F} {g} {G}}
         {h}
         {H}
     ∘
     Fα {V'} {W'} {X'} {Y'} {U'} {V'} {Z'}) a
     ≡
     (Fα {V} {W} {X} {Y} {U} {V} {Z}
     ∘
     F⊗ {f = f}
        {F}
        {⟨ g , h ⟩}
        {F⊗ {W'} {Y'} {V'} {Z'} {W} {Y} {V} {Z} {g} {G} {h} {H}}) a
   aux₂ {t₁ , t₂} = eq-× (ext-set aux₃) (ext-set (λ {a} → aux₄ {a}))
    where
      aux₃ : {a : W} → _≡_ {lzero} {_×_ {lzero} {lzero} (V → X) (U → Y)}
       ((λ v → F (t₁ (g v , h a))) , (λ u → G (fst {lzero} {lzero} {W' → Y'} {V' → Z'} (t₂ (f u)) (h a))))
       ((λ x₁ → F (t₁ (g x₁ , h a))) ,
        (λ x₁ →
           fst {lzero} {lzero} {W → Y} {V → Z}
           (F⊗ {W'} {Y'} {V'} {Z'} {W} {Y} {V} {Z} {g} {G} {h} {H}
            (t₂ (f x₁)))
           a))
      aux₃ {w} = eq-× refl (ext-set aux₄)
       where
         aux₄ : {a : U} →  _≡_ {lzero} {Y}
           (G (fst {lzero} {lzero} {W' → Y'} {V' → Z'} (t₂ (f a)) (h w)))
           (fst {lzero} {lzero} {W → Y} {V → Z} (F⊗ {W'} {Y'} {V'} {Z'} {W} {Y} {V} {Z} {g} {G} {h} {H} (t₂ (f a))) w)
         aux₄ {u} with t₂ (f u)
         aux₄ {a} | x , y = refl

      aux₄ : {a : U × V} → (H (snd (t₂ (fst (⟨ f , g ⟩ a))) (snd (⟨ f , g ⟩ a)))) ≡ (snd (F⊗ {f = g} {G} {h} {H} (t₂ (f (fst a)))) (snd a))
      aux₄ {u , v} with t₂ (f u)
      ... | x , y = refl

-- TODO:
--   SMC diagrams

pentagon : {A B C D : Obj} → (⊗-α {A}{B}{C} ⊗ₐ id {D}) ○ ⊗-α {A}{B ⊗ C}{D} ○ (id {A} ⊗ₐ ⊗-α {B}{C}{D}) ≡h ⊗-α {A ⊗ B}{C}{D} ○ ⊗-α {A}{B}{C ⊗ D}
pentagon {U , X , α} {V , Y , β} {W , Z , γ} {R , S , φ} = (ext-set aux₁) , ext-set aux₂
 where
   aux₁ : {a : ((U × V) × W) × R} → (⟨ id-set , lr-assoc-× ⟩ ∘ (lr-assoc-× ∘ ⟨ lr-assoc-× , id-set ⟩)) a ≡ (lr-assoc-× ∘ lr-assoc-×) a
   aux₁ {((u , v) , w) , r} = refl

   aux₂ : {a : (V × W × R → X) × (U → (W × R → Y) × (V → (R → Z) × (W → S)))}
     → ((F⊗ {f = lr-assoc-× {lzero} {lzero} {lzero} {U} {V} {W}}
            {Fα {V} {W} {X} {Y} {U} {V} {Z}}
            {id-set {lzero} {R}}{id-set {lzero} {S}}
         ∘
         Fα {V × W}{R}{X}{(W → Y) × (V → Z)}{U}{V × W}{S})
         ∘
         F⊗ {f = id-set {lzero} {U}}
            {id-set {lzero} {X}}
            {lr-assoc-× {lzero} {lzero} {lzero} {V} {W} {R}}
            {Fα {W} {R} {Y} {Z} {V} {W} {S}}) a
         ≡
         (Fα {W} {R} {(V → X) × (U → Y)} {Z}
             {U × V} {W} {S}
          ∘
          Fα {V} {W × R} {X}
             {Y} {U} {V} {(R → Z) × (W → S)}) a
   aux₂ {t₁ , t₂} = eq-× (ext-set aux₃) (ext-set (λ {a} → aux₈ {a}))
    where
     aux₃ : {a : R} →
       _≡_ {lzero}
       {Σ {lzero} {lzero} (W → Σ {lzero} {lzero} (V → X) (λ x → U → Y))
         (λ x → Σ {lzero} {lzero} U (λ x₁ → V) → Z)}
       ((λ x →
           (λ x₁ → id-set {lzero} {X} (t₁ (x₁ , x , id-set {lzero} {R} a))) ,
           (λ x₁ →
              fst {lzero} {lzero} {W → Y} {V → Z}
              (fst {lzero} {lzero} {R → _×_ {lzero} {lzero} (W → Y) (V → Z)}
                {_×_ {lzero} {lzero} V W → S}
                (Fα {W} {R} {Y} {Z} {V} {W} {S} (t₂ (id-set {lzero} {U} x₁)))
                (id-set {lzero} {R} a))
              x))
           ,
           (λ x →
           snd {lzero} {lzero} {W → Y} {V → Z}
           (fst {lzero} {lzero} {R → _×_ {lzero} {lzero} (W → Y) (V → Z)}
             {_×_ {lzero} {lzero} V W → S}
             (Fα {W} {R} {Y} {Z} {V} {W} {S}
             (t₂ (id-set {lzero} {U} (fst {lzero} {lzero} {U} {V} x))))
             (id-set {lzero} {R} a))
           (snd {lzero} {lzero} {U} {V} x)))
       ((λ x₁ →
           (λ x₂ → t₁ (x₂ , x₁ , a)) ,
           (λ x₂ →
              fst {lzero} {lzero} {_×_ {lzero} {lzero} W R → Y}
              {V → _×_ {lzero} {lzero} (R → Z) (W → S)} (t₂ x₂) (x₁ , a)))
           ,
           (λ x₁ →
           fst {lzero} {lzero} {R → Z} {W → S}
           (snd {lzero} {lzero} {_×_ {lzero} {lzero} W R → Y}
             {V → _×_ {lzero} {lzero} (R → Z) (W → S)}
             (t₂ (fst {lzero} {lzero} {U} {V} x₁))
             (snd {lzero} {lzero} {U} {V} x₁))
           a))
     aux₃ {x} = eq-× (ext-set aux₄) (ext-set (λ {a} → aux₇ {a}))
      where
       aux₄ : {a : W} →
         _≡_ {lzero} {Σ {lzero} {lzero} (V → X) (λ x₁ → U → Y)}
         ((λ x₁ → id-set {lzero} {X} (t₁ (x₁ , a , id-set {lzero} {R} x))) ,
           (λ x₁ →
             fst {lzero} {lzero} {W → Y} {V → Z}
             (fst {lzero} {lzero} {R → _×_ {lzero} {lzero} (W → Y) (V → Z)}
               {_×_ {lzero} {lzero} V W → S}
               (Fα {W} {R} {Y} {Z} {V} {W} {S} (t₂ (id-set {lzero} {U} x₁)))
               (id-set {lzero} {R} x))
             a))
         ((λ x₂ → t₁ (x₂ , a , x)) ,
           (λ x₂ →
             fst {lzero} {lzero} {_×_ {lzero} {lzero} W R → Y}
             {V → _×_ {lzero} {lzero} (R → Z) (W → S)} (t₂ x₂) (a , x)))
       aux₄ {w} = eq-× (ext-set aux₅) (ext-set aux₆) 
        where
         aux₅ : {a : V} → id-set (t₁ (a , w , id-set x)) ≡ t₁ (a , w , x)
         aux₅ {v} = refl

         aux₆ : {a : U} → fst (fst (Fα {W} {R} {Y} {Z} {V} {W} {S} (t₂ (id-set a))) (id-set x)) w ≡ fst (t₂ a) (w , x)
         aux₆ {u} with t₂ u
         aux₆ {a} | r₁ , r₂ = refl
         
       aux₇ : {a : Σ {lzero} {lzero} U (λ x₁ → V)} →
         _≡_ {lzero} {Z}
         (snd {lzero} {lzero} {W → Y} {V → Z}
           (fst {lzero} {lzero} {R → _×_ {lzero} {lzero} (W → Y) (V → Z)}
           {_×_ {lzero} {lzero} V W → S}
           (Fα {W} {R} {Y} {Z} {V} {W} {S}
             (t₂ (id-set {lzero} {U} (fst {lzero} {lzero} {U} {V} a))))
           (id-set {lzero} {R} x))
           (snd {lzero} {lzero} {U} {V} a))
         (fst {lzero} {lzero} {R → Z} {W → S}
           (snd {lzero} {lzero} {_×_ {lzero} {lzero} W R → Y}
           {V → _×_ {lzero} {lzero} (R → Z) (W → S)}
           (t₂ (fst {lzero} {lzero} {U} {V} a))
           (snd {lzero} {lzero} {U} {V} a))
           x)
       aux₇ {u , v} with t₂ u
       aux₇ {u , v} | r₁ , r₂ = refl
       
     aux₈ : {a : (U × V) × W} → id-set (snd (Fα {W} {R} {Y} {Z} {V} {W} {S} (t₂ (id-set (fst (lr-assoc-× a)))))
                                       (snd (lr-assoc-× a))) ≡ snd (snd (t₂ (fst (fst a))) (snd (fst a))) (snd a)
     aux₈ {(u , v) , w} with t₂ u
     ... | r₁ , r₂ = refl

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
