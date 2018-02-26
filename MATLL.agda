module MATLL where

open import nat

data Form : Set where
  N   : ℕ → Form
  _⊔_ : Form → Form → Form
  _⊙_ : Form → Form → Form
  _▷_ : Form → Form → Form
  
data Ctx : Set where
  *-◼ : Ctx
  *-∙ : Ctx
  *-▷ : Ctx
  el  : Form → Ctx
  _◼_ : Ctx → Ctx → Ctx
  _∙_ : Ctx → Ctx → Ctx
  _▷_ : Ctx → Ctx → Ctx

data HCtx : Set where
  hole : HCtx
  elH  : Form → HCtx
  _◼H_ : HCtx → HCtx → HCtx
  _∙H_ : HCtx → HCtx → HCtx
  _▷H_ : HCtx → HCtx → HCtx

_⟨_⟩ : HCtx → Ctx → Ctx
hole ⟨ Δ ⟩ = Δ
(elH A) ⟨ _ ⟩ = el A
(Γ₁ ◼H Γ₂) ⟨ Δ ⟩ = (Γ₁ ⟨ Δ ⟩) ◼ (Γ₂ ⟨ Δ ⟩)
(Γ₁ ∙H Γ₂) ⟨ Δ ⟩ = (Γ₁ ⟨ Δ ⟩) ∙ (Γ₂ ⟨ Δ ⟩)
(Γ₁ ▷H Γ₂) ⟨ Δ ⟩ = (Γ₁ ⟨ Δ ⟩) ▷ (Γ₂ ⟨ Δ ⟩)

data _⊨_ : Ctx → Ctx → Set where
  *r-◼ : ∀{Γ} → (Γ ◼ *-◼) ⊨ Γ
  *r-∙ : ∀{Γ} → (Γ ∙ *-∙) ⊨ Γ
  *r-▷ : ∀{Γ} → (Γ ▷ *-▷) ⊨ Γ
  *l-◼ : ∀{Γ} → (*-◼ ◼ Γ) ⊨ Γ
  *l-∙ : ∀{Γ} → (*-∙ ∙ Γ) ⊨ Γ
  *l-▷ : ∀{Γ} → (*-▷ ▷ Γ) ⊨ Γ
  assoc-◼ : ∀{Γ₁ Γ₂ Γ₃} → ((Γ₁ ◼ Γ₂) ◼ Γ₃) ⊨ (Γ₁ ◼ (Γ₂ ◼ Γ₃))
  assoc-∙ : ∀{Γ₁ Γ₂ Γ₃} → ((Γ₁ ∙ Γ₂) ∙ Γ₃) ⊨ (Γ₁ ∙ (Γ₂ ∙ Γ₃))
  assoc-▷ : ∀{Γ₁ Γ₂ Γ₃} → ((Γ₁ ▷ Γ₂) ▷ Γ₃) ⊨ (Γ₁ ▷ (Γ₂ ▷ Γ₃))
  sym-◼ : ∀{Γ Δ₁ Δ₂} → (Γ ⟨ Δ₁ ◼ Δ₂ ⟩) ⊨ ((Γ ⟨ Δ₂ ◼ Δ₁ ⟩))
  sym-∙ : ∀{Γ Δ₁ Δ₂} → (Γ ⟨ Δ₁ ∙ Δ₂ ⟩) ⊨ ((Γ ⟨ Δ₂ ∙ Δ₁ ⟩))
  -- Ideal Axioms:
  -- Filter Axioms:
  intr₀ : ∀{Γ Δ₁ Δ₂ Δ₃ Δ₄} → (Γ ⟨ (Δ₁ ▷ Δ₃) ∙ (Δ₂ ▷ Δ₄) ⟩) ⊨ (Γ ⟨ (Δ₁ ∙ Δ₂) ▷ (Δ₃ ∙ Δ₄) ⟩)
  dist₁ : ∀{Γ Δ₁ Δ₂ Δ₃ Δ₄} → (Γ ⟨ (Δ₁ ◼ Δ₃) ▷ (Δ₂ ◼ Δ₄) ⟩) ⊨ (Γ ⟨ (Δ₁ ▷ Δ₂) ◼ (Δ₃ ▷ Δ₄) ⟩)
  dist₂ : ∀{Γ Δ₁ Δ₂ Δ₃ Δ₄} → (Γ ⟨ (Δ₁ ▷ Δ₂) ◼ (Δ₃ ▷ Δ₄) ⟩) ⊨ (Γ ⟨ (Δ₁ ◼ Δ₃) ▷ (Δ₂ ◼ Δ₄) ⟩)
  dist₃ : ∀{Γ Δ₁ Δ₂ Δ₃ Δ₄} → (Γ ⟨ (Δ₁ ◼ Δ₃) ∙ (Δ₂ ◼ Δ₄) ⟩) ⊨ (Γ ⟨ (Δ₁ ∙ Δ₂) ◼ (Δ₃ ∙ Δ₄) ⟩)
  dist₄ : ∀{Γ Δ₁ Δ₂ Δ₃ Δ₄} → (Γ ⟨ (Δ₁ ∙ Δ₂) ◼ (Δ₃ ∙ Δ₄) ⟩) ⊨ (Γ ⟨ (Δ₁ ◼ Δ₃) ∙ (Δ₂ ◼ Δ₄) ⟩)
  weak : ∀{Γ Δ₁ Δ₂} → ((Γ ⟨ Δ₁ ⟩) ⊨ (Γ ⟨ Δ₁ ◼ Δ₂ ⟩))
  contract : ∀{Γ Δ} → (Γ ⟨ Δ ◼ Δ ⟩) ⊨ (Γ ⟨ Δ ⟩)

data _⊢_ : Ctx → Form → Set where
  id : ∀{A} → (el A ⊢ A)
  CM : ∀{Γ₁ Γ₂ A} → (Γ₁ ⊨ Γ₂) → (Γ₂ ⊢ A) → (Γ₁ ⊢ A)
  ⊔i : ∀{Γ A Δ B} → (Γ ⊢ A) → (Δ ⊢ B) → ((Γ ◼ Δ) ⊢ (A ⊔ B))
  ⊙i : ∀{Γ A Δ B} → (Γ ⊢ A) → (Δ ⊢ B) → ((Γ ∙ Δ) ⊢ (A ⊙ B))
  ▷i : ∀{Γ A Δ B} → (Γ ⊢ A) → (Δ ⊢ B) → ((Γ ▷ Δ) ⊢ (A ▷ B))
  ⊔e : ∀{ Γ A B Δ C} → (Γ ⊢ (A ⊔ B)) → ((Δ ⟨ (el A) ◼ (el B) ⟩) ⊢ C) → ((Δ ⟨ Γ ⟩) ⊢ C)
  ⊙e : ∀{ Γ A B Δ C} → (Γ ⊢ (A ⊙ B)) → ((Δ ⟨ (el A) ∙ (el B) ⟩) ⊢ C) → ((Δ ⟨ Γ ⟩) ⊢ C)
  ▷e : ∀{ Γ A B Δ C} → (Γ ⊢ (A ▷ B)) → ((Δ ⟨ (el A) ▷ (el B) ⟩) ⊢ C) → ((Δ ⟨ Γ ⟩) ⊢ C)

assoc-⊔ : ∀{A B C} → (el ((A ⊔ B) ⊔ C)) ⊢ (A ⊔ (B ⊔ C))
assoc-⊔ {A}{B}{C} = ⊔e {el ((A ⊔ B) ⊔ C)} {A ⊔ B} {C} {hole} id
  (⊔e {el (A ⊔ B)} {A} {B} {hole ◼H elH C} id
    (CM {(el A ◼ el B) ◼ el C} {el A ◼ (el B ◼ el C)} assoc-◼
      (⊔i id (⊔i id id))))

assoc-⊙ : ∀{A B C} → (el ((A ⊙ B) ⊙ C)) ⊢ (A ⊙ (B ⊙ C))
assoc-⊙ {A}{B}{C} = ⊙e {el ((A ⊙ B) ⊙ C)} {A ⊙ B} {C} {hole} id
  (⊙e {el (A ⊙ B)} {A} {B} {hole ∙H elH C} id
    (CM {(el A ∙ el B) ∙ el C} {el A ∙ (el B ∙ el C)} assoc-∙
      (⊙i id (⊙i id id))))

assoc-▷' : ∀{A B C} → (el ((A ▷ B) ▷ C)) ⊢ (A ▷ (B ▷ C))
assoc-▷' {A}{B}{C} = ▷e {el ((A ▷ B) ▷ C)} {A ▷ B} {C} {hole} id
  (▷e {el (A ▷ B)} {A} {B} {hole ▷H elH C} id
    (CM {(el A ▷ el B) ▷ el C} {el A ▷ (el B ▷ el C)} assoc-▷
      (▷i id (▷i id id))))

sym-⊔ : ∀{A B} → (el (A ⊔ B)) ⊢ (B ⊔ A)
sym-⊔ {A}{B} = ⊔e {el (A ⊔ B)} {A} {B} {hole} {B ⊔ A} id (CM {el A ◼ el B} {el B ◼ el A} {B ⊔ A} (sym-◼ {hole})
  (⊔i id id))

sym-⊙ : ∀{A B} → (el (A ⊙ B)) ⊢ (B ⊙ A)
sym-⊙ {A}{B} = ⊙e {el (A ⊙ B)} {A} {B} {hole} {B ⊙ A} id (CM {el A ∙ el B} {el B ∙ el A} {B ⊙ A} (sym-∙ {hole})
  (⊙i id id))

-- Connecting parallel and sequential conjunction (not provable from
-- the basic system):
-- 
-- wdist₁ : ∀{A B C}   → (el ((A ⊙ B) ▷ C)) ⊢ (A ⊙ (B ▷ C))
-- wdist₂ : ∀{A B C}   → (el (A ▷ (B ⊙ C))) ⊢ (A ▷ B) ⊙ C)
-- ▷-⊙    : ∀{A B}     → (el (A ▷ B)) ⊢ (A ⊙ B)

-- Uses weakening:
dist₁-pf : ∀{A B C} → (el (A ▷ (B ⊔ C))) ⊢ ((A ▷ B) ⊔ (A ▷ C))
dist₁-pf {A}{B}{C} =
  ▷e {el (A ▷ (B ⊔ C))} {A} {B ⊔ C} {hole} id
     (⊔e {el (B ⊔ C)} {B} {C} {elH A ▷H hole} id
         (CM {el A ▷ (el B ◼ el C)} {(el A ◼ el A) ▷ (el B ◼ el C)} (weak {hole ▷H (elH B ◼H elH C)})
             (CM {(el A ◼ el A) ▷ (el B ◼ el C)} {(el A ▷ el B) ◼ (el A ▷ el C)}
                (dist₁ {hole}{el A}{el B}{el A}{el C})
                (⊔i (▷i id id) (▷i id id)))))

dist₅-pf : ∀{A B C} → (el ((A ⊔ B) ▷ C)) ⊢ ((A ▷ C) ⊔ (B ▷ C))
dist₅-pf {A}{B}{C} = ▷e {el ((A ⊔ B) ▷ C)} {A ⊔ B} {C} {hole} id
  (⊔e {el (A ⊔ B)} {A} {B} {hole ▷H elH C} id
    (CM {(el A ◼ el B) ▷ el C} {(el A ◼ el B) ▷ (el C ◼ el C)} (weak {(elH A ◼H elH B) ▷H hole})
      (CM {(el A ◼ el B) ▷ (el C ◼ el C)} {(el A ▷ el C) ◼ (el B ▷ el C)}
         (dist₁ {hole}) (⊔i (▷i id id) (▷i id id)))))

dist₇-pf : ∀{A B C} → (el ((A ⊔ B) ⊙ C)) ⊢ ((A ⊙ C) ⊔ (B ⊙ C))
dist₇-pf {A}{B}{C} = ⊙e {el ((A ⊔ B) ⊙ C)} {A ⊔ B} {C} {hole} id
  (⊔e {el (A ⊔ B)} {A} {B} {hole ∙H elH C} id
    (CM {(el A ◼ el B) ∙ el C} {(el A ◼ el B) ∙ (el C ◼ el C)} (weak {(elH A ◼H elH B) ∙H hole})
      (CM {(el A ◼ el B) ∙ (el C ◼ el C)} {(el A ∙ el C) ◼ (el B ∙ el C)}
         (dist₃ {hole}) (⊔i (⊙i id id) (⊙i id id)))))

dist₃-pf : ∀{A B C} → (el (A ⊙ (B ⊔ C))) ⊢ ((A ⊙ B) ⊔ (A ⊙ C))
dist₃-pf {A}{B}{C} =
  ⊙e {el (A ⊙ (B ⊔ C))} {A} {B ⊔ C} {hole} id
     (⊔e {el (B ⊔ C)} {B} {C} {elH A ∙H hole} id
         (CM {el A ∙ (el B ◼ el C)} {(el A ◼ el A) ∙ (el B ◼ el C)} (weak {hole ∙H (elH B ◼H elH C)})
             (CM {(el A ◼ el A) ∙ (el B ◼ el C)} {(el A ∙ el B) ◼ (el A ∙ el C)}
                (dist₃ {hole}{el A}{el B}{el A}{el C})
                (⊔i (⊙i id id) (⊙i id id)))))

-- Uses contraction:
dist₂-pf : ∀{A B C} → (el ((A ▷ B) ⊔ (A ▷ C))) ⊢ (A ▷ (B ⊔ C))
dist₂-pf {A}{B}{C} =
  ⊔e {el ((A ▷ B) ⊔ (A ▷ C))} {A ▷ B} {A ▷ C} {hole} id
     (▷e {el (A ▷ B)} {A} {B} {hole ◼H elH (A ▷ C)} id
       (▷e {el (A ▷ C)} {A} {C} {(elH A ▷H elH B) ◼H hole} id
         (CM {(el A ▷ el B) ◼ (el A ▷ el C)} {(el A ◼ el A) ▷ (el B ◼ el C)}
            (dist₂ {hole}{el A}{el B}{el A}{el C})
            (CM {(el A ◼ el A) ▷ (el B ◼ el C)} {el A ▷ (el B ◼ el C)}
              (contract {hole ▷H ((elH B) ◼H (elH C))}{el A})
              (▷i id (⊔i id id))))))

dist₄-pf : ∀{A B C} → (el ((A ⊙ B) ⊔ (A ⊙ C))) ⊢ (A ⊙ (B ⊔ C))
dist₄-pf {A}{B}{C} =
  ⊔e {el ((A ⊙ B) ⊔ (A ⊙ C))} {A ⊙ B} {A ⊙ C} {hole} id
     (⊙e {el (A ⊙ B)} {A} {B} {hole ◼H elH (A ⊙ C)} id
       (⊙e {el (A ⊙ C)} {A} {C} {(elH A ∙H elH B) ◼H hole} id
         (CM {(el A ∙ el B) ◼ (el A ∙ el C)} {(el A ◼ el A) ∙ (el B ◼ el C)}
            (dist₄ {hole}{el A}{el B}{el A}{el C})
            (CM {(el A ◼ el A) ∙ (el B ◼ el C)} {el A ∙ (el B ◼ el C)}
              (contract {hole ∙H ((elH B) ◼H (elH C))}{el A})
              (⊙i id (⊔i id id))))))

dist₆-pf : ∀{A B C} → (el ((A ▷ C) ⊔ (B ▷ C))) ⊢ ((A ⊔ B) ▷ C)
dist₆-pf {A}{B}{C} = ⊔e {el ((A ▷ C) ⊔ (B ▷ C))} {A ▷ C} {B ▷ C} {hole} id
  (▷e {el (A ▷ C)} {A} {C} {hole ◼H elH (B ▷ C)} id
    (▷e {el (B ▷ C)} {B} {C} {(elH A ▷H elH C) ◼H hole} id
      (CM {(el A ▷ el C) ◼ (el B ▷ el C)} {(el A ◼ el B) ▷ (el C ◼ el C)}
         (dist₂ {hole})
         (CM {(el A ◼ el B) ▷ (el C ◼ el C)} {(el A ◼ el B) ▷ el C} (contract {(elH A ◼H elH B) ▷H hole})
           (▷i (⊔i id id) id)))))

dist₈-pf : ∀{A B C} → (el ((A ⊙ C) ⊔ (B ⊙ C))) ⊢ ((A ⊔ B) ⊙ C)
dist₈-pf {A}{B}{C} = ⊔e {el ((A ⊙ C) ⊔ (B ⊙ C))} {A ⊙ C} {B ⊙ C} {hole} id
  (⊙e {el (A ⊙ C)} {A} {C} {hole ◼H elH (B ⊙ C)} id
    (⊙e {el (B ⊙ C)} {B} {C} {(elH A ∙H elH C) ◼H hole} id
      (CM {(el A ∙ el C) ◼ (el B ∙ el C)} {(el A ◼ el B) ∙ (el C ◼ el C)}
         (dist₄ {hole})
         (CM {(el A ◼ el B) ∙ (el C ◼ el C)} {(el A ◼ el B) ∙ el C} (contract {(elH A ◼H elH B) ∙H hole})
           (⊙i (⊔i id id) id)))))

-- Unproveable without classical axioms, but there seems to be some
-- sort of contraction happening here:
-- aux₁ : ∀{A B C D} → (el ((A ⊙ (B ▷ C)) ⊔ (B ▷ (D ⊙ C)))) ⊢ ((A ⊔ D) ⊙ (B ▷ C))
-- aux₁ {A}{B}{C}{D} = {!!}
