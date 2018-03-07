module MAV where

open import nat

infix 21 ¬_
data Form : Set where
  atom : ℕ → Form
  I : Form
  ¬_ : Form → Form
  _⊗_ : Form → Form → Form
  _∥_ : Form → Form → Form
  _▷_ : Form → Form → Form
  _⊕_ : Form → Form → Form
  _&_ : Form → Form → Form

infix 19 _⊸_
_⊸_ : Form → Form → Form
P ⊸ Q = ¬ P ∥ Q

infix 18 _⟶_
data _⟶_ : Form → Form → Set where
 -- monoidal structure:
 assoc-∥ : ∀{P Q R} → (P ∥ Q) ∥ R ⟶ P ∥ (Q ∥ R)
 assoc-inv-∥ : ∀{P Q R} →  P ∥ (Q ∥ R) ⟶ (P ∥ Q) ∥ R
 assoc-⊗ : ∀{P Q R} → (P ⊗ Q) ⊗ R ⟶ P ⊗ (Q ⊗ R)
 assoc-inv-⊗ : ∀{P Q R} →  P ⊗ (Q ⊗ R) ⟶ (P ⊗ Q) ⊗ R
 assoc-▷ : ∀{P Q R} → (P ▷ Q) ▷ R ⟶ P ▷ (Q ▷ R)
 assoc-inv-▷ : ∀{P Q R} →  P ▷ (Q ▷ R) ⟶ (P ▷ Q) ▷ R
 sym-∥ : ∀{P Q} → P ∥ Q ⟶ Q ∥ P
 sym-⊗ : ∀{P Q} → P ⊗ Q ⟶ Q ⊗ P
 unit-▷ : ∀{P} → I ▷ P ⟶ P
 unit-inv-▷ : ∀{P} → P ▷ I ⟶ P
 unit-∥ : ∀{P} → I ∥ P ⟶ P
 unit-inv-∥ : ∀{P} → P ∥ I ⟶ P
 unit-⊗ : ∀{P} → I ⊗ P ⟶ P
 unit-inv-⊗ : ∀{P} → P ⊗ I ⟶ P
 -- De Morgan rules:
 ldn : ∀{a} → ¬ (¬ (atom a)) ⟶ atom a
 dm-I : ¬ I ⟶ I
 dm-inv-I : I ⟶ ¬ I
 dm-∥ : ∀{P Q} → ¬ (P ∥ Q) ⟶ ¬ P ⊗ ¬ Q
 dm-inv-∥ : ∀{P Q} → ¬ P ⊗ ¬ Q ⟶ ¬ (P ∥ Q)
 dm-⊗ : ∀{P Q} → ¬ (P ⊗ Q) ⟶ ¬ P ∥ ¬ Q
 dm-inv-⊗ : ∀{P Q} → ¬ P ∥ ¬ Q ⟶ ¬ (P ⊗ Q)
 dm-▷ : ∀{P Q} → ¬ (P ▷ Q) ⟶ ¬ P ▷ ¬ Q
 dm-inv-▷ : ∀{P Q} → ¬ P ▷ ¬ Q ⟶ ¬ (P ▷ Q)
 dm-⊕ : ∀{P Q} → ¬ (P ⊕ Q) ⟶ ¬ P & ¬ Q
 dm-inv-⊕ : ∀{P Q} → ¬ P & ¬ Q ⟶ ¬ (P ⊕ Q)
 dm-& : ∀{P Q} → ¬ (P & Q) ⟶ ¬ P ⊕ ¬ Q
 dm-inv-& : ∀{P Q} → ¬ P ⊕ ¬ Q ⟶ ¬ (P & Q)
 -- Rewrite rules:
 tidy : I & I ⟶ I
 atomic  : ∀{a} → ¬ (atom a) ∥ (atom a) ⟶ I
 switch : ∀{P Q R} → (P ⊗ Q) ∥ R ⟶ P ⊗ (Q ∥ R)
 sequence : ∀{P Q R S} → (P ▷ Q) ∥ (R ▷ S) ⟶ (P ∥ R) ▷ (Q ∥ S)
 left : ∀{P Q} → P ⊕ Q ⟶ P
 right : ∀{P Q} → P ⊕ Q ⟶ Q
 external : ∀{P Q R} → (P & Q) ∥ R ⟶ (P ∥ R) & (P ∥ R)
 medial : ∀{P Q R S} → (P ▷ Q) & (R ▷ S) ⟶ (P & R) ▷ (Q & S)
 -- Closure:
 refl : ∀{P} → P ⟶ P
 trans : ∀{P Q R} → P ⟶ Q → Q ⟶ R → P ⟶ R
 -- Congruence rules:
 cong-¬ : ∀{P Q} → P ⟶ Q → ¬ P ⟶ ¬ Q
 cong-⊗ : ∀{P P' Q Q'} → P ⟶ P' → Q ⟶ Q' → P ⊗ Q ⟶ P' ⊗ Q'
 cong-∥ : ∀{P P' Q Q'} → P ⟶ P' → Q ⟶ Q' → P ∥ Q ⟶ P' ∥ Q'
 cong-▷ : ∀{P P' Q Q'} → P ⟶ P' → Q ⟶ Q' → P ▷ Q ⟶ P' ▷ Q'
 cong-⊕ : ∀{P P' Q Q'} → P ⟶ P' → Q ⟶ Q' → P ⊕ Q ⟶ P' ⊕ Q'
 cong-& : ∀{P P' Q Q'} → P ⟶ P' → Q ⟶ Q' → P & Q ⟶ P' & Q'
 
ex : ∀{a b c d : ℕ} → ((¬ (((atom a) ⊕ (atom d)) ∥ ((atom b) ▷ (atom c)))) ∥ ((atom b) ▷ ((atom d) ∥ (atom c)))) ⟶ I
ex {a}{b}{c}{d} =  trans {Q = (¬ (atom d ∥ (atom b ▷ atom c))) ∥ (atom b ▷ (atom d ∥ atom c))}
                       (cong-∥ (cong-¬ (cong-∥ right refl)) refl)
                  (trans {Q = ((¬ atom d) ⊗ (¬ (atom b ▷ atom c))) ∥ (atom b ▷ (atom d ∥ atom c))}
                       (cong-∥ dm-∥ refl)
                  (trans {Q = ((¬ atom d) ⊗ ((¬ atom b) ▷ (¬ atom c))) ∥ (atom b ▷ (atom d ∥ atom c))}
                       (cong-∥ (cong-⊗ refl dm-▷) refl)
                  (trans {Q = (¬ atom d) ⊗ (((¬ atom b) ▷ (¬ atom c)) ∥ (atom b ▷ (atom d ∥ atom c)))}
                       switch
                  (trans {Q = (¬ atom d) ⊗ (((¬ atom b) ∥ atom b) ▷ ((¬ atom c) ∥ (atom d ∥ atom c)))}
                       (cong-⊗ refl sequence)
                  (trans {Q = (¬ atom d) ⊗ (I ▷ ((¬ atom c) ∥ (atom d ∥ atom c)))}
                       (cong-⊗ refl (cong-▷ atomic refl))
                  (trans {Q = (¬ atom d) ⊗ ((¬ atom c) ∥ (atom d ∥ atom c))}
                       (cong-⊗ refl unit-▷)
                  (trans {Q = (¬ atom d) ⊗ ((¬ atom c) ∥ (atom c ∥ atom d))}
                       (cong-⊗ refl (cong-∥ refl sym-∥))
                  (trans {Q = (¬ atom d) ⊗ (((¬ atom c) ∥ atom c) ∥ atom d)}
                       (cong-⊗ refl assoc-inv-∥)
                  (trans {Q = (¬ atom d) ⊗ (I ∥ atom d)}
                       (cong-⊗ refl (cong-∥ atomic refl))
                  (trans {Q = (¬ atom d) ⊗ atom d} (cong-⊗ refl unit-∥)
                       {!!}))))))))))

