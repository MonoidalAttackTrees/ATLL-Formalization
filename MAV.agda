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
 
