module attack-tree where

open import eq
open import empty
open import level
open import lineale
open import lineale-thms

data ATree (𝔹 : Set) : Set where
  NODE : (b : 𝔹) → ATree 𝔹
  AND  : ATree 𝔹 → ATree 𝔹 → ATree 𝔹
  OR   : ATree 𝔹 → ATree 𝔹 → ATree 𝔹
  SAND : ATree 𝔹 → ATree 𝔹 → ATree 𝔹

⟦_⟧_ : {𝔹 : Set} → ATree 𝔹 → (𝔹 → Four) → Four
⟦ NODE b ⟧ α = α b
⟦ AND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊙₄ (⟦ t₂ ⟧ α)
⟦ OR t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊔₄ (⟦ t₂ ⟧ α)
⟦ SAND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ▷₄ (⟦ t₂ ⟧ α)

AND-sym : ∀{𝔹}{t₁ t₂ : ATree 𝔹}{α} → (⟦ AND t₁ t₂ ⟧ α) ≡ (⟦ AND t₂ t₁ ⟧ α)
AND-sym {𝔹}{t₁}{t₂}{α} = ⊙₄-sym {⟦ t₁ ⟧ α}

AND-assoc : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ AND (AND t₁ t₂) t₄ ⟧ α) ≡ (⟦ AND t₁ (AND t₂ t₄) ⟧ α)
AND-assoc {𝔹}{t₁}{t₂}{t₄}{α} = ⊙₄-assoc {⟦ t₁ ⟧ α}

OR-sym : ∀{𝔹}{t₁ t₂ : ATree 𝔹}{α} → (⟦ OR t₁ t₂ ⟧ α) ≡ (⟦ OR t₂ t₁ ⟧ α)
OR-sym {𝔹}{t₁}{t₂}{α} = ⊔₄-sym {⟦ t₁ ⟧ α}

OR-assoc : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ OR (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR t₁ (OR t₂ t₄) ⟧ α)
OR-assoc {𝔹}{t₁}{t₂}{t₄}{α} = ⊔₄-assoc {⟦ t₁ ⟧ α}

OR-contract : ∀{𝔹}{t : ATree 𝔹}{α} → (⟦ OR t t ⟧ α) ≡ (⟦ t ⟧ α)
OR-contract {𝔹}{t} = ⊔₄-contract

SAND-assoc : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ SAND (SAND t₁ t₂) t₄ ⟧ α) ≡ (⟦ SAND t₁ (SAND t₂ t₄) ⟧ α)
SAND-assoc {𝔹}{t₁}{t₂}{t₄}{α} = sym (land-assoc {⟦ t₁ ⟧ α}{⟦ t₂ ⟧ α}{⟦ t₄ ⟧ α})

SAND-contract : (∀{a} → (a ▷₄ a) ≡ a) → ⊥ {lzero}
SAND-contract p = not-same-half-zero (p {zero})

AND-OR-dist₁ : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ AND t₁ (OR t₂ t₄) ⟧ α) ≡ (⟦ OR (AND t₁ t₂) (AND t₁ t₄) ⟧ α)
AND-OR-dist₁ {𝔹}{t₁}{t₂}{t₄}{α} = sym (para-over-lchoice {⟦ t₁ ⟧ α})

AND-OR-dist₂ : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ AND (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR (AND t₁ t₄) (AND t₂ t₄) ⟧ α)
AND-OR-dist₂ {𝔹}{t₁}{t₂}{t₄}{α} = sym (para-over-lchoice2 {⟦ t₁ ⟧ α})

SAND-OR-dist₁ : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ SAND t₁ (OR t₂ t₄) ⟧ α) ≡ (⟦ OR (SAND t₁ t₂) (SAND t₁ t₄) ⟧ α)
SAND-OR-dist₁ {𝔹}{t₁}{t₂}{t₄}{α} = sym (seq-over-lchoice {⟦ t₁ ⟧ α})

SAND-OR-dist₂ : ∀{𝔹}{t₁ t₂ t₄ : ATree 𝔹}{α} → (⟦ SAND (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR (SAND t₁ t₄) (SAND t₂ t₄) ⟧ α)
SAND-OR-dist₂ {𝔹}{t₁}{t₂}{t₄}{α} = sym (seq-over-lchoice2 {⟦ t₄ ⟧ α}{⟦ t₁ ⟧ α})
