open import prelude
open import lineale
open import lineale-thms
open import attack-tree

module quaternary-semantics (𝔹 : Set) (pf : dec 𝔹) where

⟦_⟧_ : ATree 𝔹 pf → (𝔹 → Four) → Four
⟦ NODE b ⟧ α = α b
⟦ AND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊙₄ (⟦ t₂ ⟧ α)
⟦ OR t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊔₄ (⟦ t₂ ⟧ α)
⟦ SAND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ▷₄ (⟦ t₂ ⟧ α)

AND-sym : ∀{t₁ t₂ : ATree 𝔹 pf}{α} → (⟦ AND t₁ t₂ ⟧ α) ≡ (⟦ AND t₂ t₁ ⟧ α)
AND-sym {t₁}{t₂}{α} = ⊙₄-sym {⟦ t₁ ⟧ α}

AND-assoc : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ AND (AND t₁ t₂) t₄ ⟧ α) ≡ (⟦ AND t₁ (AND t₂ t₄) ⟧ α)
AND-assoc {t₁}{t₂}{t₄}{α} = ⊙₄-assoc {⟦ t₁ ⟧ α}

OR-sym : ∀{t₁ t₂ : ATree 𝔹 pf}{α} → (⟦ OR t₁ t₂ ⟧ α) ≡ (⟦ OR t₂ t₁ ⟧ α)
OR-sym {t₁}{t₂}{α} = ⊔₄-sym {⟦ t₁ ⟧ α}

OR-assoc : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ OR (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR t₁ (OR t₂ t₄) ⟧ α)
OR-assoc {t₁}{t₂}{t₄}{α} = ⊔₄-assoc {⟦ t₁ ⟧ α}

OR-contract : ∀{t : ATree 𝔹 pf}{α} → (⟦ OR t t ⟧ α) ≡ (⟦ t ⟧ α)
OR-contract {t} = ⊔₄-contract

SAND-assoc : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ SAND (SAND t₁ t₂) t₄ ⟧ α) ≡ (⟦ SAND t₁ (SAND t₂ t₄) ⟧ α)
SAND-assoc {t₁}{t₂}{t₄}{α} = sym (▷₄-assoc {⟦ t₁ ⟧ α}{⟦ t₂ ⟧ α}{⟦ t₄ ⟧ α})

AND-OR-dist₁ : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ AND t₁ (OR t₂ t₄) ⟧ α) ≡ (⟦ OR (AND t₁ t₂) (AND t₁ t₄) ⟧ α)
AND-OR-dist₁ {t₁}{t₂}{t₄}{α} = ⊙₄-distl {⟦ t₁ ⟧ α}

AND-OR-dist₂ : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ AND (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR (AND t₁ t₄) (AND t₂ t₄) ⟧ α)
AND-OR-dist₂ {t₁}{t₂}{t₄}{α} = ⊙₄-distr {⟦ t₁ ⟧ α}

SAND-OR-dist₁ : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ SAND t₁ (OR t₂ t₄) ⟧ α) ≡ (⟦ OR (SAND t₁ t₂) (SAND t₁ t₄) ⟧ α)
SAND-OR-dist₁ {t₁}{t₂}{t₄}{α} = ▷₄-distl {⟦ t₁ ⟧ α}

SAND-OR-dist₂ : ∀{t₁ t₂ t₄ : ATree 𝔹 pf}{α} → (⟦ SAND (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR (SAND t₁ t₄) (SAND t₂ t₄) ⟧ α)
SAND-OR-dist₂ {t₁}{t₂}{t₄}{α} = ▷₄-distr {⟦ t₁ ⟧ α}{⟦ t₂ ⟧ α}{⟦ t₄ ⟧ α}
