open import prelude
open import quaternary-semantics
open import lineale
open import attack-tree

module quaternary-thms {𝔹 : Set} {pf : dec 𝔹} where

record Injection {ℓ : level}{A : Set ℓ}{B : Set ℓ} (f : A → B) : Set ℓ where
 field
   inj-pf : ∀{x y : A} → (f x) ≡ (f y) → x ≡ y

open Injection

⟦_⟧_ : ATree {𝔹} {pf} → Σ[ α ∈ (𝔹 → Four) ]( Injection α ) → Four
⟦ NODE b ⟧ (α , _) = α b
⟦ AND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊙₄ (⟦ t₂ ⟧ α)
⟦ OR t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ⊔₄ (⟦ t₂ ⟧ α)
⟦ SAND t₁ t₂ ⟧ α = (⟦ t₁ ⟧ α) ▷₄ (⟦ t₂ ⟧ α)

AND-sym : ∀{t₁ t₂ : ATree {𝔹} {pf}}{α} → (⟦ AND t₁ t₂ ⟧ α) ≡ (⟦ AND t₂ t₁ ⟧ α)
AND-sym {t₁}{t₂}{α} = ⊙₄-sym {⟦ t₁ ⟧ α}

AND-assoc : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ AND (AND t₁ t₂) t₄ ⟧ α) ≡ (⟦ AND t₁ (AND t₂ t₄) ⟧ α)
AND-assoc {t₁}{t₂}{t₄}{α} = ⊙₄-assoc {⟦ t₁ ⟧ α}

OR-sym : ∀{t₁ t₂ : ATree {𝔹} {pf}}{α} → (⟦ OR t₁ t₂ ⟧ α) ≡ (⟦ OR t₂ t₁ ⟧ α)
OR-sym {t₁}{t₂}{α} = ⊔₄-sym {⟦ t₁ ⟧ α}

OR-assoc : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ OR (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR t₁ (OR t₂ t₄) ⟧ α)
OR-assoc {t₁}{t₂}{t₄}{α} = ⊔₄-assoc {⟦ t₁ ⟧ α}

OR-contract : ∀{t : ATree {𝔹} {pf}}{α} → (⟦ OR t t ⟧ α) ≡ (⟦ t ⟧ α)
OR-contract {t} = ⊔₄-contract

SAND-assoc : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ SAND (SAND t₁ t₂) t₄ ⟧ α) ≡ (⟦ SAND t₁ (SAND t₂ t₄) ⟧ α)
SAND-assoc {t₁}{t₂}{t₄}{α} = sym (▷₄-assoc {⟦ t₁ ⟧ α}{⟦ t₂ ⟧ α}{⟦ t₄ ⟧ α})

AND-OR-distl : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ AND t₁ (OR t₂ t₄) ⟧ α) ≡ (⟦ OR (AND t₁ t₂) (AND t₁ t₄) ⟧ α)
AND-OR-distl {t₁}{t₂}{t₄}{α} = ⊙₄-distl {⟦ t₁ ⟧ α}

AND-OR-distr : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ AND (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR (AND t₁ t₄) (AND t₂ t₄) ⟧ α)
AND-OR-distr {t₁}{t₂}{t₄}{α} = ⊙₄-distr {⟦ t₁ ⟧ α}

SAND-OR-distl : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ SAND t₁ (OR t₂ t₄) ⟧ α) ≡ (⟦ OR (SAND t₁ t₂) (SAND t₁ t₄) ⟧ α)
SAND-OR-distl {t₁}{t₂}{t₄}{α} = ▷₄-distl {⟦ t₁ ⟧ α}

SAND-OR-distr : ∀{t₁ t₂ t₄ : ATree {𝔹} {pf}}{α} → (⟦ SAND (OR t₁ t₂) t₄ ⟧ α) ≡ (⟦ OR (SAND t₁ t₄) (SAND t₂ t₄) ⟧ α)
SAND-OR-distr {t₁}{t₂}{t₄}{α} = ▷₄-distr {⟦ t₁ ⟧ α}{⟦ t₂ ⟧ α}{⟦ t₄ ⟧ α}

⟿-soundness : ∀{t₁ t₂ : ATree {𝔹} {pf}}{α} → t₁ ⟿ t₂ → ⟦ t₁ ⟧ α ≡ ⟦ t₂ ⟧ α
⟿-soundness {(OR t₁ t₂)} ⟿-OR-sym = OR-sym {t₁}{t₂}
⟿-soundness {(AND t₁ t₂)} {.(AND _ _)} ⟿-AND-sym = AND-sym {t₁}{t₂}
⟿-soundness {(OR t₁ (OR t₂ t₃))} {.(OR (OR _ _) _)} ⟿-OR-assoc = sym (OR-assoc {t₁}{t₂}{t₃})
⟿-soundness {(AND t₁ (AND t₂ t₃))} {.(AND (AND _ _) _)} ⟿-AND-assoc = sym (AND-assoc {t₁}{t₂}{t₃})
⟿-soundness {(SAND t₁ (SAND t₂ t₃))} {.(SAND (SAND _ _) _)} ⟿-SAND-assoc = sym (SAND-assoc {t₁}{t₂}{t₃})
⟿-soundness {(AND t₁ (OR t₂ t₃))} {.(OR (AND _ _) (AND _ _))} ⟿-AND-dist = AND-OR-distl {t₁}{t₂}{t₃}
⟿-soundness {(SAND t₁ (OR t₂ t₃))} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-dist = SAND-OR-distl {t₁}{t₂}{t₃}
⟿-soundness {(AND t₁ t₂)} {(AND t₃ _)}{α} (⟿-AND₁ p) with ⟿-soundness {α = α} p
... | r = iso₄ (⊙₄-func {⟦ t₁ ⟧ α} {⟦ t₃ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₂ ⟧ α}
                   (fst (iso₄-inv r)) (refl₄ {⟦ t₂ ⟧ α}))
               (⊙₄-func {⟦ t₃ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₂ ⟧ α}
                   (snd (iso₄-inv r)) (refl₄ {⟦ t₂ ⟧ α}))
⟿-soundness {(AND t₁ t₂)} {(AND _ t₄)}{α} (⟿-AND₂ p) with ⟿-soundness {α = α} p
... | r = iso₄ (⊙₄-func {⟦ t₁ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₄ ⟧ α}
                   (refl₄ {⟦ t₁ ⟧ α}) (fst (iso₄-inv r)))
               (⊙₄-func {⟦ t₁ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₄ ⟧ α} {⟦ t₂ ⟧ α}
                   (refl₄ {⟦ t₁ ⟧ α}) (snd (iso₄-inv r)))
⟿-soundness {(OR t₁ t₂)} {(OR t₃ _)}{α} (⟿-OR₁ p) with ⟿-soundness {α = α} p
... | r = iso₄ (⊔₄-func {⟦ t₁ ⟧ α} {⟦ t₃ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₂ ⟧ α}
                   (fst (iso₄-inv r)) (refl₄ {⟦ t₂ ⟧ α}))
               (⊔₄-func {⟦ t₃ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₂ ⟧ α}
                   (snd (iso₄-inv r)) (refl₄ {⟦ t₂ ⟧ α}))
⟿-soundness {(OR t₁ t₂)} {(OR _ t₄)}{α} (⟿-OR₂ p) with ⟿-soundness {α = α} p
... | r = iso₄ (⊔₄-func {⟦ t₁ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₄ ⟧ α}
                   (refl₄ {⟦ t₁ ⟧ α}) (fst (iso₄-inv r)))
               (⊔₄-func {⟦ t₁ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₄ ⟧ α} {⟦ t₂ ⟧ α}
                   (refl₄ {⟦ t₁ ⟧ α}) (snd (iso₄-inv r)))
⟿-soundness {(SAND t₁ t₂)} {(SAND t₃ _)}{α} (⟿-SAND₁ p) with ⟿-soundness {α = α} p
... | r = iso₄ (▷₄-func {⟦ t₁ ⟧ α} {⟦ t₃ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₂ ⟧ α}
                   (fst (iso₄-inv r)) (refl₄ {⟦ t₂ ⟧ α}))
               (▷₄-func {⟦ t₃ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₂ ⟧ α}
                   (snd (iso₄-inv r)) (refl₄ {⟦ t₂ ⟧ α}))
⟿-soundness {(SAND t₁ t₂)} {(SAND _ t₄)}{α} (⟿-SAND₂ p) with ⟿-soundness {α = α} p
... | r = iso₄ (▷₄-func {⟦ t₁ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₂ ⟧ α} {⟦ t₄ ⟧ α}
                   (refl₄ {⟦ t₁ ⟧ α}) (fst (iso₄-inv r)))
               (▷₄-func {⟦ t₁ ⟧ α} {⟦ t₁ ⟧ α} {⟦ t₄ ⟧ α} {⟦ t₂ ⟧ α}
                   (refl₄ {⟦ t₁ ⟧ α}) (snd (iso₄-inv r)))
⟿-soundness {.(OR t₂ t₂)} {t₂}{α} ⟿-contract = OR-contract {t₂}{α}
