module lineale-thms where

open import prelude
open import lineale

refl₄ : ∀{a} → a ≤₄ a
refl₄ {zero} = triv
refl₄ {half} = triv
refl₄ {one} = triv
refl₄ {two} = triv

trans₄ : ∀{a b c} → a ≤₄ b → b ≤₄ c → a ≤₄ c
trans₄ {zero} {zero} {zero} p₁ p₂ = triv
trans₄ {zero} {zero} {half} p₁ p₂ = triv
trans₄ {zero} {zero} {one} p₁ p₂ = triv
trans₄ {zero} {zero} {two} p₁ p₂ = triv
trans₄ {zero} {half} {zero} p₁ p₂ = triv
trans₄ {zero} {half} {half} p₁ p₂ = triv
trans₄ {zero} {half} {one} p₁ p₂ = triv
trans₄ {zero} {half} {two} p₁ p₂ = triv
trans₄ {zero} {one} {zero} p₁ p₂ = triv
trans₄ {zero} {one} {half} p₁ p₂ = triv
trans₄ {zero} {one} {one} p₁ p₂ = triv
trans₄ {zero} {one} {two} p₁ p₂ = triv
trans₄ {zero} {two} {zero} p₁ p₂ = triv
trans₄ {zero} {two} {half} p₁ p₂ = triv
trans₄ {zero} {two} {one} p₁ p₂ = triv
trans₄ {zero} {two} {two} p₁ p₂ = triv
trans₄ {half} {zero} {zero} () p₂
trans₄ {half} {zero} {half} p₁ p₂ = triv
trans₄ {half} {zero} {one} p₁ p₂ = triv
trans₄ {half} {zero} {two} p₁ p₂ = triv
trans₄ {half} {half} {zero} p₁ ()
trans₄ {half} {half} {half} p₁ p₂ = triv
trans₄ {half} {half} {one} p₁ p₂ = triv
trans₄ {half} {half} {two} p₁ p₂ = triv
trans₄ {half} {one} {zero} p₁ ()
trans₄ {half} {one} {half} p₁ p₂ = triv
trans₄ {half} {one} {one} p₁ p₂ = triv
trans₄ {half} {one} {two} p₁ p₂ = triv
trans₄ {half} {two} {zero} p₁ ()
trans₄ {half} {two} {half} p₁ p₂ = triv
trans₄ {half} {two} {one} p₁ p₂ = triv
trans₄ {half} {two} {two} p₁ p₂ = triv
trans₄ {one} {zero} {zero} () p₂
trans₄ {one} {zero} {half} () p₂
trans₄ {one} {zero} {one} p₁ p₂ = triv
trans₄ {one} {zero} {two} p₁ p₂ = triv
trans₄ {one} {half} {zero} () ()
trans₄ {one} {half} {half} () p₂
trans₄ {one} {half} {one} p₁ p₂ = triv
trans₄ {one} {half} {two} p₁ p₂ = triv
trans₄ {one} {one} {zero} p₁ ()
trans₄ {one} {one} {half} p₁ ()
trans₄ {one} {one} {one} p₁ p₂ = triv
trans₄ {one} {one} {two} p₁ p₂ = triv
trans₄ {one} {two} {zero} p₁ ()
trans₄ {one} {two} {half} p₁ ()
trans₄ {one} {two} {one} p₁ p₂ = triv
trans₄ {one} {two} {two} p₁ p₂ = triv
trans₄ {two} {zero} {zero} () p₂
trans₄ {two} {zero} {half} () p₂
trans₄ {two} {zero} {one} () p₂
trans₄ {two} {zero} {two} p₁ p₂ = triv
trans₄ {two} {half} {zero} () ()
trans₄ {two} {half} {half} () p₂
trans₄ {two} {half} {one} () p₂
trans₄ {two} {half} {two} p₁ p₂ = triv
trans₄ {two} {one} {zero} () ()
trans₄ {two} {one} {half} () ()
trans₄ {two} {one} {one} () p₂
trans₄ {two} {one} {two} p₁ p₂ = triv
trans₄ {two} {two} {zero} p₁ ()
trans₄ {two} {two} {half} p₁ ()
trans₄ {two} {two} {one} p₁ ()
trans₄ {two} {two} {two} p₁ p₂ = triv

iso₄ : ∀{a b} → a ≤₄ b → b ≤₄ a → a ≡ b
iso₄ {zero} {zero} p₁ p₂ = refl
iso₄ {zero} {half} p₁ ()
iso₄ {zero} {one} p₁ ()
iso₄ {zero} {two} p₁ ()
iso₄ {half} {zero} () p₂
iso₄ {half} {half} p₁ p₂ = refl
iso₄ {half} {one} p₁ ()
iso₄ {half} {two} p₁ ()
iso₄ {one} {zero} () p₂
iso₄ {one} {half} () p₂
iso₄ {one} {one} p₁ p₂ = refl
iso₄ {one} {two} p₁ ()
iso₄ {two} {zero} () p₂
iso₄ {two} {half} () p₂
iso₄ {two} {one} () p₂
iso₄ {two} {two} p₁ p₂ = refl

iso₄-inv : ∀{a b} → a ≡ b → ((a ≤₄ b) × (b ≤₄ a))
iso₄-inv {zero} {zero} p = triv , triv
iso₄-inv {zero} {half} ()
iso₄-inv {zero} {one} ()
iso₄-inv {zero} {two} ()
iso₄-inv {half} {zero} ()
iso₄-inv {half} {half} p = triv , triv
iso₄-inv {half} {one} ()
iso₄-inv {half} {two} ()
iso₄-inv {one} {zero} ()
iso₄-inv {one} {half} ()
iso₄-inv {one} {one} p = triv , triv
iso₄-inv {one} {two} ()
iso₄-inv {two} {zero} ()
iso₄-inv {two} {half} ()
iso₄-inv {two} {one} ()
iso₄-inv {two} {two} p = triv , triv

⊙₄-zerol : ∀{x} → (zero ⊙₄ x) ≤₄ zero
⊙₄-zerol {zero} = triv
⊙₄-zerol {half} = triv
⊙₄-zerol {one} = triv
⊙₄-zerol {two} = triv

⊙₄-zeror : ∀{x} → (x ⊙₄ zero) ≤₄ zero
⊙₄-zeror {zero} = triv
⊙₄-zeror {half} = triv
⊙₄-zeror {one} = triv
⊙₄-zeror {two} = triv

⊙₄-contract : (∀{a} → (a ⊙₄ a) ≡ a) → ⊥ {lzero}
⊙₄-contract p with p {two}
... | () 

⊙₄-sym : ∀{a b} → a ⊙₄ b ≡ b ⊙₄ a
⊙₄-sym {zero} {zero} = refl
⊙₄-sym {zero} {half} = refl
⊙₄-sym {zero} {one} = refl
⊙₄-sym {zero} {two} = refl
⊙₄-sym {half} {zero} = refl
⊙₄-sym {half} {half} = refl
⊙₄-sym {half} {one} = refl
⊙₄-sym {half} {two} = refl
⊙₄-sym {one} {zero} = refl
⊙₄-sym {one} {half} = refl
⊙₄-sym {one} {one} = refl
⊙₄-sym {one} {two} = refl
⊙₄-sym {two} {zero} = refl
⊙₄-sym {two} {half} = refl
⊙₄-sym {two} {one} = refl
⊙₄-sym {two} {two} = refl

⊙₄-assoc : ∀{a b c} → (a ⊙₄ b) ⊙₄ c ≡ a ⊙₄ (b ⊙₄ c)
⊙₄-assoc {zero} {zero} {zero} = refl
⊙₄-assoc {zero} {zero} {half} = refl
⊙₄-assoc {zero} {zero} {one} = refl
⊙₄-assoc {zero} {zero} {two} = refl
⊙₄-assoc {zero} {half} {zero} = refl
⊙₄-assoc {zero} {half} {half} = refl
⊙₄-assoc {zero} {half} {one} = refl
⊙₄-assoc {zero} {half} {two} = refl
⊙₄-assoc {zero} {one} {zero} = refl
⊙₄-assoc {zero} {one} {half} = refl
⊙₄-assoc {zero} {one} {one} = refl
⊙₄-assoc {zero} {one} {two} = refl
⊙₄-assoc {zero} {two} {zero} = refl
⊙₄-assoc {zero} {two} {half} = refl
⊙₄-assoc {zero} {two} {one} = refl
⊙₄-assoc {zero} {two} {two} = refl
⊙₄-assoc {half} {zero} {zero} = refl
⊙₄-assoc {half} {zero} {half} = refl
⊙₄-assoc {half} {zero} {one} = refl
⊙₄-assoc {half} {zero} {two} = refl
⊙₄-assoc {half} {half} {zero} = refl
⊙₄-assoc {half} {half} {half} = refl
⊙₄-assoc {half} {half} {one} = refl
⊙₄-assoc {half} {half} {two} = refl
⊙₄-assoc {half} {one} {zero} = refl
⊙₄-assoc {half} {one} {half} = refl
⊙₄-assoc {half} {one} {one} = refl
⊙₄-assoc {half} {one} {two} = refl
⊙₄-assoc {half} {two} {zero} = refl
⊙₄-assoc {half} {two} {half} = refl
⊙₄-assoc {half} {two} {one} = refl
⊙₄-assoc {half} {two} {two} = refl
⊙₄-assoc {one} {zero} {zero} = refl
⊙₄-assoc {one} {zero} {half} = refl
⊙₄-assoc {one} {zero} {one} = refl
⊙₄-assoc {one} {zero} {two} = refl
⊙₄-assoc {one} {half} {zero} = refl
⊙₄-assoc {one} {half} {half} = refl
⊙₄-assoc {one} {half} {one} = refl
⊙₄-assoc {one} {half} {two} = refl
⊙₄-assoc {one} {one} {zero} = refl
⊙₄-assoc {one} {one} {half} = refl
⊙₄-assoc {one} {one} {one} = refl
⊙₄-assoc {one} {one} {two} = refl
⊙₄-assoc {one} {two} {zero} = refl
⊙₄-assoc {one} {two} {half} = refl
⊙₄-assoc {one} {two} {one} = refl
⊙₄-assoc {one} {two} {two} = refl
⊙₄-assoc {two} {zero} {zero} = refl
⊙₄-assoc {two} {zero} {half} = refl
⊙₄-assoc {two} {zero} {one} = refl
⊙₄-assoc {two} {zero} {two} = refl
⊙₄-assoc {two} {half} {zero} = refl
⊙₄-assoc {two} {half} {half} = refl
⊙₄-assoc {two} {half} {one} = refl
⊙₄-assoc {two} {half} {two} = refl
⊙₄-assoc {two} {one} {zero} = refl
⊙₄-assoc {two} {one} {half} = refl
⊙₄-assoc {two} {one} {one} = refl
⊙₄-assoc {two} {one} {two} = refl
⊙₄-assoc {two} {two} {zero} = refl
⊙₄-assoc {two} {two} {half} = refl
⊙₄-assoc {two} {two} {one} = refl
⊙₄-assoc {two} {two} {two} = refl

⊙₄-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ⊙₄ b) ≤₄ (c ⊙₄ d)
⊙₄-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {zero} {two} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {two} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {two} p₁ p₂ = triv
⊙₄-func {zero} {zero} {two} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {two} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {two} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {two} {two} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {two} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {two} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {two} p₁ p₂ = triv
⊙₄-func {zero} {half} {two} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {two} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {two} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {two} {two} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {two} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {two} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {two} p₁ p₂ = triv
⊙₄-func {zero} {one} {two} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {two} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {two} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {two} {two} p₁ p₂ = triv
⊙₄-func {zero} {two} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {two} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {two} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {two} {zero} {two} p₁ p₂ = triv
⊙₄-func {zero} {two} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {two} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {two} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {two} {half} {two} p₁ p₂ = triv
⊙₄-func {zero} {two} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {two} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {two} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {two} {one} {two} p₁ p₂ = triv
⊙₄-func {zero} {two} {two} {zero} p₁ p₂ = triv
⊙₄-func {zero} {two} {two} {half} p₁ p₂ = triv
⊙₄-func {zero} {two} {two} {one} p₁ p₂ = triv
⊙₄-func {zero} {two} {two} {two} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {two} p₁ p₂ = triv
⊙₄-func {half} {zero} {half} {zero} () ()
⊙₄-func {half} {zero} {half} {half} () p₂
⊙₄-func {half} {zero} {half} {one} () p₂
⊙₄-func {half} {zero} {half} {two} () p₂
⊙₄-func {half} {zero} {one} {zero} () ()
⊙₄-func {half} {zero} {one} {half} () ()
⊙₄-func {half} {zero} {one} {one} () p₂
⊙₄-func {half} {zero} {one} {two} () p₂
⊙₄-func {half} {zero} {two} {zero} () ()
⊙₄-func {half} {zero} {two} {half} () ()
⊙₄-func {half} {zero} {two} {one} () ()
⊙₄-func {half} {zero} {two} {two} () p₂
⊙₄-func {half} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {zero} {two} p₁ p₂ = triv
⊙₄-func {half} {half} {half} {zero} p₁ ()
⊙₄-func {half} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {half} {two} p₁ p₂ = triv
⊙₄-func {half} {half} {one} {zero} p₁ ()
⊙₄-func {half} {half} {one} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {one} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {one} {two} p₁ p₂ = triv
⊙₄-func {half} {half} {two} {zero} p₁ ()
⊙₄-func {half} {half} {two} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {two} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {two} {two} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {two} p₁ p₂ = triv
⊙₄-func {half} {one} {half} {zero} p₁ ()
⊙₄-func {half} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {half} {two} p₁ p₂ = triv
⊙₄-func {half} {one} {one} {zero} p₁ ()
⊙₄-func {half} {one} {one} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {one} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {one} {two} p₁ p₂ = triv
⊙₄-func {half} {one} {two} {zero} p₁ ()
⊙₄-func {half} {one} {two} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {two} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {two} {two} p₁ p₂ = triv
⊙₄-func {half} {two} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {two} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {two} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {two} {zero} {two} p₁ p₂ = triv
⊙₄-func {half} {two} {half} {zero} p₁ ()
⊙₄-func {half} {two} {half} {half} p₁ p₂ = triv
⊙₄-func {half} {two} {half} {one} p₁ p₂ = triv
⊙₄-func {half} {two} {half} {two} p₁ p₂ = triv
⊙₄-func {half} {two} {one} {zero} p₁ ()
⊙₄-func {half} {two} {one} {half} p₁ p₂ = triv
⊙₄-func {half} {two} {one} {one} p₁ p₂ = triv
⊙₄-func {half} {two} {one} {two} p₁ p₂ = triv
⊙₄-func {half} {two} {two} {zero} p₁ ()
⊙₄-func {half} {two} {two} {half} p₁ p₂ = triv
⊙₄-func {half} {two} {two} {one} p₁ p₂ = triv
⊙₄-func {half} {two} {two} {two} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {two} p₁ p₂ = triv
⊙₄-func {one} {zero} {half} {zero} () ()
⊙₄-func {one} {zero} {half} {half} () p₂
⊙₄-func {one} {zero} {half} {one} () p₂
⊙₄-func {one} {zero} {half} {two} () p₂
⊙₄-func {one} {zero} {one} {zero} () ()
⊙₄-func {one} {zero} {one} {half} () ()
⊙₄-func {one} {zero} {one} {one} () p₂
⊙₄-func {one} {zero} {one} {two} () p₂
⊙₄-func {one} {zero} {two} {zero} () ()
⊙₄-func {one} {zero} {two} {half} () ()
⊙₄-func {one} {zero} {two} {one} () ()
⊙₄-func {one} {zero} {two} {two} () p₂
⊙₄-func {one} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {half} {zero} {two} p₁ p₂ = triv
⊙₄-func {one} {half} {half} {zero} () ()
⊙₄-func {one} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {one} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {one} {half} {half} {two} p₁ p₂ = triv
⊙₄-func {one} {half} {one} {zero} () ()
⊙₄-func {one} {half} {one} {half} p₁ p₂ = triv
⊙₄-func {one} {half} {one} {one} p₁ p₂ = triv
⊙₄-func {one} {half} {one} {two} p₁ p₂ = triv
⊙₄-func {one} {half} {two} {zero} () ()
⊙₄-func {one} {half} {two} {half} () ()
⊙₄-func {one} {half} {two} {one} () ()
⊙₄-func {one} {half} {two} {two} () p₂
⊙₄-func {one} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {one} {zero} {two} p₁ p₂ = triv
⊙₄-func {one} {one} {half} {zero} p₁ ()
⊙₄-func {one} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {one} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {one} {one} {half} {two} p₁ p₂ = triv
⊙₄-func {one} {one} {one} {zero} p₁ ()
⊙₄-func {one} {one} {one} {half} p₁ p₂ = triv
⊙₄-func {one} {one} {one} {one} p₁ p₂ = triv
⊙₄-func {one} {one} {one} {two} p₁ p₂ = triv
⊙₄-func {one} {one} {two} {zero} p₁ ()
⊙₄-func {one} {one} {two} {half} p₁ ()
⊙₄-func {one} {one} {two} {one} p₁ ()
⊙₄-func {one} {one} {two} {two} p₁ p₂ = triv
⊙₄-func {one} {two} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {two} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {two} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {two} {zero} {two} p₁ p₂ = triv
⊙₄-func {one} {two} {half} {zero} p₁ ()
⊙₄-func {one} {two} {half} {half} p₁ p₂ = triv
⊙₄-func {one} {two} {half} {one} p₁ p₂ = triv
⊙₄-func {one} {two} {half} {two} p₁ p₂ = triv
⊙₄-func {one} {two} {one} {zero} p₁ ()
⊙₄-func {one} {two} {one} {half} p₁ p₂ = triv
⊙₄-func {one} {two} {one} {one} p₁ p₂ = triv
⊙₄-func {one} {two} {one} {two} p₁ p₂ = triv
⊙₄-func {one} {two} {two} {zero} p₁ ()
⊙₄-func {one} {two} {two} {half} p₁ ()
⊙₄-func {one} {two} {two} {one} p₁ p₂ = triv
⊙₄-func {one} {two} {two} {two} p₁ p₂ = triv
⊙₄-func {two} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {two} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {two} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {two} {zero} {zero} {two} p₁ p₂ = triv
⊙₄-func {two} {zero} {half} {zero} () ()
⊙₄-func {two} {zero} {half} {half} () p₂
⊙₄-func {two} {zero} {half} {one} () p₂
⊙₄-func {two} {zero} {half} {two} () p₂
⊙₄-func {two} {zero} {one} {zero} () ()
⊙₄-func {two} {zero} {one} {half} () ()
⊙₄-func {two} {zero} {one} {one} () p₂
⊙₄-func {two} {zero} {one} {two} () p₂
⊙₄-func {two} {zero} {two} {zero} () ()
⊙₄-func {two} {zero} {two} {half} () ()
⊙₄-func {two} {zero} {two} {one} () ()
⊙₄-func {two} {zero} {two} {two} () p₂
⊙₄-func {two} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {two} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {two} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {two} {half} {zero} {two} p₁ p₂ = triv
⊙₄-func {two} {half} {half} {zero} () ()
⊙₄-func {two} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {two} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {two} {half} {half} {two} p₁ p₂ = triv
⊙₄-func {two} {half} {one} {zero} () ()
⊙₄-func {two} {half} {one} {half} () ()
⊙₄-func {two} {half} {one} {one} () p₂
⊙₄-func {two} {half} {one} {two} () p₂
⊙₄-func {two} {half} {two} {zero} () ()
⊙₄-func {two} {half} {two} {half} () ()
⊙₄-func {two} {half} {two} {one} () ()
⊙₄-func {two} {half} {two} {two} () p₂
⊙₄-func {two} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {two} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {two} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {two} {one} {zero} {two} p₁ p₂ = triv
⊙₄-func {two} {one} {half} {zero} () ()
⊙₄-func {two} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {two} {one} {half} {one} () p₂
⊙₄-func {two} {one} {half} {two} p₁ p₂ = triv
⊙₄-func {two} {one} {one} {zero} () ()
⊙₄-func {two} {one} {one} {half} () ()
⊙₄-func {two} {one} {one} {one} () p₂
⊙₄-func {two} {one} {one} {two} p₁ p₂ = triv
⊙₄-func {two} {one} {two} {zero} () ()
⊙₄-func {two} {one} {two} {half} () ()
⊙₄-func {two} {one} {two} {one} () ()
⊙₄-func {two} {one} {two} {two} () p₂
⊙₄-func {two} {two} {zero} {zero} p₁ p₂ = triv
⊙₄-func {two} {two} {zero} {half} p₁ p₂ = triv
⊙₄-func {two} {two} {zero} {one} p₁ p₂ = triv
⊙₄-func {two} {two} {zero} {two} p₁ p₂ = triv
⊙₄-func {two} {two} {half} {zero} p₁ ()
⊙₄-func {two} {two} {half} {half} p₁ p₂ = triv
⊙₄-func {two} {two} {half} {one} p₁ p₂ = triv
⊙₄-func {two} {two} {half} {two} p₁ p₂ = triv
⊙₄-func {two} {two} {one} {zero} p₁ ()
⊙₄-func {two} {two} {one} {half} p₁ ()
⊙₄-func {two} {two} {one} {one} p₁ p₂ = triv
⊙₄-func {two} {two} {one} {two} p₁ p₂ = triv
⊙₄-func {two} {two} {two} {zero} p₁ ()
⊙₄-func {two} {two} {two} {half} p₁ ()
⊙₄-func {two} {two} {two} {one} p₁ ()
⊙₄-func {two} {two} {two} {two} p₁ p₂ = triv

⊙₄-distl : {a b c : Four} → (a ⊙₄ (b ⊔₄ c)) ≡ ((a ⊙₄ b) ⊔₄ (a ⊙₄ c))
⊙₄-distl {zero} {zero} {zero} = refl
⊙₄-distl {zero} {zero} {half} = refl
⊙₄-distl {zero} {zero} {one} = refl
⊙₄-distl {zero} {zero} {two} = refl
⊙₄-distl {zero} {half} {zero} = refl
⊙₄-distl {zero} {half} {half} = refl
⊙₄-distl {zero} {half} {one} = refl
⊙₄-distl {zero} {half} {two} = refl
⊙₄-distl {zero} {one} {zero} = refl
⊙₄-distl {zero} {one} {half} = refl
⊙₄-distl {zero} {one} {one} = refl
⊙₄-distl {zero} {one} {two} = refl
⊙₄-distl {zero} {two} {zero} = refl
⊙₄-distl {zero} {two} {half} = refl
⊙₄-distl {zero} {two} {one} = refl
⊙₄-distl {zero} {two} {two} = refl
⊙₄-distl {half} {zero} {zero} = refl
⊙₄-distl {half} {zero} {half} = refl
⊙₄-distl {half} {zero} {one} = refl
⊙₄-distl {half} {zero} {two} = refl
⊙₄-distl {half} {half} {zero} = refl
⊙₄-distl {half} {half} {half} = refl
⊙₄-distl {half} {half} {one} = refl
⊙₄-distl {half} {half} {two} = refl
⊙₄-distl {half} {one} {zero} = refl
⊙₄-distl {half} {one} {half} = refl
⊙₄-distl {half} {one} {one} = refl
⊙₄-distl {half} {one} {two} = refl
⊙₄-distl {half} {two} {zero} = refl
⊙₄-distl {half} {two} {half} = refl
⊙₄-distl {half} {two} {one} = refl
⊙₄-distl {half} {two} {two} = refl
⊙₄-distl {one} {zero} {zero} = refl
⊙₄-distl {one} {zero} {half} = refl
⊙₄-distl {one} {zero} {one} = refl
⊙₄-distl {one} {zero} {two} = refl
⊙₄-distl {one} {half} {zero} = refl
⊙₄-distl {one} {half} {half} = refl
⊙₄-distl {one} {half} {one} = refl
⊙₄-distl {one} {half} {two} = refl
⊙₄-distl {one} {one} {zero} = refl
⊙₄-distl {one} {one} {half} = refl
⊙₄-distl {one} {one} {one} = refl
⊙₄-distl {one} {one} {two} = refl
⊙₄-distl {one} {two} {zero} = refl
⊙₄-distl {one} {two} {half} = refl
⊙₄-distl {one} {two} {one} = refl
⊙₄-distl {one} {two} {two} = refl
⊙₄-distl {two} {zero} {zero} = refl
⊙₄-distl {two} {zero} {half} = refl
⊙₄-distl {two} {zero} {one} = refl
⊙₄-distl {two} {zero} {two} = refl
⊙₄-distl {two} {half} {zero} = refl
⊙₄-distl {two} {half} {half} = refl
⊙₄-distl {two} {half} {one} = refl
⊙₄-distl {two} {half} {two} = refl
⊙₄-distl {two} {one} {zero} = refl
⊙₄-distl {two} {one} {half} = refl
⊙₄-distl {two} {one} {one} = refl
⊙₄-distl {two} {one} {two} = refl
⊙₄-distl {two} {two} {zero} = refl
⊙₄-distl {two} {two} {half} = refl
⊙₄-distl {two} {two} {one} = refl
⊙₄-distl {two} {two} {two} = refl

⊙₄-distr : {a b c : Four} → ((a ⊔₄ b) ⊙₄ c) ≡ ((a ⊙₄ c) ⊔₄ (b ⊙₄ c))
⊙₄-distr {zero} {zero} {zero} = refl
⊙₄-distr {zero} {zero} {half} = refl
⊙₄-distr {zero} {zero} {one} = refl
⊙₄-distr {zero} {zero} {two} = refl
⊙₄-distr {zero} {half} {zero} = refl
⊙₄-distr {zero} {half} {half} = refl
⊙₄-distr {zero} {half} {one} = refl
⊙₄-distr {zero} {half} {two} = refl
⊙₄-distr {zero} {one} {zero} = refl
⊙₄-distr {zero} {one} {half} = refl
⊙₄-distr {zero} {one} {one} = refl
⊙₄-distr {zero} {one} {two} = refl
⊙₄-distr {zero} {two} {zero} = refl
⊙₄-distr {zero} {two} {half} = refl
⊙₄-distr {zero} {two} {one} = refl
⊙₄-distr {zero} {two} {two} = refl
⊙₄-distr {half} {zero} {zero} = refl
⊙₄-distr {half} {zero} {half} = refl
⊙₄-distr {half} {zero} {one} = refl
⊙₄-distr {half} {zero} {two} = refl
⊙₄-distr {half} {half} {zero} = refl
⊙₄-distr {half} {half} {half} = refl
⊙₄-distr {half} {half} {one} = refl
⊙₄-distr {half} {half} {two} = refl
⊙₄-distr {half} {one} {zero} = refl
⊙₄-distr {half} {one} {half} = refl
⊙₄-distr {half} {one} {one} = refl
⊙₄-distr {half} {one} {two} = refl
⊙₄-distr {half} {two} {zero} = refl
⊙₄-distr {half} {two} {half} = refl
⊙₄-distr {half} {two} {one} = refl
⊙₄-distr {half} {two} {two} = refl
⊙₄-distr {one} {zero} {zero} = refl
⊙₄-distr {one} {zero} {half} = refl
⊙₄-distr {one} {zero} {one} = refl
⊙₄-distr {one} {zero} {two} = refl
⊙₄-distr {one} {half} {zero} = refl
⊙₄-distr {one} {half} {half} = refl
⊙₄-distr {one} {half} {one} = refl
⊙₄-distr {one} {half} {two} = refl
⊙₄-distr {one} {one} {zero} = refl
⊙₄-distr {one} {one} {half} = refl
⊙₄-distr {one} {one} {one} = refl
⊙₄-distr {one} {one} {two} = refl
⊙₄-distr {one} {two} {zero} = refl
⊙₄-distr {one} {two} {half} = refl
⊙₄-distr {one} {two} {one} = refl
⊙₄-distr {one} {two} {two} = refl
⊙₄-distr {two} {zero} {zero} = refl
⊙₄-distr {two} {zero} {half} = refl
⊙₄-distr {two} {zero} {one} = refl
⊙₄-distr {two} {zero} {two} = refl
⊙₄-distr {two} {half} {zero} = refl
⊙₄-distr {two} {half} {half} = refl
⊙₄-distr {two} {half} {one} = refl
⊙₄-distr {two} {half} {two} = refl
⊙₄-distr {two} {one} {zero} = refl
⊙₄-distr {two} {one} {half} = refl
⊙₄-distr {two} {one} {one} = refl
⊙₄-distr {two} {one} {two} = refl
⊙₄-distr {two} {two} {zero} = refl
⊙₄-distr {two} {two} {half} = refl
⊙₄-distr {two} {two} {one} = refl
⊙₄-distr {two} {two} {two} = refl

▷₄-sym : (∀{a b} → (a ▷₄ b) ≡ (b ▷₄ a)) → ⊥ {lzero}
▷₄-sym p with p {half}{one}
... | () 

▷₄-contract : (∀{a} → (a ▷₄ a) ≡ a) → ⊥ {lzero}
▷₄-contract p with p {two}
... | () 

▷₄-zerol : ∀{x} → (zero ▷₄ x) ≤₄ zero
▷₄-zerol {zero} = triv
▷₄-zerol {half} = triv
▷₄-zerol {one} = triv
▷₄-zerol {two} = triv

▷₄-zeror : ∀{x} → (x ▷₄ zero) ≤₄ zero
▷₄-zeror {zero} = triv
▷₄-zeror {half} = triv
▷₄-zeror {one} = triv
▷₄-zeror {two} = triv

▷₄-assoc : {a b c : Four} →  a ▷₄ (b ▷₄ c) ≡ (a ▷₄ b) ▷₄ c
▷₄-assoc {zero} {zero} {zero} = refl
▷₄-assoc {zero} {zero} {half} = refl
▷₄-assoc {zero} {zero} {one} = refl
▷₄-assoc {zero} {zero} {two} = refl
▷₄-assoc {zero} {half} {zero} = refl
▷₄-assoc {zero} {half} {half} = refl
▷₄-assoc {zero} {half} {one} = refl
▷₄-assoc {zero} {half} {two} = refl
▷₄-assoc {zero} {one} {zero} = refl
▷₄-assoc {zero} {one} {half} = refl
▷₄-assoc {zero} {one} {one} = refl
▷₄-assoc {zero} {one} {two} = refl
▷₄-assoc {zero} {two} {zero} = refl
▷₄-assoc {zero} {two} {half} = refl
▷₄-assoc {zero} {two} {one} = refl
▷₄-assoc {zero} {two} {two} = refl
▷₄-assoc {half} {zero} {zero} = refl
▷₄-assoc {half} {zero} {half} = refl
▷₄-assoc {half} {zero} {one} = refl
▷₄-assoc {half} {zero} {two} = refl
▷₄-assoc {half} {half} {zero} = refl
▷₄-assoc {half} {half} {half} = refl
▷₄-assoc {half} {half} {one} = refl
▷₄-assoc {half} {half} {two} = refl
▷₄-assoc {half} {one} {zero} = refl
▷₄-assoc {half} {one} {half} = refl
▷₄-assoc {half} {one} {one} = refl
▷₄-assoc {half} {one} {two} = refl
▷₄-assoc {half} {two} {zero} = refl
▷₄-assoc {half} {two} {half} = refl
▷₄-assoc {half} {two} {one} = refl
▷₄-assoc {half} {two} {two} = refl
▷₄-assoc {one} {zero} {zero} = refl
▷₄-assoc {one} {zero} {half} = refl
▷₄-assoc {one} {zero} {one} = refl
▷₄-assoc {one} {zero} {two} = refl
▷₄-assoc {one} {half} {zero} = refl
▷₄-assoc {one} {half} {half} = refl
▷₄-assoc {one} {half} {one} = refl
▷₄-assoc {one} {half} {two} = refl
▷₄-assoc {one} {one} {zero} = refl
▷₄-assoc {one} {one} {half} = refl
▷₄-assoc {one} {one} {one} = refl
▷₄-assoc {one} {one} {two} = refl
▷₄-assoc {one} {two} {zero} = refl
▷₄-assoc {one} {two} {half} = refl
▷₄-assoc {one} {two} {one} = refl
▷₄-assoc {one} {two} {two} = refl
▷₄-assoc {two} {zero} {zero} = refl
▷₄-assoc {two} {zero} {half} = refl
▷₄-assoc {two} {zero} {one} = refl
▷₄-assoc {two} {zero} {two} = refl
▷₄-assoc {two} {half} {zero} = refl
▷₄-assoc {two} {half} {half} = refl
▷₄-assoc {two} {half} {one} = refl
▷₄-assoc {two} {half} {two} = refl
▷₄-assoc {two} {one} {zero} = refl
▷₄-assoc {two} {one} {half} = refl
▷₄-assoc {two} {one} {one} = refl
▷₄-assoc {two} {one} {two} = refl
▷₄-assoc {two} {two} {zero} = refl
▷₄-assoc {two} {two} {half} = refl
▷₄-assoc {two} {two} {one} = refl
▷₄-assoc {two} {two} {two} = refl

▷₄-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ▷₄ b) ≤₄ (c ▷₄ d)
▷₄-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {zero} {two} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {two} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {two} p₁ p₂ = triv
▷₄-func {zero} {zero} {two} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {two} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {two} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {two} {two} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {two} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {two} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {two} p₁ p₂ = triv
▷₄-func {zero} {half} {two} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {two} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {two} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {two} {two} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {two} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {two} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {two} p₁ p₂ = triv
▷₄-func {zero} {one} {two} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {two} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {two} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {two} {two} p₁ p₂ = triv
▷₄-func {zero} {two} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {two} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {two} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {two} {zero} {two} p₁ p₂ = triv
▷₄-func {zero} {two} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {two} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {two} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {two} {half} {two} p₁ p₂ = triv
▷₄-func {zero} {two} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {two} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {two} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {two} {one} {two} p₁ p₂ = triv
▷₄-func {zero} {two} {two} {zero} p₁ p₂ = triv
▷₄-func {zero} {two} {two} {half} p₁ p₂ = triv
▷₄-func {zero} {two} {two} {one} p₁ p₂ = triv
▷₄-func {zero} {two} {two} {two} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {two} p₁ p₂ = triv
▷₄-func {half} {zero} {half} {zero} () ()
▷₄-func {half} {zero} {half} {half} () p₂
▷₄-func {half} {zero} {half} {one} () p₂
▷₄-func {half} {zero} {half} {two} () p₂
▷₄-func {half} {zero} {one} {zero} () ()
▷₄-func {half} {zero} {one} {half} () ()
▷₄-func {half} {zero} {one} {one} () p₂
▷₄-func {half} {zero} {one} {two} () p₂
▷₄-func {half} {zero} {two} {zero} () ()
▷₄-func {half} {zero} {two} {half} () ()
▷₄-func {half} {zero} {two} {one} () ()
▷₄-func {half} {zero} {two} {two} () p₂
▷₄-func {half} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {half} {zero} {two} p₁ p₂ = triv
▷₄-func {half} {half} {half} {zero} p₁ ()
▷₄-func {half} {half} {half} {half} p₁ p₂ = triv
▷₄-func {half} {half} {half} {one} p₁ p₂ = triv
▷₄-func {half} {half} {half} {two} p₁ p₂ = triv
▷₄-func {half} {half} {one} {zero} p₁ ()
▷₄-func {half} {half} {one} {half} p₁ ()
▷₄-func {half} {half} {one} {one} p₁ p₂ = triv
▷₄-func {half} {half} {one} {two} p₁ p₂ = triv
▷₄-func {half} {half} {two} {zero} p₁ ()
▷₄-func {half} {half} {two} {half} p₁ ()
▷₄-func {half} {half} {two} {one} p₁ p₂ = triv
▷₄-func {half} {half} {two} {two} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {two} p₁ p₂ = triv
▷₄-func {half} {one} {half} {zero} p₁ ()
▷₄-func {half} {one} {half} {half} p₁ p₂ = triv
▷₄-func {half} {one} {half} {one} p₁ p₂ = triv
▷₄-func {half} {one} {half} {two} p₁ p₂ = triv
▷₄-func {half} {one} {one} {zero} p₁ ()
▷₄-func {half} {one} {one} {half} p₁ p₂ = triv
▷₄-func {half} {one} {one} {one} p₁ p₂ = triv
▷₄-func {half} {one} {one} {two} p₁ p₂ = triv
▷₄-func {half} {one} {two} {zero} p₁ ()
▷₄-func {half} {one} {two} {half} p₁ p₂ = triv
▷₄-func {half} {one} {two} {one} p₁ p₂ = triv
▷₄-func {half} {one} {two} {two} p₁ p₂ = triv
▷₄-func {half} {two} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {two} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {two} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {two} {zero} {two} p₁ p₂ = triv
▷₄-func {half} {two} {half} {zero} p₁ ()
▷₄-func {half} {two} {half} {half} p₁ p₂ = triv
▷₄-func {half} {two} {half} {one} p₁ p₂ = triv
▷₄-func {half} {two} {half} {two} p₁ p₂ = triv
▷₄-func {half} {two} {one} {zero} p₁ ()
▷₄-func {half} {two} {one} {half} p₁ p₂ = triv
▷₄-func {half} {two} {one} {one} p₁ p₂ = triv
▷₄-func {half} {two} {one} {two} p₁ p₂ = triv
▷₄-func {half} {two} {two} {zero} p₁ ()
▷₄-func {half} {two} {two} {half} p₁ p₂ = triv
▷₄-func {half} {two} {two} {one} p₁ p₂ = triv
▷₄-func {half} {two} {two} {two} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {two} p₁ p₂ = triv
▷₄-func {one} {zero} {half} {zero} () ()
▷₄-func {one} {zero} {half} {half} () p₂
▷₄-func {one} {zero} {half} {one} () p₂
▷₄-func {one} {zero} {half} {two} () p₂
▷₄-func {one} {zero} {one} {zero} () ()
▷₄-func {one} {zero} {one} {half} () ()
▷₄-func {one} {zero} {one} {one} () p₂
▷₄-func {one} {zero} {one} {two} () p₂
▷₄-func {one} {zero} {two} {zero} () ()
▷₄-func {one} {zero} {two} {half} () ()
▷₄-func {one} {zero} {two} {one} () ()
▷₄-func {one} {zero} {two} {two} () p₂
▷₄-func {one} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {half} {zero} {two} p₁ p₂ = triv
▷₄-func {one} {half} {half} {zero} () ()
▷₄-func {one} {half} {half} {half} () p₂
▷₄-func {one} {half} {half} {one} () p₂
▷₄-func {one} {half} {half} {two} () p₂
▷₄-func {one} {half} {one} {zero} () ()
▷₄-func {one} {half} {one} {half} () ()
▷₄-func {one} {half} {one} {one} () p₂
▷₄-func {one} {half} {one} {two} () p₂
▷₄-func {one} {half} {two} {zero} () ()
▷₄-func {one} {half} {two} {half} () ()
▷₄-func {one} {half} {two} {one} () ()
▷₄-func {one} {half} {two} {two} () p₂
▷₄-func {one} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {two} p₁ p₂ = triv
▷₄-func {one} {one} {half} {zero} p₁ ()
▷₄-func {one} {one} {half} {half} p₁ p₂ = triv
▷₄-func {one} {one} {half} {one} p₁ p₂ = triv
▷₄-func {one} {one} {half} {two} p₁ p₂ = triv
▷₄-func {one} {one} {one} {zero} p₁ ()
▷₄-func {one} {one} {one} {half} p₁ p₂ = triv
▷₄-func {one} {one} {one} {one} p₁ p₂ = triv
▷₄-func {one} {one} {one} {two} p₁ p₂ = triv
▷₄-func {one} {one} {two} {zero} p₁ ()
▷₄-func {one} {one} {two} {half} p₁ p₂ = triv
▷₄-func {one} {one} {two} {one} p₁ p₂ = triv
▷₄-func {one} {one} {two} {two} p₁ p₂ = triv
▷₄-func {one} {two} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {two} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {two} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {two} {zero} {two} p₁ p₂ = triv
▷₄-func {one} {two} {half} {zero} p₁ ()
▷₄-func {one} {two} {half} {half} p₁ p₂ = triv
▷₄-func {one} {two} {half} {one} p₁ p₂ = triv
▷₄-func {one} {two} {half} {two} p₁ p₂ = triv
▷₄-func {one} {two} {one} {zero} p₁ ()
▷₄-func {one} {two} {one} {half} p₁ p₂ = triv
▷₄-func {one} {two} {one} {one} p₁ p₂ = triv
▷₄-func {one} {two} {one} {two} p₁ p₂ = triv
▷₄-func {one} {two} {two} {zero} p₁ ()
▷₄-func {one} {two} {two} {half} p₁ p₂ = triv
▷₄-func {one} {two} {two} {one} p₁ p₂ = triv
▷₄-func {one} {two} {two} {two} p₁ p₂ = triv
▷₄-func {two} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {two} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {two} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {two} {zero} {zero} {two} p₁ p₂ = triv
▷₄-func {two} {zero} {half} {zero} p₁ ()
▷₄-func {two} {zero} {half} {half} () p₂
▷₄-func {two} {zero} {half} {one} () p₂
▷₄-func {two} {zero} {half} {two} () p₂
▷₄-func {two} {zero} {one} {zero} () ()
▷₄-func {two} {zero} {one} {half} () ()
▷₄-func {two} {zero} {one} {one} () p₂
▷₄-func {two} {zero} {one} {two} () p₂
▷₄-func {two} {zero} {two} {zero} () ()
▷₄-func {two} {zero} {two} {half} () ()
▷₄-func {two} {zero} {two} {one} () ()
▷₄-func {two} {zero} {two} {two} () p₂
▷₄-func {two} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {two} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {two} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {two} {half} {zero} {two} p₁ p₂ = triv
▷₄-func {two} {half} {half} {zero} () ()
▷₄-func {two} {half} {half} {half} () p₂
▷₄-func {two} {half} {half} {one} () p₂
▷₄-func {two} {half} {half} {two} () p₂
▷₄-func {two} {half} {one} {zero} () ()
▷₄-func {two} {half} {one} {half} () ()
▷₄-func {two} {half} {one} {one} () p₂
▷₄-func {two} {half} {one} {two} () p₂
▷₄-func {two} {half} {two} {zero} () ()
▷₄-func {two} {half} {two} {half} () ()
▷₄-func {two} {half} {two} {one} () ()
▷₄-func {two} {half} {two} {two} () p₂
▷₄-func {two} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {two} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {two} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {two} {one} {zero} {two} p₁ p₂ = triv
▷₄-func {two} {one} {half} {zero} () ()
▷₄-func {two} {one} {half} {half} () p₂
▷₄-func {two} {one} {half} {one} () p₂
▷₄-func {two} {one} {half} {two} () p₂
▷₄-func {two} {one} {one} {zero} () ()
▷₄-func {two} {one} {one} {half} p₁ p₂ = triv
▷₄-func {two} {one} {one} {one} p₁ p₂ = triv
▷₄-func {two} {one} {one} {two} p₁ p₂ = triv
▷₄-func {two} {one} {two} {zero} () ()
▷₄-func {two} {one} {two} {half} p₁ p₂ = triv
▷₄-func {two} {one} {two} {one} p₁ p₂ = triv
▷₄-func {two} {one} {two} {two} p₁ p₂ = triv
▷₄-func {two} {two} {zero} {zero} p₁ p₂ = triv
▷₄-func {two} {two} {zero} {half} p₁ p₂ = triv
▷₄-func {two} {two} {zero} {one} p₁ p₂ = triv
▷₄-func {two} {two} {zero} {two} p₁ p₂ = triv
▷₄-func {two} {two} {half} {zero} p₁ ()
▷₄-func {two} {two} {half} {half} p₁ p₂ = triv
▷₄-func {two} {two} {half} {one} p₁ p₂ = triv
▷₄-func {two} {two} {half} {two} p₁ p₂ = triv
▷₄-func {two} {two} {one} {zero} p₁ ()
▷₄-func {two} {two} {one} {half} p₁ p₂ = triv
▷₄-func {two} {two} {one} {one} p₁ p₂ = triv
▷₄-func {two} {two} {one} {two} p₁ p₂ = triv
▷₄-func {two} {two} {two} {zero} p₁ ()
▷₄-func {two} {two} {two} {half} p₁ p₂ = triv
▷₄-func {two} {two} {two} {one} p₁ p₂ = triv
▷₄-func {two} {two} {two} {two} p₁ p₂ = triv

▷₄-distl : {a b c : Four} → (a ▷₄ (b ⊔₄ c)) ≡ ((a ▷₄ b) ⊔₄ (a ▷₄ c))
▷₄-distl {zero} {zero} {zero} = refl
▷₄-distl {zero} {zero} {half} = refl
▷₄-distl {zero} {zero} {one} = refl
▷₄-distl {zero} {zero} {two} = refl
▷₄-distl {zero} {half} {zero} = refl
▷₄-distl {zero} {half} {half} = refl
▷₄-distl {zero} {half} {one} = refl
▷₄-distl {zero} {half} {two} = refl
▷₄-distl {zero} {one} {zero} = refl
▷₄-distl {zero} {one} {half} = refl
▷₄-distl {zero} {one} {one} = refl
▷₄-distl {zero} {one} {two} = refl
▷₄-distl {zero} {two} {zero} = refl
▷₄-distl {zero} {two} {half} = refl
▷₄-distl {zero} {two} {one} = refl
▷₄-distl {zero} {two} {two} = refl
▷₄-distl {half} {zero} {zero} = refl
▷₄-distl {half} {zero} {half} = refl
▷₄-distl {half} {zero} {one} = refl
▷₄-distl {half} {zero} {two} = refl
▷₄-distl {half} {half} {zero} = refl
▷₄-distl {half} {half} {half} = refl
▷₄-distl {half} {half} {one} = refl
▷₄-distl {half} {half} {two} = refl
▷₄-distl {half} {one} {zero} = refl
▷₄-distl {half} {one} {half} = refl
▷₄-distl {half} {one} {one} = refl
▷₄-distl {half} {one} {two} = refl
▷₄-distl {half} {two} {zero} = refl
▷₄-distl {half} {two} {half} = refl
▷₄-distl {half} {two} {one} = refl
▷₄-distl {half} {two} {two} = refl
▷₄-distl {one} {zero} {zero} = refl
▷₄-distl {one} {zero} {half} = refl
▷₄-distl {one} {zero} {one} = refl
▷₄-distl {one} {zero} {two} = refl
▷₄-distl {one} {half} {zero} = refl
▷₄-distl {one} {half} {half} = refl
▷₄-distl {one} {half} {one} = refl
▷₄-distl {one} {half} {two} = refl
▷₄-distl {one} {one} {zero} = refl
▷₄-distl {one} {one} {half} = refl
▷₄-distl {one} {one} {one} = refl
▷₄-distl {one} {one} {two} = refl
▷₄-distl {one} {two} {zero} = refl
▷₄-distl {one} {two} {half} = refl
▷₄-distl {one} {two} {one} = refl
▷₄-distl {one} {two} {two} = refl
▷₄-distl {two} {zero} {zero} = refl
▷₄-distl {two} {zero} {half} = refl
▷₄-distl {two} {zero} {one} = refl
▷₄-distl {two} {zero} {two} = refl
▷₄-distl {two} {half} {zero} = refl
▷₄-distl {two} {half} {half} = refl
▷₄-distl {two} {half} {one} = refl
▷₄-distl {two} {half} {two} = refl
▷₄-distl {two} {one} {zero} = refl
▷₄-distl {two} {one} {half} = refl
▷₄-distl {two} {one} {one} = refl
▷₄-distl {two} {one} {two} = refl
▷₄-distl {two} {two} {zero} = refl
▷₄-distl {two} {two} {half} = refl
▷₄-distl {two} {two} {one} = refl
▷₄-distl {two} {two} {two} = refl

▷₄-distr : {a b c : Four} → ((a ⊔₄ b) ▷₄ c) ≡ ((a ▷₄ c) ⊔₄ (b ▷₄ c))
▷₄-distr {zero} {zero} {zero} = refl
▷₄-distr {zero} {zero} {half} = refl
▷₄-distr {zero} {zero} {one} = refl
▷₄-distr {zero} {zero} {two} = refl
▷₄-distr {zero} {half} {zero} = refl
▷₄-distr {zero} {half} {half} = refl
▷₄-distr {zero} {half} {one} = refl
▷₄-distr {zero} {half} {two} = refl
▷₄-distr {zero} {one} {zero} = refl
▷₄-distr {zero} {one} {half} = refl
▷₄-distr {zero} {one} {one} = refl
▷₄-distr {zero} {one} {two} = refl
▷₄-distr {zero} {two} {zero} = refl
▷₄-distr {zero} {two} {half} = refl
▷₄-distr {zero} {two} {one} = refl
▷₄-distr {zero} {two} {two} = refl
▷₄-distr {half} {zero} {zero} = refl
▷₄-distr {half} {zero} {half} = refl
▷₄-distr {half} {zero} {one} = refl
▷₄-distr {half} {zero} {two} = refl
▷₄-distr {half} {half} {zero} = refl
▷₄-distr {half} {half} {half} = refl
▷₄-distr {half} {half} {one} = refl
▷₄-distr {half} {half} {two} = refl
▷₄-distr {half} {one} {zero} = refl
▷₄-distr {half} {one} {half} = refl
▷₄-distr {half} {one} {one} = refl
▷₄-distr {half} {one} {two} = refl
▷₄-distr {half} {two} {zero} = refl
▷₄-distr {half} {two} {half} = refl
▷₄-distr {half} {two} {one} = refl
▷₄-distr {half} {two} {two} = refl
▷₄-distr {one} {zero} {zero} = refl
▷₄-distr {one} {zero} {half} = refl
▷₄-distr {one} {zero} {one} = refl
▷₄-distr {one} {zero} {two} = refl
▷₄-distr {one} {half} {zero} = refl
▷₄-distr {one} {half} {half} = refl
▷₄-distr {one} {half} {one} = refl
▷₄-distr {one} {half} {two} = refl
▷₄-distr {one} {one} {zero} = refl
▷₄-distr {one} {one} {half} = refl
▷₄-distr {one} {one} {one} = refl
▷₄-distr {one} {one} {two} = refl
▷₄-distr {one} {two} {zero} = refl
▷₄-distr {one} {two} {half} = refl
▷₄-distr {one} {two} {one} = refl
▷₄-distr {one} {two} {two} = refl
▷₄-distr {two} {zero} {zero} = refl
▷₄-distr {two} {zero} {half} = refl
▷₄-distr {two} {zero} {one} = refl
▷₄-distr {two} {zero} {two} = refl
▷₄-distr {two} {half} {zero} = refl
▷₄-distr {two} {half} {half} = refl
▷₄-distr {two} {half} {one} = refl
▷₄-distr {two} {half} {two} = refl
▷₄-distr {two} {one} {zero} = refl
▷₄-distr {two} {one} {half} = refl
▷₄-distr {two} {one} {one} = refl
▷₄-distr {two} {one} {two} = refl
▷₄-distr {two} {two} {zero} = refl
▷₄-distr {two} {two} {half} = refl
▷₄-distr {two} {two} {one} = refl
▷₄-distr {two} {two} {two} = refl

⊔₄-sym : ∀{a b} → (a ⊔₄ b) ≡ (b ⊔₄ a)
⊔₄-sym {zero} {zero} = refl
⊔₄-sym {zero} {half} = refl
⊔₄-sym {zero} {one} = refl
⊔₄-sym {zero} {two} = refl
⊔₄-sym {half} {zero} = refl
⊔₄-sym {half} {half} = refl
⊔₄-sym {half} {one} = refl
⊔₄-sym {half} {two} = refl
⊔₄-sym {one} {zero} = refl
⊔₄-sym {one} {half} = refl
⊔₄-sym {one} {one} = refl
⊔₄-sym {one} {two} = refl
⊔₄-sym {two} {zero} = refl
⊔₄-sym {two} {half} = refl
⊔₄-sym {two} {one} = refl
⊔₄-sym {two} {two} = refl

⊔₄-assoc : ∀{a b c} → (a ⊔₄ b) ⊔₄ c ≡ a ⊔₄ (b ⊔₄ c)
⊔₄-assoc {zero} {zero} {zero} = refl
⊔₄-assoc {zero} {zero} {half} = refl
⊔₄-assoc {zero} {zero} {one} = refl
⊔₄-assoc {zero} {zero} {two} = refl
⊔₄-assoc {zero} {half} {zero} = refl
⊔₄-assoc {zero} {half} {half} = refl
⊔₄-assoc {zero} {half} {one} = refl
⊔₄-assoc {zero} {half} {two} = refl
⊔₄-assoc {zero} {one} {zero} = refl
⊔₄-assoc {zero} {one} {half} = refl
⊔₄-assoc {zero} {one} {one} = refl
⊔₄-assoc {zero} {one} {two} = refl
⊔₄-assoc {zero} {two} {zero} = refl
⊔₄-assoc {zero} {two} {half} = refl
⊔₄-assoc {zero} {two} {one} = refl
⊔₄-assoc {zero} {two} {two} = refl
⊔₄-assoc {half} {zero} {zero} = refl
⊔₄-assoc {half} {zero} {half} = refl
⊔₄-assoc {half} {zero} {one} = refl
⊔₄-assoc {half} {zero} {two} = refl
⊔₄-assoc {half} {half} {zero} = refl
⊔₄-assoc {half} {half} {half} = refl
⊔₄-assoc {half} {half} {one} = refl
⊔₄-assoc {half} {half} {two} = refl
⊔₄-assoc {half} {one} {zero} = refl
⊔₄-assoc {half} {one} {half} = refl
⊔₄-assoc {half} {one} {one} = refl
⊔₄-assoc {half} {one} {two} = refl
⊔₄-assoc {half} {two} {zero} = refl
⊔₄-assoc {half} {two} {half} = refl
⊔₄-assoc {half} {two} {one} = refl
⊔₄-assoc {half} {two} {two} = refl
⊔₄-assoc {one} {zero} {zero} = refl
⊔₄-assoc {one} {zero} {half} = refl
⊔₄-assoc {one} {zero} {one} = refl
⊔₄-assoc {one} {zero} {two} = refl
⊔₄-assoc {one} {half} {zero} = refl
⊔₄-assoc {one} {half} {half} = refl
⊔₄-assoc {one} {half} {one} = refl
⊔₄-assoc {one} {half} {two} = refl
⊔₄-assoc {one} {one} {zero} = refl
⊔₄-assoc {one} {one} {half} = refl
⊔₄-assoc {one} {one} {one} = refl
⊔₄-assoc {one} {one} {two} = refl
⊔₄-assoc {one} {two} {zero} = refl
⊔₄-assoc {one} {two} {half} = refl
⊔₄-assoc {one} {two} {one} = refl
⊔₄-assoc {one} {two} {two} = refl
⊔₄-assoc {two} {zero} {zero} = refl
⊔₄-assoc {two} {zero} {half} = refl
⊔₄-assoc {two} {zero} {one} = refl
⊔₄-assoc {two} {zero} {two} = refl
⊔₄-assoc {two} {half} {zero} = refl
⊔₄-assoc {two} {half} {half} = refl
⊔₄-assoc {two} {half} {one} = refl
⊔₄-assoc {two} {half} {two} = refl
⊔₄-assoc {two} {one} {zero} = refl
⊔₄-assoc {two} {one} {half} = refl
⊔₄-assoc {two} {one} {one} = refl
⊔₄-assoc {two} {one} {two} = refl
⊔₄-assoc {two} {two} {zero} = refl
⊔₄-assoc {two} {two} {half} = refl
⊔₄-assoc {two} {two} {one} = refl
⊔₄-assoc {two} {two} {two} = refl

⊔₄-func : ∀{a c b d} → a ≤₄ c → b ≤₄ d → (a ⊔₄ b) ≤₄ (c ⊔₄ d)
⊔₄-func {zero} {zero} {zero} {zero} triv triv = triv
⊔₄-func {zero} {zero} {zero} {half} triv triv = triv
⊔₄-func {zero} {zero} {zero} {one} triv triv = triv
⊔₄-func {zero} {zero} {zero} {two} triv triv = triv
⊔₄-func {zero} {zero} {half} {zero} triv ()
⊔₄-func {zero} {zero} {half} {half} triv triv = triv
⊔₄-func {zero} {zero} {half} {one} triv triv = triv
⊔₄-func {zero} {zero} {half} {two} triv triv = triv
⊔₄-func {zero} {zero} {one} {zero} triv ()
⊔₄-func {zero} {zero} {one} {half} triv ()
⊔₄-func {zero} {zero} {one} {one} triv triv = triv
⊔₄-func {zero} {zero} {one} {two} triv triv = triv
⊔₄-func {zero} {zero} {two} {zero} triv ()
⊔₄-func {zero} {zero} {two} {half} triv ()
⊔₄-func {zero} {zero} {two} {one} triv ()
⊔₄-func {zero} {zero} {two} {two} triv triv = triv
⊔₄-func {zero} {half} {zero} {zero} triv triv = triv
⊔₄-func {zero} {half} {zero} {half} triv triv = triv
⊔₄-func {zero} {half} {zero} {one} triv triv = triv
⊔₄-func {zero} {half} {zero} {two} triv triv = triv
⊔₄-func {zero} {half} {half} {zero} triv ()
⊔₄-func {zero} {half} {half} {half} triv triv = triv
⊔₄-func {zero} {half} {half} {one} triv triv = triv
⊔₄-func {zero} {half} {half} {two} triv triv = triv
⊔₄-func {zero} {half} {one} {zero} triv ()
⊔₄-func {zero} {half} {one} {half} triv ()
⊔₄-func {zero} {half} {one} {one} triv triv = triv
⊔₄-func {zero} {half} {one} {two} triv triv = triv
⊔₄-func {zero} {half} {two} {zero} triv ()
⊔₄-func {zero} {half} {two} {half} triv ()
⊔₄-func {zero} {half} {two} {one} triv ()
⊔₄-func {zero} {half} {two} {two} triv triv = triv
⊔₄-func {zero} {one} {zero} {zero} triv triv = triv
⊔₄-func {zero} {one} {zero} {half} triv triv = triv
⊔₄-func {zero} {one} {zero} {one} triv triv = triv
⊔₄-func {zero} {one} {zero} {two} triv triv = triv
⊔₄-func {zero} {one} {half} {zero} triv ()
⊔₄-func {zero} {one} {half} {half} triv triv = triv
⊔₄-func {zero} {one} {half} {one} triv triv = triv
⊔₄-func {zero} {one} {half} {two} triv triv = triv
⊔₄-func {zero} {one} {one} {zero} triv ()
⊔₄-func {zero} {one} {one} {half} triv ()
⊔₄-func {zero} {one} {one} {one} triv triv = triv
⊔₄-func {zero} {one} {one} {two} triv triv = triv
⊔₄-func {zero} {one} {two} {zero} triv ()
⊔₄-func {zero} {one} {two} {half} triv ()
⊔₄-func {zero} {one} {two} {one} triv ()
⊔₄-func {zero} {one} {two} {two} triv triv = triv
⊔₄-func {zero} {two} {zero} {zero} triv triv = triv
⊔₄-func {zero} {two} {zero} {half} triv triv = triv
⊔₄-func {zero} {two} {zero} {one} triv triv = triv
⊔₄-func {zero} {two} {zero} {two} triv triv = triv
⊔₄-func {zero} {two} {half} {zero} triv ()
⊔₄-func {zero} {two} {half} {half} triv triv = triv
⊔₄-func {zero} {two} {half} {one} triv triv = triv
⊔₄-func {zero} {two} {half} {two} triv triv = triv
⊔₄-func {zero} {two} {one} {zero} triv ()
⊔₄-func {zero} {two} {one} {half} triv ()
⊔₄-func {zero} {two} {one} {one} triv triv = triv
⊔₄-func {zero} {two} {one} {two} triv triv = triv
⊔₄-func {zero} {two} {two} {zero} triv ()
⊔₄-func {zero} {two} {two} {half} triv ()
⊔₄-func {zero} {two} {two} {one} triv ()
⊔₄-func {zero} {two} {two} {two} triv triv = triv
⊔₄-func {half} {zero} {zero} {zero} () p₂
⊔₄-func {half} {zero} {zero} {half} () p₂
⊔₄-func {half} {zero} {zero} {one} () p₂
⊔₄-func {half} {zero} {zero} {two} () p₂
⊔₄-func {half} {zero} {half} {zero} () p₂
⊔₄-func {half} {zero} {half} {half} () p₂
⊔₄-func {half} {zero} {half} {one} () p₂
⊔₄-func {half} {zero} {half} {two} () p₂
⊔₄-func {half} {zero} {one} {zero} () p₂
⊔₄-func {half} {zero} {one} {half} () p₂
⊔₄-func {half} {zero} {one} {one} () p₂
⊔₄-func {half} {zero} {one} {two} () p₂
⊔₄-func {half} {zero} {two} {zero} () p₂
⊔₄-func {half} {zero} {two} {half} () p₂
⊔₄-func {half} {zero} {two} {one} () p₂
⊔₄-func {half} {zero} {two} {two} () p₂
⊔₄-func {half} {half} {zero} {zero} triv triv = triv
⊔₄-func {half} {half} {zero} {half} triv triv = triv
⊔₄-func {half} {half} {zero} {one} triv triv = triv
⊔₄-func {half} {half} {zero} {two} triv triv = triv
⊔₄-func {half} {half} {half} {zero} triv ()
⊔₄-func {half} {half} {half} {half} triv triv = triv
⊔₄-func {half} {half} {half} {one} triv triv = triv
⊔₄-func {half} {half} {half} {two} triv triv = triv
⊔₄-func {half} {half} {one} {zero} triv ()
⊔₄-func {half} {half} {one} {half} triv ()
⊔₄-func {half} {half} {one} {one} triv triv = triv
⊔₄-func {half} {half} {one} {two} triv triv = triv
⊔₄-func {half} {half} {two} {zero} triv ()
⊔₄-func {half} {half} {two} {half} triv ()
⊔₄-func {half} {half} {two} {one} triv ()
⊔₄-func {half} {half} {two} {two} triv triv = triv
⊔₄-func {half} {one} {zero} {zero} triv triv = triv
⊔₄-func {half} {one} {zero} {half} triv triv = triv
⊔₄-func {half} {one} {zero} {one} triv triv = triv
⊔₄-func {half} {one} {zero} {two} triv triv = triv
⊔₄-func {half} {one} {half} {zero} triv ()
⊔₄-func {half} {one} {half} {half} triv triv = triv
⊔₄-func {half} {one} {half} {one} triv triv = triv
⊔₄-func {half} {one} {half} {two} triv triv = triv
⊔₄-func {half} {one} {one} {zero} triv ()
⊔₄-func {half} {one} {one} {half} triv ()
⊔₄-func {half} {one} {one} {one} triv triv = triv
⊔₄-func {half} {one} {one} {two} triv triv = triv
⊔₄-func {half} {one} {two} {zero} triv ()
⊔₄-func {half} {one} {two} {half} triv ()
⊔₄-func {half} {one} {two} {one} triv ()
⊔₄-func {half} {one} {two} {two} triv triv = triv
⊔₄-func {half} {two} {zero} {zero} triv triv = triv
⊔₄-func {half} {two} {zero} {half} triv triv = triv
⊔₄-func {half} {two} {zero} {one} triv triv = triv
⊔₄-func {half} {two} {zero} {two} triv triv = triv
⊔₄-func {half} {two} {half} {zero} triv ()
⊔₄-func {half} {two} {half} {half} triv triv = triv
⊔₄-func {half} {two} {half} {one} triv triv = triv
⊔₄-func {half} {two} {half} {two} triv triv = triv
⊔₄-func {half} {two} {one} {zero} triv ()
⊔₄-func {half} {two} {one} {half} triv ()
⊔₄-func {half} {two} {one} {one} triv triv = triv
⊔₄-func {half} {two} {one} {two} triv triv = triv
⊔₄-func {half} {two} {two} {zero} triv ()
⊔₄-func {half} {two} {two} {half} triv ()
⊔₄-func {half} {two} {two} {one} triv ()
⊔₄-func {half} {two} {two} {two} triv triv = triv
⊔₄-func {one} {zero} {zero} {zero} () p₂
⊔₄-func {one} {zero} {zero} {half} () p₂
⊔₄-func {one} {zero} {zero} {one} () p₂
⊔₄-func {one} {zero} {zero} {two} () p₂
⊔₄-func {one} {zero} {half} {zero} () p₂
⊔₄-func {one} {zero} {half} {half} () p₂
⊔₄-func {one} {zero} {half} {one} () p₂
⊔₄-func {one} {zero} {half} {two} () p₂
⊔₄-func {one} {zero} {one} {zero} () p₂
⊔₄-func {one} {zero} {one} {half} () p₂
⊔₄-func {one} {zero} {one} {one} () p₂
⊔₄-func {one} {zero} {one} {two} () p₂
⊔₄-func {one} {zero} {two} {zero} () p₂
⊔₄-func {one} {zero} {two} {half} () p₂
⊔₄-func {one} {zero} {two} {one} () p₂
⊔₄-func {one} {zero} {two} {two} () p₂
⊔₄-func {one} {half} {zero} {zero} () p₂
⊔₄-func {one} {half} {zero} {half} () p₂
⊔₄-func {one} {half} {zero} {one} () p₂
⊔₄-func {one} {half} {zero} {two} () p₂
⊔₄-func {one} {half} {half} {zero} () p₂
⊔₄-func {one} {half} {half} {half} () p₂
⊔₄-func {one} {half} {half} {one} () p₂
⊔₄-func {one} {half} {half} {two} () p₂
⊔₄-func {one} {half} {one} {zero} () p₂
⊔₄-func {one} {half} {one} {half} () p₂
⊔₄-func {one} {half} {one} {one} () p₂
⊔₄-func {one} {half} {one} {two} () p₂
⊔₄-func {one} {half} {two} {zero} () p₂
⊔₄-func {one} {half} {two} {half} () p₂
⊔₄-func {one} {half} {two} {one} () p₂
⊔₄-func {one} {half} {two} {two} () p₂
⊔₄-func {one} {one} {zero} {zero} triv triv = triv
⊔₄-func {one} {one} {zero} {half} triv triv = triv
⊔₄-func {one} {one} {zero} {one} triv triv = triv
⊔₄-func {one} {one} {zero} {two} triv triv = triv
⊔₄-func {one} {one} {half} {zero} triv ()
⊔₄-func {one} {one} {half} {half} triv triv = triv
⊔₄-func {one} {one} {half} {one} triv triv = triv
⊔₄-func {one} {one} {half} {two} triv triv = triv
⊔₄-func {one} {one} {one} {zero} triv ()
⊔₄-func {one} {one} {one} {half} triv ()
⊔₄-func {one} {one} {one} {one} triv triv = triv
⊔₄-func {one} {one} {one} {two} triv triv = triv
⊔₄-func {one} {one} {two} {zero} triv ()
⊔₄-func {one} {one} {two} {half} triv ()
⊔₄-func {one} {one} {two} {one} triv ()
⊔₄-func {one} {one} {two} {two} triv triv = triv
⊔₄-func {one} {two} {zero} {zero} triv triv = triv
⊔₄-func {one} {two} {zero} {half} triv triv = triv
⊔₄-func {one} {two} {zero} {one} triv triv = triv
⊔₄-func {one} {two} {zero} {two} triv triv = triv
⊔₄-func {one} {two} {half} {zero} triv ()
⊔₄-func {one} {two} {half} {half} triv triv = triv
⊔₄-func {one} {two} {half} {one} triv triv = triv
⊔₄-func {one} {two} {half} {two} triv triv = triv
⊔₄-func {one} {two} {one} {zero} triv ()
⊔₄-func {one} {two} {one} {half} triv ()
⊔₄-func {one} {two} {one} {one} triv triv = triv
⊔₄-func {one} {two} {one} {two} triv triv = triv
⊔₄-func {one} {two} {two} {zero} triv ()
⊔₄-func {one} {two} {two} {half} triv ()
⊔₄-func {one} {two} {two} {one} triv ()
⊔₄-func {one} {two} {two} {two} triv triv = triv
⊔₄-func {two} {zero} {zero} {zero} () p₂
⊔₄-func {two} {zero} {zero} {half} () p₂
⊔₄-func {two} {zero} {zero} {one} () p₂
⊔₄-func {two} {zero} {zero} {two} () p₂
⊔₄-func {two} {zero} {half} {zero} () p₂
⊔₄-func {two} {zero} {half} {half} () p₂
⊔₄-func {two} {zero} {half} {one} () p₂
⊔₄-func {two} {zero} {half} {two} () p₂
⊔₄-func {two} {zero} {one} {zero} () p₂
⊔₄-func {two} {zero} {one} {half} () p₂
⊔₄-func {two} {zero} {one} {one} () p₂
⊔₄-func {two} {zero} {one} {two} () p₂
⊔₄-func {two} {zero} {two} {zero} () p₂
⊔₄-func {two} {zero} {two} {half} () p₂
⊔₄-func {two} {zero} {two} {one} () p₂
⊔₄-func {two} {zero} {two} {two} () p₂
⊔₄-func {two} {half} {zero} {zero} () p₂
⊔₄-func {two} {half} {zero} {half} () p₂
⊔₄-func {two} {half} {zero} {one} () p₂
⊔₄-func {two} {half} {zero} {two} () p₂
⊔₄-func {two} {half} {half} {zero} () p₂
⊔₄-func {two} {half} {half} {half} () p₂
⊔₄-func {two} {half} {half} {one} () p₂
⊔₄-func {two} {half} {half} {two} () p₂
⊔₄-func {two} {half} {one} {zero} () p₂
⊔₄-func {two} {half} {one} {half} () p₂
⊔₄-func {two} {half} {one} {one} () p₂
⊔₄-func {two} {half} {one} {two} () p₂
⊔₄-func {two} {half} {two} {zero} () p₂
⊔₄-func {two} {half} {two} {half} () p₂
⊔₄-func {two} {half} {two} {one} () p₂
⊔₄-func {two} {half} {two} {two} () p₂
⊔₄-func {two} {one} {zero} {zero} () p₂
⊔₄-func {two} {one} {zero} {half} () p₂
⊔₄-func {two} {one} {zero} {one} () p₂
⊔₄-func {two} {one} {zero} {two} () p₂
⊔₄-func {two} {one} {half} {zero} () p₂
⊔₄-func {two} {one} {half} {half} () p₂
⊔₄-func {two} {one} {half} {one} () p₂
⊔₄-func {two} {one} {half} {two} () p₂
⊔₄-func {two} {one} {one} {zero} () p₂
⊔₄-func {two} {one} {one} {half} () p₂
⊔₄-func {two} {one} {one} {one} () p₂
⊔₄-func {two} {one} {one} {two} () p₂
⊔₄-func {two} {one} {two} {zero} () p₂
⊔₄-func {two} {one} {two} {half} () p₂
⊔₄-func {two} {one} {two} {one} () p₂
⊔₄-func {two} {one} {two} {two} () p₂
⊔₄-func {two} {two} {zero} {zero} triv triv = triv
⊔₄-func {two} {two} {zero} {half} triv triv = triv
⊔₄-func {two} {two} {zero} {one} triv triv = triv
⊔₄-func {two} {two} {zero} {two} triv triv = triv
⊔₄-func {two} {two} {half} {zero} triv ()
⊔₄-func {two} {two} {half} {half} triv triv = triv
⊔₄-func {two} {two} {half} {one} triv triv = triv
⊔₄-func {two} {two} {half} {two} triv triv = triv
⊔₄-func {two} {two} {one} {zero} triv ()
⊔₄-func {two} {two} {one} {half} triv ()
⊔₄-func {two} {two} {one} {one} triv triv = triv
⊔₄-func {two} {two} {one} {two} triv triv = triv
⊔₄-func {two} {two} {two} {zero} triv ()
⊔₄-func {two} {two} {two} {half} triv ()
⊔₄-func {two} {two} {two} {one} triv ()
⊔₄-func {two} {two} {two} {two} triv triv = triv

⊔₄-contract : ∀{a} → (a ⊔₄ a) ≡ a
⊔₄-contract {zero} = refl
⊔₄-contract {half} = refl
⊔₄-contract {one} = refl
⊔₄-contract {two} = refl

⊗₄-func : ∀{a c b d} → a ≤₄ c → b ≤₄ d → (a ⊗₄ b) ≤₄ (c ⊗₄ d)
⊗₄-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {zero} {two} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {two} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {two} p₁ p₂ = triv
⊗₄-func {zero} {zero} {two} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {two} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {two} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {two} {two} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {two} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {two} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {two} p₁ p₂ = triv
⊗₄-func {zero} {half} {two} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {two} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {two} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {two} {two} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {two} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {two} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {two} p₁ p₂ = triv
⊗₄-func {zero} {one} {two} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {two} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {two} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {two} {two} p₁ p₂ = triv
⊗₄-func {zero} {two} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {two} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {two} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {two} {zero} {two} p₁ p₂ = triv
⊗₄-func {zero} {two} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {two} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {two} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {two} {half} {two} p₁ p₂ = triv
⊗₄-func {zero} {two} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {two} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {two} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {two} {one} {two} p₁ p₂ = triv
⊗₄-func {zero} {two} {two} {zero} p₁ p₂ = triv
⊗₄-func {zero} {two} {two} {half} p₁ p₂ = triv
⊗₄-func {zero} {two} {two} {one} p₁ p₂ = triv
⊗₄-func {zero} {two} {two} {two} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {two} p₁ p₂ = triv
⊗₄-func {half} {zero} {half} {zero} () ()
⊗₄-func {half} {zero} {half} {half} () p₂
⊗₄-func {half} {zero} {half} {one} () p₂
⊗₄-func {half} {zero} {half} {two} () p₂
⊗₄-func {half} {zero} {one} {zero} () p₂
⊗₄-func {half} {zero} {one} {half} () p₂
⊗₄-func {half} {zero} {one} {one} () p₂
⊗₄-func {half} {zero} {one} {two} () p₂
⊗₄-func {half} {zero} {two} {zero} () p₂
⊗₄-func {half} {zero} {two} {half} () p₂
⊗₄-func {half} {zero} {two} {one} () p₂
⊗₄-func {half} {zero} {two} {two} () p₂
⊗₄-func {half} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {two} p₁ p₂ = triv
⊗₄-func {half} {half} {half} {zero} triv ()
⊗₄-func {half} {half} {half} {half} p₁ p₂ = triv
⊗₄-func {half} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {half} {two} p₁ p₂ = triv
⊗₄-func {half} {half} {one} {zero} triv ()
⊗₄-func {half} {half} {one} {half} triv ()
⊗₄-func {half} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {one} {two} p₁ p₂ = triv
⊗₄-func {half} {half} {two} {zero} triv ()
⊗₄-func {half} {half} {two} {half} triv ()
⊗₄-func {half} {half} {two} {one} triv ()
⊗₄-func {half} {half} {two} {two} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {two} p₁ p₂ = triv
⊗₄-func {half} {one} {half} {zero} triv ()
⊗₄-func {half} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {half} {two} p₁ p₂ = triv
⊗₄-func {half} {one} {one} {zero} triv ()
⊗₄-func {half} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {one} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {one} {two} p₁ p₂ = triv
⊗₄-func {half} {one} {two} {zero} triv ()
⊗₄-func {half} {one} {two} {half} triv ()
⊗₄-func {half} {one} {two} {one} triv ()
⊗₄-func {half} {one} {two} {two} p₁ p₂ = triv
⊗₄-func {half} {two} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {two} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {two} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {two} {zero} {two} p₁ p₂ = triv
⊗₄-func {half} {two} {half} {zero} triv ()
⊗₄-func {half} {two} {half} {half} p₁ p₂ = triv
⊗₄-func {half} {two} {half} {one} p₁ p₂ = triv
⊗₄-func {half} {two} {half} {two} p₁ p₂ = triv
⊗₄-func {half} {two} {one} {zero} triv ()
⊗₄-func {half} {two} {one} {half} p₁ p₂ = triv
⊗₄-func {half} {two} {one} {one} p₁ p₂ = triv
⊗₄-func {half} {two} {one} {two} p₁ p₂ = triv
⊗₄-func {half} {two} {two} {zero} triv ()
⊗₄-func {half} {two} {two} {half} p₁ p₂ = triv
⊗₄-func {half} {two} {two} {one} p₁ p₂ = triv
⊗₄-func {half} {two} {two} {two} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {two} p₁ p₂ = triv
⊗₄-func {one} {zero} {half} {zero} () p₂
⊗₄-func {one} {zero} {half} {half} () p₂
⊗₄-func {one} {zero} {half} {one} () p₂
⊗₄-func {one} {zero} {half} {two} () p₂
⊗₄-func {one} {zero} {one} {zero} () p₂
⊗₄-func {one} {zero} {one} {half} () p₂
⊗₄-func {one} {zero} {one} {one} () p₂
⊗₄-func {one} {zero} {one} {two} () p₂
⊗₄-func {one} {zero} {two} {zero} () p₂
⊗₄-func {one} {zero} {two} {half} () p₂
⊗₄-func {one} {zero} {two} {one} () p₂
⊗₄-func {one} {zero} {two} {two} () p₂
⊗₄-func {one} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {two} p₁ p₂ = triv
⊗₄-func {one} {half} {half} {zero} () p₂
⊗₄-func {one} {half} {half} {half} () p₂
⊗₄-func {one} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {half} {two} p₁ p₂ = triv
⊗₄-func {one} {half} {one} {zero} () p₂
⊗₄-func {one} {half} {one} {half} () p₂
⊗₄-func {one} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {one} {two} p₁ p₂ = triv
⊗₄-func {one} {half} {two} {zero} () p₂
⊗₄-func {one} {half} {two} {half} () p₂
⊗₄-func {one} {half} {two} {one} () p₂
⊗₄-func {one} {half} {two} {two} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {two} p₁ p₂ = triv
⊗₄-func {one} {one} {half} {zero} triv ()
⊗₄-func {one} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {half} {two} p₁ p₂ = triv
⊗₄-func {one} {one} {one} {zero} triv ()
⊗₄-func {one} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {one} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {one} {two} p₁ p₂ = triv
⊗₄-func {one} {one} {two} {zero} triv ()
⊗₄-func {one} {one} {two} {half} triv ()
⊗₄-func {one} {one} {two} {one} triv ()
⊗₄-func {one} {one} {two} {two} p₁ p₂ = triv
⊗₄-func {one} {two} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {two} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {two} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {two} {zero} {two} p₁ p₂ = triv
⊗₄-func {one} {two} {half} {zero} triv ()
⊗₄-func {one} {two} {half} {half} p₁ p₂ = triv
⊗₄-func {one} {two} {half} {one} p₁ p₂ = triv
⊗₄-func {one} {two} {half} {two} p₁ p₂ = triv
⊗₄-func {one} {two} {one} {zero} triv ()
⊗₄-func {one} {two} {one} {half} p₁ p₂ = triv
⊗₄-func {one} {two} {one} {one} p₁ p₂ = triv
⊗₄-func {one} {two} {one} {two} p₁ p₂ = triv
⊗₄-func {one} {two} {two} {zero} triv ()
⊗₄-func {one} {two} {two} {half} p₁ p₂ = triv
⊗₄-func {one} {two} {two} {one} p₁ p₂ = triv
⊗₄-func {one} {two} {two} {two} p₁ p₂ = triv
⊗₄-func {two} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {two} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {two} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {two} {zero} {zero} {two} p₁ p₂ = triv
⊗₄-func {two} {zero} {half} {zero} () p₂
⊗₄-func {two} {zero} {half} {half} () p₂
⊗₄-func {two} {zero} {half} {one} () p₂
⊗₄-func {two} {zero} {half} {two} () p₂
⊗₄-func {two} {zero} {one} {zero} () p₂
⊗₄-func {two} {zero} {one} {half} () p₂
⊗₄-func {two} {zero} {one} {one} () p₂
⊗₄-func {two} {zero} {one} {two} () p₂
⊗₄-func {two} {zero} {two} {zero} () p₂
⊗₄-func {two} {zero} {two} {half} () p₂
⊗₄-func {two} {zero} {two} {one} () p₂
⊗₄-func {two} {zero} {two} {two} () p₂
⊗₄-func {two} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {two} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {two} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {two} {half} {zero} {two} p₁ p₂ = triv
⊗₄-func {two} {half} {half} {zero} () p₂
⊗₄-func {two} {half} {half} {half} () p₂
⊗₄-func {two} {half} {half} {one} () p₂
⊗₄-func {two} {half} {half} {two} p₁ p₂ = triv
⊗₄-func {two} {half} {one} {zero} () p₂
⊗₄-func {two} {half} {one} {half} () p₂
⊗₄-func {two} {half} {one} {one} () p₂
⊗₄-func {two} {half} {one} {two} p₁ p₂ = triv
⊗₄-func {two} {half} {two} {zero} () p₂
⊗₄-func {two} {half} {two} {half} () p₂
⊗₄-func {two} {half} {two} {one} () p₂
⊗₄-func {two} {half} {two} {two} p₁ p₂ = triv
⊗₄-func {two} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {two} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {two} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {two} {one} {zero} {two} p₁ p₂ = triv
⊗₄-func {two} {one} {half} {zero} () p₂
⊗₄-func {two} {one} {half} {half} () p₂
⊗₄-func {two} {one} {half} {one} () p₂
⊗₄-func {two} {one} {half} {two} p₁ p₂ = triv
⊗₄-func {two} {one} {one} {zero} () p₂
⊗₄-func {two} {one} {one} {half} () p₂
⊗₄-func {two} {one} {one} {one} () p₂
⊗₄-func {two} {one} {one} {two} p₁ p₂ = triv
⊗₄-func {two} {one} {two} {zero} () p₂
⊗₄-func {two} {one} {two} {half} () p₂
⊗₄-func {two} {one} {two} {one} () p₂
⊗₄-func {two} {one} {two} {two} p₁ p₂ = triv
⊗₄-func {two} {two} {zero} {zero} p₁ p₂ = triv
⊗₄-func {two} {two} {zero} {half} p₁ p₂ = triv
⊗₄-func {two} {two} {zero} {one} p₁ p₂ = triv
⊗₄-func {two} {two} {zero} {two} p₁ p₂ = triv
⊗₄-func {two} {two} {half} {zero} triv ()
⊗₄-func {two} {two} {half} {half} p₁ p₂ = triv
⊗₄-func {two} {two} {half} {one} p₁ p₂ = triv
⊗₄-func {two} {two} {half} {two} p₁ p₂ = triv
⊗₄-func {two} {two} {one} {zero} triv ()
⊗₄-func {two} {two} {one} {half} p₁ p₂ = triv
⊗₄-func {two} {two} {one} {one} p₁ p₂ = triv
⊗₄-func {two} {two} {one} {two} p₁ p₂ = triv
⊗₄-func {two} {two} {two} {zero} triv ()
⊗₄-func {two} {two} {two} {half} p₁ p₂ = triv
⊗₄-func {two} {two} {two} {one} p₁ p₂ = triv
⊗₄-func {two} {two} {two} {two} p₁ p₂ = triv

⊗₄-compat : ∀{a b c} → a ≤₄ b → (a ⊗₄ c) ≤₄ (b ⊗₄ c)
⊗₄-compat {a}{b}{c} p = ⊗₄-func {a}{b}{c}{c} p (refl₄ {c})

⊗₄-unitl : ∀{a} → (a ⊗₄ I₄) ≡ a
⊗₄-unitl {zero} = refl
⊗₄-unitl {half} = refl
⊗₄-unitl {one} = refl
⊗₄-unitl {two} = refl

⊗₄-unitr : ∀{a} → (I₄ ⊗₄ a) ≡ a
⊗₄-unitr {zero} = refl
⊗₄-unitr {half} = refl
⊗₄-unitr {one} = refl
⊗₄-unitr {two} = refl

⊗₄-sym : ∀{a b} → (a ⊗₄ b) ≡ (b ⊗₄ a)
⊗₄-sym {zero} {zero} = refl
⊗₄-sym {zero} {half} = refl
⊗₄-sym {zero} {one} = refl
⊗₄-sym {zero} {two} = refl
⊗₄-sym {half} {zero} = refl
⊗₄-sym {half} {half} = refl
⊗₄-sym {half} {one} = refl
⊗₄-sym {half} {two} = refl
⊗₄-sym {one} {zero} = refl
⊗₄-sym {one} {half} = refl
⊗₄-sym {one} {one} = refl
⊗₄-sym {one} {two} = refl
⊗₄-sym {two} {zero} = refl
⊗₄-sym {two} {half} = refl
⊗₄-sym {two} {one} = refl
⊗₄-sym {two} {two} = refl

⊗₄-assoc : ∀{a b c} → ((a ⊗₄ b) ⊗₄ c) ≡ (a ⊗₄ (b ⊗₄ c))
⊗₄-assoc {zero} {zero} {zero} = refl
⊗₄-assoc {zero} {zero} {half} = refl
⊗₄-assoc {zero} {zero} {one} = refl
⊗₄-assoc {zero} {zero} {two} = refl
⊗₄-assoc {zero} {half} {zero} = refl
⊗₄-assoc {zero} {half} {half} = refl
⊗₄-assoc {zero} {half} {one} = refl
⊗₄-assoc {zero} {half} {two} = refl
⊗₄-assoc {zero} {one} {zero} = refl
⊗₄-assoc {zero} {one} {half} = refl
⊗₄-assoc {zero} {one} {one} = refl
⊗₄-assoc {zero} {one} {two} = refl
⊗₄-assoc {zero} {two} {zero} = refl
⊗₄-assoc {zero} {two} {half} = refl
⊗₄-assoc {zero} {two} {one} = refl
⊗₄-assoc {zero} {two} {two} = refl
⊗₄-assoc {half} {zero} {zero} = refl
⊗₄-assoc {half} {zero} {half} = refl
⊗₄-assoc {half} {zero} {one} = refl
⊗₄-assoc {half} {zero} {two} = refl
⊗₄-assoc {half} {half} {zero} = refl
⊗₄-assoc {half} {half} {half} = refl
⊗₄-assoc {half} {half} {one} = refl
⊗₄-assoc {half} {half} {two} = refl
⊗₄-assoc {half} {one} {zero} = refl
⊗₄-assoc {half} {one} {half} = refl
⊗₄-assoc {half} {one} {one} = refl
⊗₄-assoc {half} {one} {two} = refl
⊗₄-assoc {half} {two} {zero} = refl
⊗₄-assoc {half} {two} {half} = refl
⊗₄-assoc {half} {two} {one} = refl
⊗₄-assoc {half} {two} {two} = refl
⊗₄-assoc {one} {zero} {zero} = refl
⊗₄-assoc {one} {zero} {half} = refl
⊗₄-assoc {one} {zero} {one} = refl
⊗₄-assoc {one} {zero} {two} = refl
⊗₄-assoc {one} {half} {zero} = refl
⊗₄-assoc {one} {half} {half} = refl
⊗₄-assoc {one} {half} {one} = refl
⊗₄-assoc {one} {half} {two} = refl
⊗₄-assoc {one} {one} {zero} = refl
⊗₄-assoc {one} {one} {half} = refl
⊗₄-assoc {one} {one} {one} = refl
⊗₄-assoc {one} {one} {two} = refl
⊗₄-assoc {one} {two} {zero} = refl
⊗₄-assoc {one} {two} {half} = refl
⊗₄-assoc {one} {two} {one} = refl
⊗₄-assoc {one} {two} {two} = refl
⊗₄-assoc {two} {zero} {zero} = refl
⊗₄-assoc {two} {zero} {half} = refl
⊗₄-assoc {two} {zero} {one} = refl
⊗₄-assoc {two} {zero} {two} = refl
⊗₄-assoc {two} {half} {zero} = refl
⊗₄-assoc {two} {half} {half} = refl
⊗₄-assoc {two} {half} {one} = refl
⊗₄-assoc {two} {half} {two} = refl
⊗₄-assoc {two} {one} {zero} = refl
⊗₄-assoc {two} {one} {half} = refl
⊗₄-assoc {two} {one} {one} = refl
⊗₄-assoc {two} {one} {two} = refl
⊗₄-assoc {two} {two} {zero} = refl
⊗₄-assoc {two} {two} {half} = refl
⊗₄-assoc {two} {two} {one} = refl
⊗₄-assoc {two} {two} {two} = refl

⊸₄-func : ∀{c a b d} → c ≤₄ a → b ≤₄ d → (a ⊸₄ b) ≤₄ (c ⊸₄ d)
⊸₄-func {zero} {zero} {zero} {zero} triv triv = triv
⊸₄-func {zero} {zero} {zero} {half} triv triv = triv
⊸₄-func {zero} {zero} {zero} {one} triv triv = triv
⊸₄-func {zero} {zero} {zero} {two} triv triv = triv
⊸₄-func {zero} {zero} {half} {zero} triv ()
⊸₄-func {zero} {zero} {half} {half} triv triv = triv
⊸₄-func {zero} {zero} {half} {one} triv triv = triv
⊸₄-func {zero} {zero} {half} {two} triv triv = triv
⊸₄-func {zero} {zero} {one} {zero} triv ()
⊸₄-func {zero} {zero} {one} {half} triv ()
⊸₄-func {zero} {zero} {one} {one} triv triv = triv
⊸₄-func {zero} {zero} {one} {two} triv triv = triv
⊸₄-func {zero} {zero} {two} {zero} triv ()
⊸₄-func {zero} {zero} {two} {half} triv ()
⊸₄-func {zero} {zero} {two} {one} triv ()
⊸₄-func {zero} {zero} {two} {two} triv triv = triv
⊸₄-func {zero} {half} {zero} {zero} triv triv = triv
⊸₄-func {zero} {half} {zero} {half} triv triv = triv
⊸₄-func {zero} {half} {zero} {one} triv triv = triv
⊸₄-func {zero} {half} {zero} {two} triv triv = triv
⊸₄-func {zero} {half} {half} {zero} triv ()
⊸₄-func {zero} {half} {half} {half} triv triv = triv
⊸₄-func {zero} {half} {half} {one} triv triv = triv
⊸₄-func {zero} {half} {half} {two} triv triv = triv
⊸₄-func {zero} {half} {one} {zero} triv ()
⊸₄-func {zero} {half} {one} {half} triv ()
⊸₄-func {zero} {half} {one} {one} triv triv = triv
⊸₄-func {zero} {half} {one} {two} triv triv = triv
⊸₄-func {zero} {half} {two} {zero} triv ()
⊸₄-func {zero} {half} {two} {half} triv ()
⊸₄-func {zero} {half} {two} {one} triv ()
⊸₄-func {zero} {half} {two} {two} triv triv = triv
⊸₄-func {zero} {one} {zero} {zero} triv triv = triv
⊸₄-func {zero} {one} {zero} {half} triv triv = triv
⊸₄-func {zero} {one} {zero} {one} triv triv = triv
⊸₄-func {zero} {one} {zero} {two} triv triv = triv
⊸₄-func {zero} {one} {half} {zero} triv ()
⊸₄-func {zero} {one} {half} {half} triv triv = triv
⊸₄-func {zero} {one} {half} {one} triv triv = triv
⊸₄-func {zero} {one} {half} {two} triv triv = triv
⊸₄-func {zero} {one} {one} {zero} triv ()
⊸₄-func {zero} {one} {one} {half} triv ()
⊸₄-func {zero} {one} {one} {one} triv triv = triv
⊸₄-func {zero} {one} {one} {two} triv triv = triv
⊸₄-func {zero} {one} {two} {zero} triv ()
⊸₄-func {zero} {one} {two} {half} triv ()
⊸₄-func {zero} {one} {two} {one} triv ()
⊸₄-func {zero} {one} {two} {two} triv triv = triv
⊸₄-func {zero} {two} {zero} {zero} triv triv = triv
⊸₄-func {zero} {two} {zero} {half} triv triv = triv
⊸₄-func {zero} {two} {zero} {one} triv triv = triv
⊸₄-func {zero} {two} {zero} {two} triv triv = triv
⊸₄-func {zero} {two} {half} {zero} triv ()
⊸₄-func {zero} {two} {half} {half} triv triv = triv
⊸₄-func {zero} {two} {half} {one} triv triv = triv
⊸₄-func {zero} {two} {half} {two} triv triv = triv
⊸₄-func {zero} {two} {one} {zero} triv ()
⊸₄-func {zero} {two} {one} {half} triv ()
⊸₄-func {zero} {two} {one} {one} triv triv = triv
⊸₄-func {zero} {two} {one} {two} triv triv = triv
⊸₄-func {zero} {two} {two} {zero} triv ()
⊸₄-func {zero} {two} {two} {half} triv ()
⊸₄-func {zero} {two} {two} {one} triv ()
⊸₄-func {zero} {two} {two} {two} triv triv = triv
⊸₄-func {half} {zero} {zero} {zero} () p₂
⊸₄-func {half} {zero} {zero} {half} () p₂
⊸₄-func {half} {zero} {zero} {one} () p₂
⊸₄-func {half} {zero} {zero} {two} () p₂
⊸₄-func {half} {zero} {half} {zero} () p₂
⊸₄-func {half} {zero} {half} {half} () p₂
⊸₄-func {half} {zero} {half} {one} () p₂
⊸₄-func {half} {zero} {half} {two} () p₂
⊸₄-func {half} {zero} {one} {zero} () p₂
⊸₄-func {half} {zero} {one} {half} () p₂
⊸₄-func {half} {zero} {one} {one} () p₂
⊸₄-func {half} {zero} {one} {two} () p₂
⊸₄-func {half} {zero} {two} {zero} () p₂
⊸₄-func {half} {zero} {two} {half} () p₂
⊸₄-func {half} {zero} {two} {one} () p₂
⊸₄-func {half} {zero} {two} {two} () p₂
⊸₄-func {half} {half} {zero} {zero} triv triv = triv
⊸₄-func {half} {half} {zero} {half} triv triv = triv
⊸₄-func {half} {half} {zero} {one} triv triv = triv
⊸₄-func {half} {half} {zero} {two} triv triv = triv
⊸₄-func {half} {half} {half} {zero} triv ()
⊸₄-func {half} {half} {half} {half} triv triv = triv
⊸₄-func {half} {half} {half} {one} triv triv = triv
⊸₄-func {half} {half} {half} {two} triv triv = triv
⊸₄-func {half} {half} {one} {zero} triv ()
⊸₄-func {half} {half} {one} {half} triv ()
⊸₄-func {half} {half} {one} {one} triv triv = triv
⊸₄-func {half} {half} {one} {two} triv triv = triv
⊸₄-func {half} {half} {two} {zero} triv ()
⊸₄-func {half} {half} {two} {half} triv ()
⊸₄-func {half} {half} {two} {one} triv ()
⊸₄-func {half} {half} {two} {two} triv triv = triv
⊸₄-func {half} {one} {zero} {zero} triv triv = triv
⊸₄-func {half} {one} {zero} {half} triv triv = triv
⊸₄-func {half} {one} {zero} {one} triv triv = triv
⊸₄-func {half} {one} {zero} {two} triv triv = triv
⊸₄-func {half} {one} {half} {zero} triv ()
⊸₄-func {half} {one} {half} {half} triv triv = triv
⊸₄-func {half} {one} {half} {one} triv triv = triv
⊸₄-func {half} {one} {half} {two} triv triv = triv
⊸₄-func {half} {one} {one} {zero} triv ()
⊸₄-func {half} {one} {one} {half} triv ()
⊸₄-func {half} {one} {one} {one} triv triv = triv
⊸₄-func {half} {one} {one} {two} triv triv = triv
⊸₄-func {half} {one} {two} {zero} triv ()
⊸₄-func {half} {one} {two} {half} triv ()
⊸₄-func {half} {one} {two} {one} triv ()
⊸₄-func {half} {one} {two} {two} triv triv = triv
⊸₄-func {half} {two} {zero} {zero} triv triv = triv
⊸₄-func {half} {two} {zero} {half} triv triv = triv
⊸₄-func {half} {two} {zero} {one} triv triv = triv
⊸₄-func {half} {two} {zero} {two} triv triv = triv
⊸₄-func {half} {two} {half} {zero} triv ()
⊸₄-func {half} {two} {half} {half} triv triv = triv
⊸₄-func {half} {two} {half} {one} triv triv = triv
⊸₄-func {half} {two} {half} {two} triv triv = triv
⊸₄-func {half} {two} {one} {zero} triv ()
⊸₄-func {half} {two} {one} {half} triv ()
⊸₄-func {half} {two} {one} {one} triv triv = triv
⊸₄-func {half} {two} {one} {two} triv triv = triv
⊸₄-func {half} {two} {two} {zero} triv ()
⊸₄-func {half} {two} {two} {half} triv ()
⊸₄-func {half} {two} {two} {one} triv ()
⊸₄-func {half} {two} {two} {two} triv triv = triv
⊸₄-func {one} {zero} {zero} {zero} () p₂
⊸₄-func {one} {zero} {zero} {half} () p₂
⊸₄-func {one} {zero} {zero} {one} () p₂
⊸₄-func {one} {zero} {zero} {two} () p₂
⊸₄-func {one} {zero} {half} {zero} () p₂
⊸₄-func {one} {zero} {half} {half} () p₂
⊸₄-func {one} {zero} {half} {one} () p₂
⊸₄-func {one} {zero} {half} {two} () p₂
⊸₄-func {one} {zero} {one} {zero} () p₂
⊸₄-func {one} {zero} {one} {half} () p₂
⊸₄-func {one} {zero} {one} {one} () p₂
⊸₄-func {one} {zero} {one} {two} () p₂
⊸₄-func {one} {zero} {two} {zero} () p₂
⊸₄-func {one} {zero} {two} {half} () p₂
⊸₄-func {one} {zero} {two} {one} () p₂
⊸₄-func {one} {zero} {two} {two} () p₂
⊸₄-func {one} {half} {zero} {zero} () p₂
⊸₄-func {one} {half} {zero} {half} () p₂
⊸₄-func {one} {half} {zero} {one} () p₂
⊸₄-func {one} {half} {zero} {two} () p₂
⊸₄-func {one} {half} {half} {zero} () p₂
⊸₄-func {one} {half} {half} {half} () p₂
⊸₄-func {one} {half} {half} {one} () p₂
⊸₄-func {one} {half} {half} {two} () p₂
⊸₄-func {one} {half} {one} {zero} () p₂
⊸₄-func {one} {half} {one} {half} () p₂
⊸₄-func {one} {half} {one} {one} () p₂
⊸₄-func {one} {half} {one} {two} () p₂
⊸₄-func {one} {half} {two} {zero} () p₂
⊸₄-func {one} {half} {two} {half} () p₂
⊸₄-func {one} {half} {two} {one} () p₂
⊸₄-func {one} {half} {two} {two} () p₂
⊸₄-func {one} {one} {zero} {zero} triv triv = triv
⊸₄-func {one} {one} {zero} {half} triv triv = triv
⊸₄-func {one} {one} {zero} {one} triv triv = triv
⊸₄-func {one} {one} {zero} {two} triv triv = triv
⊸₄-func {one} {one} {half} {zero} triv ()
⊸₄-func {one} {one} {half} {half} triv triv = triv
⊸₄-func {one} {one} {half} {one} triv triv = triv
⊸₄-func {one} {one} {half} {two} triv triv = triv
⊸₄-func {one} {one} {one} {zero} triv ()
⊸₄-func {one} {one} {one} {half} triv ()
⊸₄-func {one} {one} {one} {one} triv triv = triv
⊸₄-func {one} {one} {one} {two} triv triv = triv
⊸₄-func {one} {one} {two} {zero} triv ()
⊸₄-func {one} {one} {two} {half} triv ()
⊸₄-func {one} {one} {two} {one} triv ()
⊸₄-func {one} {one} {two} {two} triv triv = triv
⊸₄-func {one} {two} {zero} {zero} triv triv = triv
⊸₄-func {one} {two} {zero} {half} triv triv = triv
⊸₄-func {one} {two} {zero} {one} triv triv = triv
⊸₄-func {one} {two} {zero} {two} triv triv = triv
⊸₄-func {one} {two} {half} {zero} triv ()
⊸₄-func {one} {two} {half} {half} triv triv = triv
⊸₄-func {one} {two} {half} {one} triv triv = triv
⊸₄-func {one} {two} {half} {two} triv triv = triv
⊸₄-func {one} {two} {one} {zero} triv ()
⊸₄-func {one} {two} {one} {half} triv ()
⊸₄-func {one} {two} {one} {one} triv triv = triv
⊸₄-func {one} {two} {one} {two} triv triv = triv
⊸₄-func {one} {two} {two} {zero} triv ()
⊸₄-func {one} {two} {two} {half} triv ()
⊸₄-func {one} {two} {two} {one} triv ()
⊸₄-func {one} {two} {two} {two} triv triv = triv
⊸₄-func {two} {zero} {zero} {zero} () p₂
⊸₄-func {two} {zero} {zero} {half} () p₂
⊸₄-func {two} {zero} {zero} {one} () p₂
⊸₄-func {two} {zero} {zero} {two} () p₂
⊸₄-func {two} {zero} {half} {zero} () p₂
⊸₄-func {two} {zero} {half} {half} () p₂
⊸₄-func {two} {zero} {half} {one} () p₂
⊸₄-func {two} {zero} {half} {two} () p₂
⊸₄-func {two} {zero} {one} {zero} () p₂
⊸₄-func {two} {zero} {one} {half} () p₂
⊸₄-func {two} {zero} {one} {one} () p₂
⊸₄-func {two} {zero} {one} {two} () p₂
⊸₄-func {two} {zero} {two} {zero} () p₂
⊸₄-func {two} {zero} {two} {half} () p₂
⊸₄-func {two} {zero} {two} {one} () p₂
⊸₄-func {two} {zero} {two} {two} () p₂
⊸₄-func {two} {half} {zero} {zero} () p₂
⊸₄-func {two} {half} {zero} {half} () p₂
⊸₄-func {two} {half} {zero} {one} () p₂
⊸₄-func {two} {half} {zero} {two} () p₂
⊸₄-func {two} {half} {half} {zero} () p₂
⊸₄-func {two} {half} {half} {half} () p₂
⊸₄-func {two} {half} {half} {one} () p₂
⊸₄-func {two} {half} {half} {two} () p₂
⊸₄-func {two} {half} {one} {zero} () p₂
⊸₄-func {two} {half} {one} {half} () p₂
⊸₄-func {two} {half} {one} {one} () p₂
⊸₄-func {two} {half} {one} {two} () p₂
⊸₄-func {two} {half} {two} {zero} () p₂
⊸₄-func {two} {half} {two} {half} () p₂
⊸₄-func {two} {half} {two} {one} () p₂
⊸₄-func {two} {half} {two} {two} () p₂
⊸₄-func {two} {one} {zero} {zero} () p₂
⊸₄-func {two} {one} {zero} {half} () p₂
⊸₄-func {two} {one} {zero} {one} () p₂
⊸₄-func {two} {one} {zero} {two} () p₂
⊸₄-func {two} {one} {half} {zero} () p₂
⊸₄-func {two} {one} {half} {half} () p₂
⊸₄-func {two} {one} {half} {one} () p₂
⊸₄-func {two} {one} {half} {two} () p₂
⊸₄-func {two} {one} {one} {zero} () p₂
⊸₄-func {two} {one} {one} {half} () p₂
⊸₄-func {two} {one} {one} {one} () p₂
⊸₄-func {two} {one} {one} {two} () p₂
⊸₄-func {two} {one} {two} {zero} () p₂
⊸₄-func {two} {one} {two} {half} () p₂
⊸₄-func {two} {one} {two} {one} () p₂
⊸₄-func {two} {one} {two} {two} () p₂
⊸₄-func {two} {two} {zero} {zero} triv triv = triv
⊸₄-func {two} {two} {zero} {half} triv triv = triv
⊸₄-func {two} {two} {zero} {one} triv triv = triv
⊸₄-func {two} {two} {zero} {two} triv triv = triv
⊸₄-func {two} {two} {half} {zero} triv ()
⊸₄-func {two} {two} {half} {half} triv triv = triv
⊸₄-func {two} {two} {half} {one} triv triv = triv
⊸₄-func {two} {two} {half} {two} triv triv = triv
⊸₄-func {two} {two} {one} {zero} triv ()
⊸₄-func {two} {two} {one} {half} triv ()
⊸₄-func {two} {two} {one} {one} triv triv = triv
⊸₄-func {two} {two} {one} {two} triv triv = triv
⊸₄-func {two} {two} {two} {zero} triv ()
⊸₄-func {two} {two} {two} {half} triv ()
⊸₄-func {two} {two} {two} {one} triv ()
⊸₄-func {two} {two} {two} {two} triv triv = triv

curry₄ : ∀{a b c} → (a ⊗₄ b) ≤₄ c → a ≤₄ (b ⊸₄ c)
curry₄ {zero} {zero} {zero} p = triv
curry₄ {zero} {zero} {half} p = triv
curry₄ {zero} {zero} {one} p = triv
curry₄ {zero} {zero} {two} p = triv
curry₄ {zero} {half} {zero} p = triv
curry₄ {zero} {half} {half} p = triv
curry₄ {zero} {half} {one} p = triv
curry₄ {zero} {half} {two} p = triv
curry₄ {zero} {one} {zero} p = triv
curry₄ {zero} {one} {half} p = triv
curry₄ {zero} {one} {one} p = triv
curry₄ {zero} {one} {two} p = triv
curry₄ {zero} {two} {zero} p = triv
curry₄ {zero} {two} {half} p = triv
curry₄ {zero} {two} {one} p = triv
curry₄ {zero} {two} {two} p = triv
curry₄ {half} {zero} {zero} p = triv
curry₄ {half} {zero} {half} p = triv
curry₄ {half} {zero} {one} p = triv
curry₄ {half} {zero} {two} p = triv
curry₄ {half} {half} {zero} ()
curry₄ {half} {half} {half} p = triv
curry₄ {half} {half} {one} p = triv
curry₄ {half} {half} {two} p = triv
curry₄ {half} {one} {zero} ()
curry₄ {half} {one} {half} ()
curry₄ {half} {one} {one} p = triv
curry₄ {half} {one} {two} p = triv
curry₄ {half} {two} {zero} ()
curry₄ {half} {two} {half} ()
curry₄ {half} {two} {one} ()
curry₄ {half} {two} {two} p = triv
curry₄ {one} {zero} {zero} p = triv
curry₄ {one} {zero} {half} p = triv
curry₄ {one} {zero} {one} p = triv
curry₄ {one} {zero} {two} p = triv
curry₄ {one} {half} {zero} ()
curry₄ {one} {half} {half} ()
curry₄ {one} {half} {one} p = triv
curry₄ {one} {half} {two} p = triv
curry₄ {one} {one} {zero} ()
curry₄ {one} {one} {half} ()
curry₄ {one} {one} {one} p = triv
curry₄ {one} {one} {two} p = triv
curry₄ {one} {two} {zero} ()
curry₄ {one} {two} {half} ()
curry₄ {one} {two} {one} ()
curry₄ {one} {two} {two} p = triv
curry₄ {two} {zero} {zero} p = triv
curry₄ {two} {zero} {half} p = triv
curry₄ {two} {zero} {one} p = triv
curry₄ {two} {zero} {two} p = triv
curry₄ {two} {half} {zero} ()
curry₄ {two} {half} {half} ()
curry₄ {two} {half} {one} ()
curry₄ {two} {half} {two} p = triv
curry₄ {two} {one} {zero} ()
curry₄ {two} {one} {half} ()
curry₄ {two} {one} {one} ()
curry₄ {two} {one} {two} p = triv
curry₄ {two} {two} {zero} ()
curry₄ {two} {two} {half} ()
curry₄ {two} {two} {one} ()
curry₄ {two} {two} {two} p = triv

curry₄-inv : ∀{a b c} → a ≤₄ (b ⊸₄ c) → (a ⊗₄ b) ≤₄ c
curry₄-inv {zero} {zero} {zero} p = triv
curry₄-inv {zero} {zero} {half} p = triv
curry₄-inv {zero} {zero} {one} p = triv
curry₄-inv {zero} {zero} {two} p = triv
curry₄-inv {zero} {half} {zero} p = triv
curry₄-inv {zero} {half} {half} p = triv
curry₄-inv {zero} {half} {one} p = triv
curry₄-inv {zero} {half} {two} p = triv
curry₄-inv {zero} {one} {zero} p = triv
curry₄-inv {zero} {one} {half} p = triv
curry₄-inv {zero} {one} {one} p = triv
curry₄-inv {zero} {one} {two} p = triv
curry₄-inv {zero} {two} {zero} p = triv
curry₄-inv {zero} {two} {half} p = triv
curry₄-inv {zero} {two} {one} p = triv
curry₄-inv {zero} {two} {two} p = triv
curry₄-inv {half} {zero} {zero} p = triv
curry₄-inv {half} {zero} {half} p = triv
curry₄-inv {half} {zero} {one} p = triv
curry₄-inv {half} {zero} {two} p = triv
curry₄-inv {half} {half} {zero} ()
curry₄-inv {half} {half} {half} p = triv
curry₄-inv {half} {half} {one} p = triv
curry₄-inv {half} {half} {two} p = triv
curry₄-inv {half} {one} {zero} ()
curry₄-inv {half} {one} {half} ()
curry₄-inv {half} {one} {one} p = triv
curry₄-inv {half} {one} {two} p = triv
curry₄-inv {half} {two} {zero} ()
curry₄-inv {half} {two} {half} ()
curry₄-inv {half} {two} {one} ()
curry₄-inv {half} {two} {two} p = triv
curry₄-inv {one} {zero} {zero} p = triv
curry₄-inv {one} {zero} {half} p = triv
curry₄-inv {one} {zero} {one} p = triv
curry₄-inv {one} {zero} {two} p = triv
curry₄-inv {one} {half} {zero} ()
curry₄-inv {one} {half} {half} ()
curry₄-inv {one} {half} {one} p = triv
curry₄-inv {one} {half} {two} p = triv
curry₄-inv {one} {one} {zero} ()
curry₄-inv {one} {one} {half} ()
curry₄-inv {one} {one} {one} p = triv
curry₄-inv {one} {one} {two} p = triv
curry₄-inv {one} {two} {zero} ()
curry₄-inv {one} {two} {half} ()
curry₄-inv {one} {two} {one} ()
curry₄-inv {one} {two} {two} p = triv
curry₄-inv {two} {zero} {zero} p = triv
curry₄-inv {two} {zero} {half} p = triv
curry₄-inv {two} {zero} {one} p = triv
curry₄-inv {two} {zero} {two} p = triv
curry₄-inv {two} {half} {zero} ()
curry₄-inv {two} {half} {half} ()
curry₄-inv {two} {half} {one} ()
curry₄-inv {two} {half} {two} p = triv
curry₄-inv {two} {one} {zero} ()
curry₄-inv {two} {one} {half} ()
curry₄-inv {two} {one} {one} ()
curry₄-inv {two} {one} {two} p = triv
curry₄-inv {two} {two} {zero} ()
curry₄-inv {two} {two} {half} ()
curry₄-inv {two} {two} {one} ()
curry₄-inv {two} {two} {two} p = triv
