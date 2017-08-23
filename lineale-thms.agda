module lineale-thms where

open import prelude
open import lineale

refl₄ : ∀{a} → a ≤₄ a
refl₄ {zero} = triv
refl₄ {forth} = triv
refl₄ {half} = triv
refl₄ {one} = triv

trans₄ : ∀{a b c} → a ≤₄ b → b ≤₄ c → a ≤₄ c
trans₄ {zero} {zero} {zero} p₁ p₂ = triv
trans₄ {zero} {zero} {forth} p₁ p₂ = triv
trans₄ {zero} {zero} {half} p₁ p₂ = triv
trans₄ {zero} {zero} {one} p₁ p₂ = triv
trans₄ {zero} {forth} {zero} p₁ p₂ = triv
trans₄ {zero} {forth} {forth} p₁ p₂ = triv
trans₄ {zero} {forth} {half} p₁ p₂ = triv
trans₄ {zero} {forth} {one} p₁ p₂ = triv
trans₄ {zero} {half} {zero} p₁ p₂ = triv
trans₄ {zero} {half} {forth} p₁ p₂ = triv
trans₄ {zero} {half} {half} p₁ p₂ = triv
trans₄ {zero} {half} {one} p₁ p₂ = triv
trans₄ {zero} {one} {zero} p₁ p₂ = triv
trans₄ {zero} {one} {forth} p₁ p₂ = triv
trans₄ {zero} {one} {half} p₁ p₂ = triv
trans₄ {zero} {one} {one} p₁ p₂ = triv
trans₄ {forth} {zero} {zero} () p₂
trans₄ {forth} {zero} {forth} p₁ p₂ = triv
trans₄ {forth} {zero} {half} p₁ p₂ = triv
trans₄ {forth} {zero} {one} p₁ p₂ = triv
trans₄ {forth} {forth} {zero} p₁ ()
trans₄ {forth} {forth} {forth} p₁ p₂ = triv
trans₄ {forth} {forth} {half} p₁ p₂ = triv
trans₄ {forth} {forth} {one} p₁ p₂ = triv
trans₄ {forth} {half} {zero} p₁ ()
trans₄ {forth} {half} {forth} p₁ p₂ = triv
trans₄ {forth} {half} {half} p₁ p₂ = triv
trans₄ {forth} {half} {one} p₁ p₂ = triv
trans₄ {forth} {one} {zero} p₁ ()
trans₄ {forth} {one} {forth} p₁ p₂ = triv
trans₄ {forth} {one} {half} p₁ p₂ = triv
trans₄ {forth} {one} {one} p₁ p₂ = triv
trans₄ {half} {zero} {zero} () p₂
trans₄ {half} {zero} {forth} () p₂
trans₄ {half} {zero} {half} p₁ p₂ = triv
trans₄ {half} {zero} {one} p₁ p₂ = triv
trans₄ {half} {forth} {zero} () ()
trans₄ {half} {forth} {forth} () p₂
trans₄ {half} {forth} {half} p₁ p₂ = triv
trans₄ {half} {forth} {one} p₁ p₂ = triv
trans₄ {half} {half} {zero} p₁ ()
trans₄ {half} {half} {forth} p₁ ()
trans₄ {half} {half} {half} p₁ p₂ = triv
trans₄ {half} {half} {one} p₁ p₂ = triv
trans₄ {half} {one} {zero} p₁ ()
trans₄ {half} {one} {forth} p₁ ()
trans₄ {half} {one} {half} p₁ p₂ = triv
trans₄ {half} {one} {one} p₁ p₂ = triv
trans₄ {one} {zero} {zero} () p₂
trans₄ {one} {zero} {forth} () p₂
trans₄ {one} {zero} {half} () p₂
trans₄ {one} {zero} {one} p₁ p₂ = triv
trans₄ {one} {forth} {zero} () ()
trans₄ {one} {forth} {forth} () p₂
trans₄ {one} {forth} {half} () p₂
trans₄ {one} {forth} {one} p₁ p₂ = triv
trans₄ {one} {half} {zero} () ()
trans₄ {one} {half} {forth} () ()
trans₄ {one} {half} {half} () p₂
trans₄ {one} {half} {one} p₁ p₂ = triv
trans₄ {one} {one} {zero} p₁ ()
trans₄ {one} {one} {forth} p₁ ()
trans₄ {one} {one} {half} p₁ ()
trans₄ {one} {one} {one} p₁ p₂ = triv

iso₄ : ∀{a b} → a ≤₄ b → b ≤₄ a → a ≡ b
iso₄ {zero} {zero} p₁ p₂ = refl
iso₄ {zero} {forth} p₁ ()
iso₄ {zero} {half} p₁ ()
iso₄ {zero} {one} p₁ ()
iso₄ {forth} {zero} () p₂
iso₄ {forth} {forth} p₁ p₂ = refl
iso₄ {forth} {half} p₁ ()
iso₄ {forth} {one} p₁ ()
iso₄ {half} {zero} () p₂
iso₄ {half} {forth} () p₂
iso₄ {half} {half} p₁ p₂ = refl
iso₄ {half} {one} p₁ ()
iso₄ {one} {zero} () p₂
iso₄ {one} {forth} () p₂
iso₄ {one} {half} () p₂
iso₄ {one} {one} p₁ p₂ = refl

iso₄-inv : ∀{a b} → a ≡ b → ((a ≤₄ b) × (b ≤₄ a))
iso₄-inv {zero} {zero} p = triv , triv
iso₄-inv {zero} {forth} ()
iso₄-inv {zero} {half} ()
iso₄-inv {zero} {one} ()
iso₄-inv {forth} {zero} ()
iso₄-inv {forth} {forth} p = triv , triv
iso₄-inv {forth} {half} ()
iso₄-inv {forth} {one} ()
iso₄-inv {half} {zero} ()
iso₄-inv {half} {forth} ()
iso₄-inv {half} {half} p = triv , triv
iso₄-inv {half} {one} ()
iso₄-inv {one} {zero} ()
iso₄-inv {one} {forth} ()
iso₄-inv {one} {half} ()
iso₄-inv {one} {one} p = triv , triv

⊙₄-zerol : ∀{x} → (zero ⊙₄ x) ≤₄ zero
⊙₄-zerol {zero} = triv
⊙₄-zerol {forth} = triv
⊙₄-zerol {half} = triv
⊙₄-zerol {one} = triv

⊙₄-zeror : ∀{x} → (x ⊙₄ zero) ≤₄ zero
⊙₄-zeror {zero} = triv
⊙₄-zeror {forth} = triv
⊙₄-zeror {half} = triv
⊙₄-zeror {one} = triv

⊙₄-contract : (∀{a} → (a ⊙₄ a) ≡ a) → ⊥ {lzero}
⊙₄-contract p with p {forth} 
... | () 

⊙₄-sym : ∀{a b} → a ⊙₄ b ≡ b ⊙₄ a
⊙₄-sym {zero} {zero} = refl
⊙₄-sym {zero} {forth} = refl
⊙₄-sym {zero} {half} = refl
⊙₄-sym {zero} {one} = refl
⊙₄-sym {forth} {zero} = refl
⊙₄-sym {forth} {forth} = refl
⊙₄-sym {forth} {half} = refl
⊙₄-sym {forth} {one} = refl
⊙₄-sym {half} {zero} = refl
⊙₄-sym {half} {forth} = refl
⊙₄-sym {half} {half} = refl
⊙₄-sym {half} {one} = refl
⊙₄-sym {one} {zero} = refl
⊙₄-sym {one} {forth} = refl
⊙₄-sym {one} {half} = refl
⊙₄-sym {one} {one} = refl

⊙₄-assoc : ∀{a b c} → (a ⊙₄ b) ⊙₄ c ≡ a ⊙₄ (b ⊙₄ c)
⊙₄-assoc {zero} {zero} {zero} = refl
⊙₄-assoc {zero} {zero} {forth} = refl
⊙₄-assoc {zero} {zero} {half} = refl
⊙₄-assoc {zero} {zero} {one} = refl
⊙₄-assoc {zero} {forth} {zero} = refl
⊙₄-assoc {zero} {forth} {forth} = refl
⊙₄-assoc {zero} {forth} {half} = refl
⊙₄-assoc {zero} {forth} {one} = refl
⊙₄-assoc {zero} {half} {zero} = refl
⊙₄-assoc {zero} {half} {forth} = refl
⊙₄-assoc {zero} {half} {half} = refl
⊙₄-assoc {zero} {half} {one} = refl
⊙₄-assoc {zero} {one} {zero} = refl
⊙₄-assoc {zero} {one} {forth} = refl
⊙₄-assoc {zero} {one} {half} = refl
⊙₄-assoc {zero} {one} {one} = refl
⊙₄-assoc {forth} {zero} {zero} = refl
⊙₄-assoc {forth} {zero} {forth} = refl
⊙₄-assoc {forth} {zero} {half} = refl
⊙₄-assoc {forth} {zero} {one} = refl
⊙₄-assoc {forth} {forth} {zero} = refl
⊙₄-assoc {forth} {forth} {forth} = refl
⊙₄-assoc {forth} {forth} {half} = refl
⊙₄-assoc {forth} {forth} {one} = refl
⊙₄-assoc {forth} {half} {zero} = refl
⊙₄-assoc {forth} {half} {forth} = refl
⊙₄-assoc {forth} {half} {half} = refl
⊙₄-assoc {forth} {half} {one} = refl
⊙₄-assoc {forth} {one} {zero} = refl
⊙₄-assoc {forth} {one} {forth} = refl
⊙₄-assoc {forth} {one} {half} = refl
⊙₄-assoc {forth} {one} {one} = refl
⊙₄-assoc {half} {zero} {zero} = refl
⊙₄-assoc {half} {zero} {forth} = refl
⊙₄-assoc {half} {zero} {half} = refl
⊙₄-assoc {half} {zero} {one} = refl
⊙₄-assoc {half} {forth} {zero} = refl
⊙₄-assoc {half} {forth} {forth} = refl
⊙₄-assoc {half} {forth} {half} = refl
⊙₄-assoc {half} {forth} {one} = refl
⊙₄-assoc {half} {half} {zero} = refl
⊙₄-assoc {half} {half} {forth} = refl
⊙₄-assoc {half} {half} {half} = refl
⊙₄-assoc {half} {half} {one} = refl
⊙₄-assoc {half} {one} {zero} = refl
⊙₄-assoc {half} {one} {forth} = refl
⊙₄-assoc {half} {one} {half} = refl
⊙₄-assoc {half} {one} {one} = refl
⊙₄-assoc {one} {zero} {zero} = refl
⊙₄-assoc {one} {zero} {forth} = refl
⊙₄-assoc {one} {zero} {half} = refl
⊙₄-assoc {one} {zero} {one} = refl
⊙₄-assoc {one} {forth} {zero} = refl
⊙₄-assoc {one} {forth} {forth} = refl
⊙₄-assoc {one} {forth} {half} = refl
⊙₄-assoc {one} {forth} {one} = refl
⊙₄-assoc {one} {half} {zero} = refl
⊙₄-assoc {one} {half} {forth} = refl
⊙₄-assoc {one} {half} {half} = refl
⊙₄-assoc {one} {half} {one} = refl
⊙₄-assoc {one} {one} {zero} = refl
⊙₄-assoc {one} {one} {forth} = refl
⊙₄-assoc {one} {one} {half} = refl
⊙₄-assoc {one} {one} {one} = refl

⊙₄-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ⊙₄ b) ≤₄ (c ⊙₄ d)
⊙₄-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
⊙₄-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
⊙₄-func {zero} {zero} {forth} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {forth} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {forth} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {forth} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
⊙₄-func {zero} {forth} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {forth} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
⊙₄-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
⊙₄-func {zero} {forth} {forth} {half} p₁ p₂ = triv
⊙₄-func {zero} {forth} {forth} {one} p₁ p₂ = triv
⊙₄-func {zero} {forth} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {forth} {half} {forth} p₁ p₂ = triv
⊙₄-func {zero} {forth} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {forth} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {forth} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {forth} {one} {forth} p₁ p₂ = triv
⊙₄-func {zero} {forth} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {forth} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {forth} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {forth} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {forth} {forth} p₁ p₂ = triv
⊙₄-func {zero} {half} {forth} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {forth} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {forth} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {forth} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {half} {one} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {forth} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {forth} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {forth} {forth} p₁ p₂ = triv
⊙₄-func {zero} {one} {forth} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {forth} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {forth} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {forth} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {half} p₁ p₂ = triv
⊙₄-func {zero} {one} {one} {one} p₁ p₂ = triv
⊙₄-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
⊙₄-func {forth} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {forth} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {forth} {zero} {forth} {zero} () ()
⊙₄-func {forth} {zero} {forth} {forth} () p₂
⊙₄-func {forth} {zero} {forth} {half} () p₂
⊙₄-func {forth} {zero} {forth} {one} () p₂
⊙₄-func {forth} {zero} {half} {zero} () ()
⊙₄-func {forth} {zero} {half} {forth} () ()
⊙₄-func {forth} {zero} {half} {half} () p₂
⊙₄-func {forth} {zero} {half} {one} () p₂
⊙₄-func {forth} {zero} {one} {zero} () ()
⊙₄-func {forth} {zero} {one} {forth} () ()
⊙₄-func {forth} {zero} {one} {half} () ()
⊙₄-func {forth} {zero} {one} {one} () p₂
⊙₄-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
⊙₄-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
⊙₄-func {forth} {forth} {zero} {half} p₁ p₂ = triv
⊙₄-func {forth} {forth} {zero} {one} p₁ p₂ = triv
⊙₄-func {forth} {forth} {forth} {zero} p₁ ()
⊙₄-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
⊙₄-func {forth} {forth} {forth} {half} p₁ p₂ = triv
⊙₄-func {forth} {forth} {forth} {one} p₁ p₂ = triv
⊙₄-func {forth} {forth} {half} {zero} p₁ ()
⊙₄-func {forth} {forth} {half} {forth} p₁ p₂ = triv
⊙₄-func {forth} {forth} {half} {half} p₁ p₂ = triv
⊙₄-func {forth} {forth} {half} {one} p₁ p₂ = triv
⊙₄-func {forth} {forth} {one} {zero} p₁ ()
⊙₄-func {forth} {forth} {one} {forth} p₁ p₂ = triv
⊙₄-func {forth} {forth} {one} {half} p₁ p₂ = triv
⊙₄-func {forth} {forth} {one} {one} p₁ p₂ = triv
⊙₄-func {forth} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {forth} {half} {zero} {forth} p₁ p₂ = triv
⊙₄-func {forth} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {forth} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {forth} {half} {forth} {zero} p₁ ()
⊙₄-func {forth} {half} {forth} {forth} p₁ p₂ = triv
⊙₄-func {forth} {half} {forth} {half} p₁ p₂ = triv
⊙₄-func {forth} {half} {forth} {one} p₁ p₂ = triv
⊙₄-func {forth} {half} {half} {zero} p₁ ()
⊙₄-func {forth} {half} {half} {forth} p₁ p₂ = triv
⊙₄-func {forth} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {forth} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {forth} {half} {one} {zero} p₁ ()
⊙₄-func {forth} {half} {one} {forth} p₁ p₂ = triv
⊙₄-func {forth} {half} {one} {half} p₁ p₂ = triv
⊙₄-func {forth} {half} {one} {one} p₁ p₂ = triv
⊙₄-func {forth} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {forth} {one} {zero} {forth} p₁ p₂ = triv
⊙₄-func {forth} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {forth} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {forth} {one} {forth} {zero} p₁ ()
⊙₄-func {forth} {one} {forth} {forth} p₁ p₂ = triv
⊙₄-func {forth} {one} {forth} {half} p₁ p₂ = triv
⊙₄-func {forth} {one} {forth} {one} p₁ p₂ = triv
⊙₄-func {forth} {one} {half} {zero} p₁ ()
⊙₄-func {forth} {one} {half} {forth} p₁ p₂ = triv
⊙₄-func {forth} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {forth} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {forth} {one} {one} {zero} p₁ ()
⊙₄-func {forth} {one} {one} {forth} p₁ p₂ = triv
⊙₄-func {forth} {one} {one} {half} p₁ p₂ = triv
⊙₄-func {forth} {one} {one} {one} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {forth} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {zero} {forth} {zero} () ()
⊙₄-func {half} {zero} {forth} {forth} () p₂
⊙₄-func {half} {zero} {forth} {half} () p₂
⊙₄-func {half} {zero} {forth} {one} () p₂
⊙₄-func {half} {zero} {half} {zero} () ()
⊙₄-func {half} {zero} {half} {forth} () ()
⊙₄-func {half} {zero} {half} {half} () p₂
⊙₄-func {half} {zero} {half} {one} () p₂
⊙₄-func {half} {zero} {one} {zero} () ()
⊙₄-func {half} {zero} {one} {forth} () ()
⊙₄-func {half} {zero} {one} {half} () ()
⊙₄-func {half} {zero} {one} {one} () p₂
⊙₄-func {half} {forth} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {forth} {zero} {forth} p₁ p₂ = triv
⊙₄-func {half} {forth} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {forth} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {forth} {forth} {zero} () ()
⊙₄-func {half} {forth} {forth} {forth} p₁ p₂ = triv
⊙₄-func {half} {forth} {forth} {half} p₁ p₂ = triv
⊙₄-func {half} {forth} {forth} {one} p₁ p₂ = triv
⊙₄-func {half} {forth} {half} {zero} () ()
⊙₄-func {half} {forth} {half} {forth} p₁ p₂ = triv
⊙₄-func {half} {forth} {half} {half} p₁ p₂ = triv
⊙₄-func {half} {forth} {half} {one} p₁ p₂ = triv
⊙₄-func {half} {forth} {one} {zero} () ()
⊙₄-func {half} {forth} {one} {forth} () ()
⊙₄-func {half} {forth} {one} {half} () ()
⊙₄-func {half} {forth} {one} {one} () p₂
⊙₄-func {half} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {half} {zero} {forth} p₁ p₂ = triv
⊙₄-func {half} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {forth} {zero} p₁ ()
⊙₄-func {half} {half} {forth} {forth} p₁ p₂ = triv
⊙₄-func {half} {half} {forth} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {forth} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {half} {zero} p₁ ()
⊙₄-func {half} {half} {half} {forth} p₁ p₂ = triv
⊙₄-func {half} {half} {half} {half} p₁ p₂ = triv
⊙₄-func {half} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {half} {half} {one} {zero} p₁ ()
⊙₄-func {half} {half} {one} {forth} p₁ ()
⊙₄-func {half} {half} {one} {half} p₁ ()
⊙₄-func {half} {half} {one} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {forth} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {forth} {zero} p₁ ()
⊙₄-func {half} {one} {forth} {forth} p₁ p₂ = triv
⊙₄-func {half} {one} {forth} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {forth} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {half} {zero} p₁ ()
⊙₄-func {half} {one} {half} {forth} p₁ p₂ = triv
⊙₄-func {half} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {half} {one} {one} {zero} p₁ ()
⊙₄-func {half} {one} {one} {forth} p₁ ()
⊙₄-func {half} {one} {one} {half} p₁ p₂ = triv
⊙₄-func {half} {one} {one} {one} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {forth} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {zero} {forth} {zero} () ()
⊙₄-func {one} {zero} {forth} {forth} () p₂
⊙₄-func {one} {zero} {forth} {half} () p₂
⊙₄-func {one} {zero} {forth} {one} () p₂
⊙₄-func {one} {zero} {half} {zero} () ()
⊙₄-func {one} {zero} {half} {forth} () ()
⊙₄-func {one} {zero} {half} {half} () p₂
⊙₄-func {one} {zero} {half} {one} () p₂
⊙₄-func {one} {zero} {one} {zero} () ()
⊙₄-func {one} {zero} {one} {forth} () ()
⊙₄-func {one} {zero} {one} {half} () ()
⊙₄-func {one} {zero} {one} {one} () p₂
⊙₄-func {one} {forth} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {forth} {zero} {forth} p₁ p₂ = triv
⊙₄-func {one} {forth} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {forth} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {forth} {forth} {zero} () ()
⊙₄-func {one} {forth} {forth} {forth} p₁ p₂ = triv
⊙₄-func {one} {forth} {forth} {half} p₁ p₂ = triv
⊙₄-func {one} {forth} {forth} {one} p₁ p₂ = triv
⊙₄-func {one} {forth} {half} {zero} () ()
⊙₄-func {one} {forth} {half} {forth} () ()
⊙₄-func {one} {forth} {half} {half} () p₂
⊙₄-func {one} {forth} {half} {one} () p₂
⊙₄-func {one} {forth} {one} {zero} () ()
⊙₄-func {one} {forth} {one} {forth} () ()
⊙₄-func {one} {forth} {one} {half} () ()
⊙₄-func {one} {forth} {one} {one} () p₂
⊙₄-func {one} {half} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {half} {zero} {forth} p₁ p₂ = triv
⊙₄-func {one} {half} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {half} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {half} {forth} {zero} () ()
⊙₄-func {one} {half} {forth} {forth} p₁ p₂ = triv
⊙₄-func {one} {half} {forth} {half} () p₂
⊙₄-func {one} {half} {forth} {one} p₁ p₂ = triv
⊙₄-func {one} {half} {half} {zero} () ()
⊙₄-func {one} {half} {half} {forth} () ()
⊙₄-func {one} {half} {half} {half} () p₂
⊙₄-func {one} {half} {half} {one} p₁ p₂ = triv
⊙₄-func {one} {half} {one} {zero} () ()
⊙₄-func {one} {half} {one} {forth} () ()
⊙₄-func {one} {half} {one} {half} () ()
⊙₄-func {one} {half} {one} {one} () p₂
⊙₄-func {one} {one} {zero} {zero} p₁ p₂ = triv
⊙₄-func {one} {one} {zero} {forth} p₁ p₂ = triv
⊙₄-func {one} {one} {zero} {half} p₁ p₂ = triv
⊙₄-func {one} {one} {zero} {one} p₁ p₂ = triv
⊙₄-func {one} {one} {forth} {zero} p₁ ()
⊙₄-func {one} {one} {forth} {forth} p₁ p₂ = triv
⊙₄-func {one} {one} {forth} {half} p₁ p₂ = triv
⊙₄-func {one} {one} {forth} {one} p₁ p₂ = triv
⊙₄-func {one} {one} {half} {zero} p₁ ()
⊙₄-func {one} {one} {half} {forth} p₁ ()
⊙₄-func {one} {one} {half} {half} p₁ p₂ = triv
⊙₄-func {one} {one} {half} {one} p₁ p₂ = triv
⊙₄-func {one} {one} {one} {zero} p₁ ()
⊙₄-func {one} {one} {one} {forth} p₁ ()
⊙₄-func {one} {one} {one} {half} p₁ ()
⊙₄-func {one} {one} {one} {one} p₁ p₂ = triv

⊙₄-distl : {a b c : Four} → (a ⊙₄ (b ⊔₄ c)) ≡ ((a ⊙₄ b) ⊔₄ (a ⊙₄ c))
⊙₄-distl {zero} {zero} {zero} = refl
⊙₄-distl {zero} {zero} {forth} = refl
⊙₄-distl {zero} {zero} {half} = refl
⊙₄-distl {zero} {zero} {one} = refl
⊙₄-distl {zero} {forth} {zero} = refl
⊙₄-distl {zero} {forth} {forth} = refl
⊙₄-distl {zero} {forth} {half} = refl
⊙₄-distl {zero} {forth} {one} = refl
⊙₄-distl {zero} {half} {zero} = refl
⊙₄-distl {zero} {half} {forth} = refl
⊙₄-distl {zero} {half} {half} = refl
⊙₄-distl {zero} {half} {one} = refl
⊙₄-distl {zero} {one} {zero} = refl
⊙₄-distl {zero} {one} {forth} = refl
⊙₄-distl {zero} {one} {half} = refl
⊙₄-distl {zero} {one} {one} = refl
⊙₄-distl {forth} {zero} {zero} = refl
⊙₄-distl {forth} {zero} {forth} = refl
⊙₄-distl {forth} {zero} {half} = refl
⊙₄-distl {forth} {zero} {one} = refl
⊙₄-distl {forth} {forth} {zero} = refl
⊙₄-distl {forth} {forth} {forth} = refl
⊙₄-distl {forth} {forth} {half} = refl
⊙₄-distl {forth} {forth} {one} = refl
⊙₄-distl {forth} {half} {zero} = refl
⊙₄-distl {forth} {half} {forth} = refl
⊙₄-distl {forth} {half} {half} = refl
⊙₄-distl {forth} {half} {one} = refl
⊙₄-distl {forth} {one} {zero} = refl
⊙₄-distl {forth} {one} {forth} = refl
⊙₄-distl {forth} {one} {half} = refl
⊙₄-distl {forth} {one} {one} = refl
⊙₄-distl {half} {zero} {zero} = refl
⊙₄-distl {half} {zero} {forth} = refl
⊙₄-distl {half} {zero} {half} = refl
⊙₄-distl {half} {zero} {one} = refl
⊙₄-distl {half} {forth} {zero} = refl
⊙₄-distl {half} {forth} {forth} = refl
⊙₄-distl {half} {forth} {half} = refl
⊙₄-distl {half} {forth} {one} = refl
⊙₄-distl {half} {half} {zero} = refl
⊙₄-distl {half} {half} {forth} = refl
⊙₄-distl {half} {half} {half} = refl
⊙₄-distl {half} {half} {one} = refl
⊙₄-distl {half} {one} {zero} = refl
⊙₄-distl {half} {one} {forth} = refl
⊙₄-distl {half} {one} {half} = refl
⊙₄-distl {half} {one} {one} = refl
⊙₄-distl {one} {zero} {zero} = refl
⊙₄-distl {one} {zero} {forth} = refl
⊙₄-distl {one} {zero} {half} = refl
⊙₄-distl {one} {zero} {one} = refl
⊙₄-distl {one} {forth} {zero} = refl
⊙₄-distl {one} {forth} {forth} = refl
⊙₄-distl {one} {forth} {half} = refl
⊙₄-distl {one} {forth} {one} = refl
⊙₄-distl {one} {half} {zero} = refl
⊙₄-distl {one} {half} {forth} = refl
⊙₄-distl {one} {half} {half} = refl
⊙₄-distl {one} {half} {one} = refl
⊙₄-distl {one} {one} {zero} = refl
⊙₄-distl {one} {one} {forth} = refl
⊙₄-distl {one} {one} {half} = refl
⊙₄-distl {one} {one} {one} = refl

⊙₄-distr : {a b c : Four} → ((a ⊔₄ b) ⊙₄ c) ≡ ((a ⊙₄ c) ⊔₄ (b ⊙₄ c))
⊙₄-distr {zero} {zero} {zero} = refl
⊙₄-distr {zero} {zero} {forth} = refl
⊙₄-distr {zero} {zero} {half} = refl
⊙₄-distr {zero} {zero} {one} = refl
⊙₄-distr {zero} {forth} {zero} = refl
⊙₄-distr {zero} {forth} {forth} = refl
⊙₄-distr {zero} {forth} {half} = refl
⊙₄-distr {zero} {forth} {one} = refl
⊙₄-distr {zero} {half} {zero} = refl
⊙₄-distr {zero} {half} {forth} = refl
⊙₄-distr {zero} {half} {half} = refl
⊙₄-distr {zero} {half} {one} = refl
⊙₄-distr {zero} {one} {zero} = refl
⊙₄-distr {zero} {one} {forth} = refl
⊙₄-distr {zero} {one} {half} = refl
⊙₄-distr {zero} {one} {one} = refl
⊙₄-distr {forth} {zero} {zero} = refl
⊙₄-distr {forth} {zero} {forth} = refl
⊙₄-distr {forth} {zero} {half} = refl
⊙₄-distr {forth} {zero} {one} = refl
⊙₄-distr {forth} {forth} {zero} = refl
⊙₄-distr {forth} {forth} {forth} = refl
⊙₄-distr {forth} {forth} {half} = refl
⊙₄-distr {forth} {forth} {one} = refl
⊙₄-distr {forth} {half} {zero} = refl
⊙₄-distr {forth} {half} {forth} = refl
⊙₄-distr {forth} {half} {half} = refl
⊙₄-distr {forth} {half} {one} = refl
⊙₄-distr {forth} {one} {zero} = refl
⊙₄-distr {forth} {one} {forth} = refl
⊙₄-distr {forth} {one} {half} = refl
⊙₄-distr {forth} {one} {one} = refl
⊙₄-distr {half} {zero} {zero} = refl
⊙₄-distr {half} {zero} {forth} = refl
⊙₄-distr {half} {zero} {half} = refl
⊙₄-distr {half} {zero} {one} = refl
⊙₄-distr {half} {forth} {zero} = refl
⊙₄-distr {half} {forth} {forth} = refl
⊙₄-distr {half} {forth} {half} = refl
⊙₄-distr {half} {forth} {one} = refl
⊙₄-distr {half} {half} {zero} = refl
⊙₄-distr {half} {half} {forth} = refl
⊙₄-distr {half} {half} {half} = refl
⊙₄-distr {half} {half} {one} = refl
⊙₄-distr {half} {one} {zero} = refl
⊙₄-distr {half} {one} {forth} = refl
⊙₄-distr {half} {one} {half} = refl
⊙₄-distr {half} {one} {one} = refl
⊙₄-distr {one} {zero} {zero} = refl
⊙₄-distr {one} {zero} {forth} = refl
⊙₄-distr {one} {zero} {half} = refl
⊙₄-distr {one} {zero} {one} = refl
⊙₄-distr {one} {forth} {zero} = refl
⊙₄-distr {one} {forth} {forth} = refl
⊙₄-distr {one} {forth} {half} = refl
⊙₄-distr {one} {forth} {one} = refl
⊙₄-distr {one} {half} {zero} = refl
⊙₄-distr {one} {half} {forth} = refl
⊙₄-distr {one} {half} {half} = refl
⊙₄-distr {one} {half} {one} = refl
⊙₄-distr {one} {one} {zero} = refl
⊙₄-distr {one} {one} {forth} = refl
⊙₄-distr {one} {one} {half} = refl
⊙₄-distr {one} {one} {one} = refl

▷₄-sym : (∀{a b} → (a ▷₄ b) ≡ (b ▷₄ a)) → ⊥ {lzero}
▷₄-sym p with p {forth}{half}
... | () 

▷₄-contract : (∀{a} → (a ▷₄ a) ≡ a) → ⊥ {lzero}
▷₄-contract p with p {half}
... | () 

▷₄-zerol : ∀{x} → (zero ▷₄ x) ≤₄ zero
▷₄-zerol {zero} = triv
▷₄-zerol {forth} = triv
▷₄-zerol {half} = triv
▷₄-zerol {one} = triv

▷₄-zeror : ∀{x} → (x ▷₄ zero) ≤₄ zero
▷₄-zeror {zero} = triv
▷₄-zeror {forth} = triv
▷₄-zeror {half} = triv
▷₄-zeror {one} = triv

▷₄-assoc : {a b c : Four} →  a ▷₄ (b ▷₄ c) ≡ (a ▷₄ b) ▷₄ c
▷₄-assoc {zero} {zero} {zero} = refl
▷₄-assoc {zero} {zero} {forth} = refl
▷₄-assoc {zero} {zero} {half} = refl
▷₄-assoc {zero} {zero} {one} = refl
▷₄-assoc {zero} {forth} {zero} = refl
▷₄-assoc {zero} {forth} {forth} = refl
▷₄-assoc {zero} {forth} {half} = refl
▷₄-assoc {zero} {forth} {one} = refl
▷₄-assoc {zero} {half} {zero} = refl
▷₄-assoc {zero} {half} {forth} = refl
▷₄-assoc {zero} {half} {half} = refl
▷₄-assoc {zero} {half} {one} = refl
▷₄-assoc {zero} {one} {zero} = refl
▷₄-assoc {zero} {one} {forth} = refl
▷₄-assoc {zero} {one} {half} = refl
▷₄-assoc {zero} {one} {one} = refl
▷₄-assoc {forth} {zero} {zero} = refl
▷₄-assoc {forth} {zero} {forth} = refl
▷₄-assoc {forth} {zero} {half} = refl
▷₄-assoc {forth} {zero} {one} = refl
▷₄-assoc {forth} {forth} {zero} = refl
▷₄-assoc {forth} {forth} {forth} = refl
▷₄-assoc {forth} {forth} {half} = refl
▷₄-assoc {forth} {forth} {one} = refl
▷₄-assoc {forth} {half} {zero} = refl
▷₄-assoc {forth} {half} {forth} = refl
▷₄-assoc {forth} {half} {half} = refl
▷₄-assoc {forth} {half} {one} = refl
▷₄-assoc {forth} {one} {zero} = refl
▷₄-assoc {forth} {one} {forth} = refl
▷₄-assoc {forth} {one} {half} = refl
▷₄-assoc {forth} {one} {one} = refl
▷₄-assoc {half} {zero} {zero} = refl
▷₄-assoc {half} {zero} {forth} = refl
▷₄-assoc {half} {zero} {half} = refl
▷₄-assoc {half} {zero} {one} = refl
▷₄-assoc {half} {forth} {zero} = refl
▷₄-assoc {half} {forth} {forth} = refl
▷₄-assoc {half} {forth} {half} = refl
▷₄-assoc {half} {forth} {one} = refl
▷₄-assoc {half} {half} {zero} = refl
▷₄-assoc {half} {half} {forth} = refl
▷₄-assoc {half} {half} {half} = refl
▷₄-assoc {half} {half} {one} = refl
▷₄-assoc {half} {one} {zero} = refl
▷₄-assoc {half} {one} {forth} = refl
▷₄-assoc {half} {one} {half} = refl
▷₄-assoc {half} {one} {one} = refl
▷₄-assoc {one} {zero} {zero} = refl
▷₄-assoc {one} {zero} {forth} = refl
▷₄-assoc {one} {zero} {half} = refl
▷₄-assoc {one} {zero} {one} = refl
▷₄-assoc {one} {forth} {zero} = refl
▷₄-assoc {one} {forth} {forth} = refl
▷₄-assoc {one} {forth} {half} = refl
▷₄-assoc {one} {forth} {one} = refl
▷₄-assoc {one} {half} {zero} = refl
▷₄-assoc {one} {half} {forth} = refl
▷₄-assoc {one} {half} {half} = refl
▷₄-assoc {one} {half} {one} = refl
▷₄-assoc {one} {one} {zero} = refl
▷₄-assoc {one} {one} {forth} = refl
▷₄-assoc {one} {one} {half} = refl
▷₄-assoc {one} {one} {one} = refl

▷₄-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ▷₄ b) ≤₄ (c ▷₄ d)
▷₄-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
▷₄-func {zero} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
▷₄-func {zero} {zero} {forth} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {forth} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {forth} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {forth} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {zero} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
▷₄-func {zero} {forth} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {forth} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
▷₄-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
▷₄-func {zero} {forth} {forth} {half} p₁ p₂ = triv
▷₄-func {zero} {forth} {forth} {one} p₁ p₂ = triv
▷₄-func {zero} {forth} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {forth} {half} {forth} p₁ p₂ = triv
▷₄-func {zero} {forth} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {forth} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {forth} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {forth} {one} {forth} p₁ p₂ = triv
▷₄-func {zero} {forth} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {forth} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {forth} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {forth} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {forth} {forth} p₁ p₂ = triv
▷₄-func {zero} {half} {forth} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {forth} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {forth} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {forth} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {half} {one} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {forth} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {forth} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {forth} {forth} p₁ p₂ = triv
▷₄-func {zero} {one} {forth} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {forth} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {forth} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {half} {one} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {zero} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {forth} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {half} p₁ p₂ = triv
▷₄-func {zero} {one} {one} {one} p₁ p₂ = triv
▷₄-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
▷₄-func {forth} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {forth} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {forth} {zero} {forth} {zero} () ()
▷₄-func {forth} {zero} {forth} {forth} () p₂
▷₄-func {forth} {zero} {forth} {half} () p₂
▷₄-func {forth} {zero} {forth} {one} () p₂
▷₄-func {forth} {zero} {half} {zero} () ()
▷₄-func {forth} {zero} {half} {forth} () ()
▷₄-func {forth} {zero} {half} {half} () p₂
▷₄-func {forth} {zero} {half} {one} () p₂
▷₄-func {forth} {zero} {one} {zero} () ()
▷₄-func {forth} {zero} {one} {forth} () ()
▷₄-func {forth} {zero} {one} {half} () ()
▷₄-func {forth} {zero} {one} {one} () p₂
▷₄-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
▷₄-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
▷₄-func {forth} {forth} {zero} {half} p₁ p₂ = triv
▷₄-func {forth} {forth} {zero} {one} p₁ p₂ = triv
▷₄-func {forth} {forth} {forth} {zero} p₁ ()
▷₄-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
▷₄-func {forth} {forth} {forth} {half} p₁ p₂ = triv
▷₄-func {forth} {forth} {forth} {one} p₁ p₂ = triv
▷₄-func {forth} {forth} {half} {zero} p₁ ()
▷₄-func {forth} {forth} {half} {forth} p₁ ()
▷₄-func {forth} {forth} {half} {half} p₁ p₂ = triv
▷₄-func {forth} {forth} {half} {one} p₁ p₂ = triv
▷₄-func {forth} {forth} {one} {zero} p₁ ()
▷₄-func {forth} {forth} {one} {forth} p₁ ()
▷₄-func {forth} {forth} {one} {half} p₁ p₂ = triv
▷₄-func {forth} {forth} {one} {one} p₁ p₂ = triv
▷₄-func {forth} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {forth} {half} {zero} {forth} p₁ p₂ = triv
▷₄-func {forth} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {forth} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {forth} {half} {forth} {zero} p₁ ()
▷₄-func {forth} {half} {forth} {forth} p₁ p₂ = triv
▷₄-func {forth} {half} {forth} {half} p₁ p₂ = triv
▷₄-func {forth} {half} {forth} {one} p₁ p₂ = triv
▷₄-func {forth} {half} {half} {zero} p₁ ()
▷₄-func {forth} {half} {half} {forth} p₁ p₂ = triv
▷₄-func {forth} {half} {half} {half} p₁ p₂ = triv
▷₄-func {forth} {half} {half} {one} p₁ p₂ = triv
▷₄-func {forth} {half} {one} {zero} p₁ ()
▷₄-func {forth} {half} {one} {forth} p₁ p₂ = triv
▷₄-func {forth} {half} {one} {half} p₁ p₂ = triv
▷₄-func {forth} {half} {one} {one} p₁ p₂ = triv
▷₄-func {forth} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {forth} {one} {zero} {forth} p₁ p₂ = triv
▷₄-func {forth} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {forth} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {forth} {one} {forth} {zero} p₁ ()
▷₄-func {forth} {one} {forth} {forth} p₁ p₂ = triv
▷₄-func {forth} {one} {forth} {half} p₁ p₂ = triv
▷₄-func {forth} {one} {forth} {one} p₁ p₂ = triv
▷₄-func {forth} {one} {half} {zero} p₁ ()
▷₄-func {forth} {one} {half} {forth} p₁ p₂ = triv
▷₄-func {forth} {one} {half} {half} p₁ p₂ = triv
▷₄-func {forth} {one} {half} {one} p₁ p₂ = triv
▷₄-func {forth} {one} {one} {zero} p₁ ()
▷₄-func {forth} {one} {one} {forth} p₁ p₂ = triv
▷₄-func {forth} {one} {one} {half} p₁ p₂ = triv
▷₄-func {forth} {one} {one} {one} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {forth} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {zero} {forth} {zero} () ()
▷₄-func {half} {zero} {forth} {forth} () p₂
▷₄-func {half} {zero} {forth} {half} () p₂
▷₄-func {half} {zero} {forth} {one} () p₂
▷₄-func {half} {zero} {half} {zero} () ()
▷₄-func {half} {zero} {half} {forth} () ()
▷₄-func {half} {zero} {half} {half} () p₂
▷₄-func {half} {zero} {half} {one} () p₂
▷₄-func {half} {zero} {one} {zero} () ()
▷₄-func {half} {zero} {one} {forth} () ()
▷₄-func {half} {zero} {one} {half} () ()
▷₄-func {half} {zero} {one} {one} () p₂
▷₄-func {half} {forth} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {forth} {zero} {forth} p₁ p₂ = triv
▷₄-func {half} {forth} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {forth} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {forth} {forth} {zero} () ()
▷₄-func {half} {forth} {forth} {forth} () p₂
▷₄-func {half} {forth} {forth} {half} () p₂
▷₄-func {half} {forth} {forth} {one} () p₂
▷₄-func {half} {forth} {half} {zero} () ()
▷₄-func {half} {forth} {half} {forth} () ()
▷₄-func {half} {forth} {half} {half} () p₂
▷₄-func {half} {forth} {half} {one} () p₂
▷₄-func {half} {forth} {one} {zero} () ()
▷₄-func {half} {forth} {one} {forth} () ()
▷₄-func {half} {forth} {one} {half} () ()
▷₄-func {half} {forth} {one} {one} () p₂
▷₄-func {half} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {half} {zero} {forth} p₁ p₂ = triv
▷₄-func {half} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {half} {forth} {zero} p₁ ()
▷₄-func {half} {half} {forth} {forth} p₁ p₂ = triv
▷₄-func {half} {half} {forth} {half} p₁ p₂ = triv
▷₄-func {half} {half} {forth} {one} p₁ p₂ = triv
▷₄-func {half} {half} {half} {zero} p₁ ()
▷₄-func {half} {half} {half} {forth} p₁ p₂ = triv
▷₄-func {half} {half} {half} {half} p₁ p₂ = triv
▷₄-func {half} {half} {half} {one} p₁ p₂ = triv
▷₄-func {half} {half} {one} {zero} p₁ ()
▷₄-func {half} {half} {one} {forth} p₁ p₂ = triv
▷₄-func {half} {half} {one} {half} p₁ p₂ = triv
▷₄-func {half} {half} {one} {one} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {forth} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {half} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {half} {one} {forth} {zero} p₁ ()
▷₄-func {half} {one} {forth} {forth} p₁ p₂ = triv
▷₄-func {half} {one} {forth} {half} p₁ p₂ = triv
▷₄-func {half} {one} {forth} {one} p₁ p₂ = triv
▷₄-func {half} {one} {half} {zero} p₁ ()
▷₄-func {half} {one} {half} {forth} p₁ p₂ = triv
▷₄-func {half} {one} {half} {half} p₁ p₂ = triv
▷₄-func {half} {one} {half} {one} p₁ p₂ = triv
▷₄-func {half} {one} {one} {zero} p₁ ()
▷₄-func {half} {one} {one} {forth} p₁ p₂ = triv
▷₄-func {half} {one} {one} {half} p₁ p₂ = triv
▷₄-func {half} {one} {one} {one} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {forth} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {zero} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {zero} {forth} {zero} p₁ ()
▷₄-func {one} {zero} {forth} {forth} () p₂
▷₄-func {one} {zero} {forth} {half} () p₂
▷₄-func {one} {zero} {forth} {one} () p₂
▷₄-func {one} {zero} {half} {zero} () ()
▷₄-func {one} {zero} {half} {forth} () ()
▷₄-func {one} {zero} {half} {half} () p₂
▷₄-func {one} {zero} {half} {one} () p₂
▷₄-func {one} {zero} {one} {zero} () ()
▷₄-func {one} {zero} {one} {forth} () ()
▷₄-func {one} {zero} {one} {half} () ()
▷₄-func {one} {zero} {one} {one} () p₂
▷₄-func {one} {forth} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {forth} {zero} {forth} p₁ p₂ = triv
▷₄-func {one} {forth} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {forth} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {forth} {forth} {zero} () ()
▷₄-func {one} {forth} {forth} {forth} () p₂
▷₄-func {one} {forth} {forth} {half} () p₂
▷₄-func {one} {forth} {forth} {one} () p₂
▷₄-func {one} {forth} {half} {zero} () ()
▷₄-func {one} {forth} {half} {forth} () ()
▷₄-func {one} {forth} {half} {half} () p₂
▷₄-func {one} {forth} {half} {one} () p₂
▷₄-func {one} {forth} {one} {zero} () ()
▷₄-func {one} {forth} {one} {forth} () ()
▷₄-func {one} {forth} {one} {half} () ()
▷₄-func {one} {forth} {one} {one} () p₂
▷₄-func {one} {half} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {half} {zero} {forth} p₁ p₂ = triv
▷₄-func {one} {half} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {half} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {half} {forth} {zero} () ()
▷₄-func {one} {half} {forth} {forth} () p₂
▷₄-func {one} {half} {forth} {half} () p₂
▷₄-func {one} {half} {forth} {one} () p₂
▷₄-func {one} {half} {half} {zero} () ()
▷₄-func {one} {half} {half} {forth} p₁ p₂ = triv
▷₄-func {one} {half} {half} {half} p₁ p₂ = triv
▷₄-func {one} {half} {half} {one} p₁ p₂ = triv
▷₄-func {one} {half} {one} {zero} () ()
▷₄-func {one} {half} {one} {forth} p₁ p₂ = triv
▷₄-func {one} {half} {one} {half} p₁ p₂ = triv
▷₄-func {one} {half} {one} {one} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {zero} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {forth} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {half} p₁ p₂ = triv
▷₄-func {one} {one} {zero} {one} p₁ p₂ = triv
▷₄-func {one} {one} {forth} {zero} p₁ ()
▷₄-func {one} {one} {forth} {forth} p₁ p₂ = triv
▷₄-func {one} {one} {forth} {half} p₁ p₂ = triv
▷₄-func {one} {one} {forth} {one} p₁ p₂ = triv
▷₄-func {one} {one} {half} {zero} p₁ ()
▷₄-func {one} {one} {half} {forth} p₁ p₂ = triv
▷₄-func {one} {one} {half} {half} p₁ p₂ = triv
▷₄-func {one} {one} {half} {one} p₁ p₂ = triv
▷₄-func {one} {one} {one} {zero} p₁ ()
▷₄-func {one} {one} {one} {forth} p₁ p₂ = triv
▷₄-func {one} {one} {one} {half} p₁ p₂ = triv
▷₄-func {one} {one} {one} {one} p₁ p₂ = triv

▷₄-distl : {a b c : Four} → (a ▷₄ (b ⊔₄ c)) ≡ ((a ▷₄ b) ⊔₄ (a ▷₄ c))
▷₄-distl {zero} {zero} {zero} = refl
▷₄-distl {zero} {zero} {forth} = refl
▷₄-distl {zero} {zero} {half} = refl
▷₄-distl {zero} {zero} {one} = refl
▷₄-distl {zero} {forth} {zero} = refl
▷₄-distl {zero} {forth} {forth} = refl
▷₄-distl {zero} {forth} {half} = refl
▷₄-distl {zero} {forth} {one} = refl
▷₄-distl {zero} {half} {zero} = refl
▷₄-distl {zero} {half} {forth} = refl
▷₄-distl {zero} {half} {half} = refl
▷₄-distl {zero} {half} {one} = refl
▷₄-distl {zero} {one} {zero} = refl
▷₄-distl {zero} {one} {forth} = refl
▷₄-distl {zero} {one} {half} = refl
▷₄-distl {zero} {one} {one} = refl
▷₄-distl {forth} {zero} {zero} = refl
▷₄-distl {forth} {zero} {forth} = refl
▷₄-distl {forth} {zero} {half} = refl
▷₄-distl {forth} {zero} {one} = refl
▷₄-distl {forth} {forth} {zero} = refl
▷₄-distl {forth} {forth} {forth} = refl
▷₄-distl {forth} {forth} {half} = refl
▷₄-distl {forth} {forth} {one} = refl
▷₄-distl {forth} {half} {zero} = refl
▷₄-distl {forth} {half} {forth} = refl
▷₄-distl {forth} {half} {half} = refl
▷₄-distl {forth} {half} {one} = refl
▷₄-distl {forth} {one} {zero} = refl
▷₄-distl {forth} {one} {forth} = refl
▷₄-distl {forth} {one} {half} = refl
▷₄-distl {forth} {one} {one} = refl
▷₄-distl {half} {zero} {zero} = refl
▷₄-distl {half} {zero} {forth} = refl
▷₄-distl {half} {zero} {half} = refl
▷₄-distl {half} {zero} {one} = refl
▷₄-distl {half} {forth} {zero} = refl
▷₄-distl {half} {forth} {forth} = refl
▷₄-distl {half} {forth} {half} = refl
▷₄-distl {half} {forth} {one} = refl
▷₄-distl {half} {half} {zero} = refl
▷₄-distl {half} {half} {forth} = refl
▷₄-distl {half} {half} {half} = refl
▷₄-distl {half} {half} {one} = refl
▷₄-distl {half} {one} {zero} = refl
▷₄-distl {half} {one} {forth} = refl
▷₄-distl {half} {one} {half} = refl
▷₄-distl {half} {one} {one} = refl
▷₄-distl {one} {zero} {zero} = refl
▷₄-distl {one} {zero} {forth} = refl
▷₄-distl {one} {zero} {half} = refl
▷₄-distl {one} {zero} {one} = refl
▷₄-distl {one} {forth} {zero} = refl
▷₄-distl {one} {forth} {forth} = refl
▷₄-distl {one} {forth} {half} = refl
▷₄-distl {one} {forth} {one} = refl
▷₄-distl {one} {half} {zero} = refl
▷₄-distl {one} {half} {forth} = refl
▷₄-distl {one} {half} {half} = refl
▷₄-distl {one} {half} {one} = refl
▷₄-distl {one} {one} {zero} = refl
▷₄-distl {one} {one} {forth} = refl
▷₄-distl {one} {one} {half} = refl
▷₄-distl {one} {one} {one} = refl

▷₄-distr : {a b c : Four} → ((a ⊔₄ b) ▷₄ c) ≡ ((a ▷₄ c) ⊔₄ (b ▷₄ c))
▷₄-distr {zero} {zero} {zero} = refl
▷₄-distr {zero} {zero} {forth} = refl
▷₄-distr {zero} {zero} {half} = refl
▷₄-distr {zero} {zero} {one} = refl
▷₄-distr {zero} {forth} {zero} = refl
▷₄-distr {zero} {forth} {forth} = refl
▷₄-distr {zero} {forth} {half} = refl
▷₄-distr {zero} {forth} {one} = refl
▷₄-distr {zero} {half} {zero} = refl
▷₄-distr {zero} {half} {forth} = refl
▷₄-distr {zero} {half} {half} = refl
▷₄-distr {zero} {half} {one} = refl
▷₄-distr {zero} {one} {zero} = refl
▷₄-distr {zero} {one} {forth} = refl
▷₄-distr {zero} {one} {half} = refl
▷₄-distr {zero} {one} {one} = refl
▷₄-distr {forth} {zero} {zero} = refl
▷₄-distr {forth} {zero} {forth} = refl
▷₄-distr {forth} {zero} {half} = refl
▷₄-distr {forth} {zero} {one} = refl
▷₄-distr {forth} {forth} {zero} = refl
▷₄-distr {forth} {forth} {forth} = refl
▷₄-distr {forth} {forth} {half} = refl
▷₄-distr {forth} {forth} {one} = refl
▷₄-distr {forth} {half} {zero} = refl
▷₄-distr {forth} {half} {forth} = refl
▷₄-distr {forth} {half} {half} = refl
▷₄-distr {forth} {half} {one} = refl
▷₄-distr {forth} {one} {zero} = refl
▷₄-distr {forth} {one} {forth} = refl
▷₄-distr {forth} {one} {half} = refl
▷₄-distr {forth} {one} {one} = refl
▷₄-distr {half} {zero} {zero} = refl
▷₄-distr {half} {zero} {forth} = refl
▷₄-distr {half} {zero} {half} = refl
▷₄-distr {half} {zero} {one} = refl
▷₄-distr {half} {forth} {zero} = refl
▷₄-distr {half} {forth} {forth} = refl
▷₄-distr {half} {forth} {half} = refl
▷₄-distr {half} {forth} {one} = refl
▷₄-distr {half} {half} {zero} = refl
▷₄-distr {half} {half} {forth} = refl
▷₄-distr {half} {half} {half} = refl
▷₄-distr {half} {half} {one} = refl
▷₄-distr {half} {one} {zero} = refl
▷₄-distr {half} {one} {forth} = refl
▷₄-distr {half} {one} {half} = refl
▷₄-distr {half} {one} {one} = refl
▷₄-distr {one} {zero} {zero} = refl
▷₄-distr {one} {zero} {forth} = refl
▷₄-distr {one} {zero} {half} = refl
▷₄-distr {one} {zero} {one} = refl
▷₄-distr {one} {forth} {zero} = refl
▷₄-distr {one} {forth} {forth} = refl
▷₄-distr {one} {forth} {half} = refl
▷₄-distr {one} {forth} {one} = refl
▷₄-distr {one} {half} {zero} = refl
▷₄-distr {one} {half} {forth} = refl
▷₄-distr {one} {half} {half} = refl
▷₄-distr {one} {half} {one} = refl
▷₄-distr {one} {one} {zero} = refl
▷₄-distr {one} {one} {forth} = refl
▷₄-distr {one} {one} {half} = refl
▷₄-distr {one} {one} {one} = refl

⊔₄-sym : ∀{a b} → (a ⊔₄ b) ≡ (b ⊔₄ a)
⊔₄-sym {zero} {zero} = refl
⊔₄-sym {zero} {forth} = refl
⊔₄-sym {zero} {half} = refl
⊔₄-sym {zero} {one} = refl
⊔₄-sym {forth} {zero} = refl
⊔₄-sym {forth} {forth} = refl
⊔₄-sym {forth} {half} = refl
⊔₄-sym {forth} {one} = refl
⊔₄-sym {half} {zero} = refl
⊔₄-sym {half} {forth} = refl
⊔₄-sym {half} {half} = refl
⊔₄-sym {half} {one} = refl
⊔₄-sym {one} {zero} = refl
⊔₄-sym {one} {forth} = refl
⊔₄-sym {one} {half} = refl
⊔₄-sym {one} {one} = refl

⊔₄-assoc : ∀{a b c} → (a ⊔₄ b) ⊔₄ c ≡ a ⊔₄ (b ⊔₄ c)
⊔₄-assoc {zero} {zero} {zero} = refl
⊔₄-assoc {zero} {zero} {forth} = refl
⊔₄-assoc {zero} {zero} {half} = refl
⊔₄-assoc {zero} {zero} {one} = refl
⊔₄-assoc {zero} {forth} {zero} = refl
⊔₄-assoc {zero} {forth} {forth} = refl
⊔₄-assoc {zero} {forth} {half} = refl
⊔₄-assoc {zero} {forth} {one} = refl
⊔₄-assoc {zero} {half} {zero} = refl
⊔₄-assoc {zero} {half} {forth} = refl
⊔₄-assoc {zero} {half} {half} = refl
⊔₄-assoc {zero} {half} {one} = refl
⊔₄-assoc {zero} {one} {zero} = refl
⊔₄-assoc {zero} {one} {forth} = refl
⊔₄-assoc {zero} {one} {half} = refl
⊔₄-assoc {zero} {one} {one} = refl
⊔₄-assoc {forth} {zero} {zero} = refl
⊔₄-assoc {forth} {zero} {forth} = refl
⊔₄-assoc {forth} {zero} {half} = refl
⊔₄-assoc {forth} {zero} {one} = refl
⊔₄-assoc {forth} {forth} {zero} = refl
⊔₄-assoc {forth} {forth} {forth} = refl
⊔₄-assoc {forth} {forth} {half} = refl
⊔₄-assoc {forth} {forth} {one} = refl
⊔₄-assoc {forth} {half} {zero} = refl
⊔₄-assoc {forth} {half} {forth} = refl
⊔₄-assoc {forth} {half} {half} = refl
⊔₄-assoc {forth} {half} {one} = refl
⊔₄-assoc {forth} {one} {zero} = refl
⊔₄-assoc {forth} {one} {forth} = refl
⊔₄-assoc {forth} {one} {half} = refl
⊔₄-assoc {forth} {one} {one} = refl
⊔₄-assoc {half} {zero} {zero} = refl
⊔₄-assoc {half} {zero} {forth} = refl
⊔₄-assoc {half} {zero} {half} = refl
⊔₄-assoc {half} {zero} {one} = refl
⊔₄-assoc {half} {forth} {zero} = refl
⊔₄-assoc {half} {forth} {forth} = refl
⊔₄-assoc {half} {forth} {half} = refl
⊔₄-assoc {half} {forth} {one} = refl
⊔₄-assoc {half} {half} {zero} = refl
⊔₄-assoc {half} {half} {forth} = refl
⊔₄-assoc {half} {half} {half} = refl
⊔₄-assoc {half} {half} {one} = refl
⊔₄-assoc {half} {one} {zero} = refl
⊔₄-assoc {half} {one} {forth} = refl
⊔₄-assoc {half} {one} {half} = refl
⊔₄-assoc {half} {one} {one} = refl
⊔₄-assoc {one} {zero} {zero} = refl
⊔₄-assoc {one} {zero} {forth} = refl
⊔₄-assoc {one} {zero} {half} = refl
⊔₄-assoc {one} {zero} {one} = refl
⊔₄-assoc {one} {forth} {zero} = refl
⊔₄-assoc {one} {forth} {forth} = refl
⊔₄-assoc {one} {forth} {half} = refl
⊔₄-assoc {one} {forth} {one} = refl
⊔₄-assoc {one} {half} {zero} = refl
⊔₄-assoc {one} {half} {forth} = refl
⊔₄-assoc {one} {half} {half} = refl
⊔₄-assoc {one} {half} {one} = refl
⊔₄-assoc {one} {one} {zero} = refl
⊔₄-assoc {one} {one} {forth} = refl
⊔₄-assoc {one} {one} {half} = refl
⊔₄-assoc {one} {one} {one} = refl

⊔₄-func : ∀{a c b d} → a ≤₄ c → b ≤₄ d → (a ⊔₄ b) ≤₄ (c ⊔₄ d)
⊔₄-func {zero} {zero} {zero} {zero} triv triv = triv
⊔₄-func {zero} {zero} {zero} {forth} triv triv = triv
⊔₄-func {zero} {zero} {zero} {half} triv triv = triv
⊔₄-func {zero} {zero} {zero} {one} triv triv = triv
⊔₄-func {zero} {zero} {forth} {zero} triv ()
⊔₄-func {zero} {zero} {forth} {forth} triv triv = triv
⊔₄-func {zero} {zero} {forth} {half} triv triv = triv
⊔₄-func {zero} {zero} {forth} {one} triv triv = triv
⊔₄-func {zero} {zero} {half} {zero} triv ()
⊔₄-func {zero} {zero} {half} {forth} triv ()
⊔₄-func {zero} {zero} {half} {half} triv triv = triv
⊔₄-func {zero} {zero} {half} {one} triv triv = triv
⊔₄-func {zero} {zero} {one} {zero} triv ()
⊔₄-func {zero} {zero} {one} {forth} triv ()
⊔₄-func {zero} {zero} {one} {half} triv ()
⊔₄-func {zero} {zero} {one} {one} triv triv = triv
⊔₄-func {zero} {forth} {zero} {zero} triv triv = triv
⊔₄-func {zero} {forth} {zero} {forth} triv triv = triv
⊔₄-func {zero} {forth} {zero} {half} triv triv = triv
⊔₄-func {zero} {forth} {zero} {one} triv triv = triv
⊔₄-func {zero} {forth} {forth} {zero} triv ()
⊔₄-func {zero} {forth} {forth} {forth} triv triv = triv
⊔₄-func {zero} {forth} {forth} {half} triv triv = triv
⊔₄-func {zero} {forth} {forth} {one} triv triv = triv
⊔₄-func {zero} {forth} {half} {zero} triv ()
⊔₄-func {zero} {forth} {half} {forth} triv ()
⊔₄-func {zero} {forth} {half} {half} triv triv = triv
⊔₄-func {zero} {forth} {half} {one} triv triv = triv
⊔₄-func {zero} {forth} {one} {zero} triv ()
⊔₄-func {zero} {forth} {one} {forth} triv ()
⊔₄-func {zero} {forth} {one} {half} triv ()
⊔₄-func {zero} {forth} {one} {one} triv triv = triv
⊔₄-func {zero} {half} {zero} {zero} triv triv = triv
⊔₄-func {zero} {half} {zero} {forth} triv triv = triv
⊔₄-func {zero} {half} {zero} {half} triv triv = triv
⊔₄-func {zero} {half} {zero} {one} triv triv = triv
⊔₄-func {zero} {half} {forth} {zero} triv ()
⊔₄-func {zero} {half} {forth} {forth} triv triv = triv
⊔₄-func {zero} {half} {forth} {half} triv triv = triv
⊔₄-func {zero} {half} {forth} {one} triv triv = triv
⊔₄-func {zero} {half} {half} {zero} triv ()
⊔₄-func {zero} {half} {half} {forth} triv ()
⊔₄-func {zero} {half} {half} {half} triv triv = triv
⊔₄-func {zero} {half} {half} {one} triv triv = triv
⊔₄-func {zero} {half} {one} {zero} triv ()
⊔₄-func {zero} {half} {one} {forth} triv ()
⊔₄-func {zero} {half} {one} {half} triv ()
⊔₄-func {zero} {half} {one} {one} triv triv = triv
⊔₄-func {zero} {one} {zero} {zero} triv triv = triv
⊔₄-func {zero} {one} {zero} {forth} triv triv = triv
⊔₄-func {zero} {one} {zero} {half} triv triv = triv
⊔₄-func {zero} {one} {zero} {one} triv triv = triv
⊔₄-func {zero} {one} {forth} {zero} triv ()
⊔₄-func {zero} {one} {forth} {forth} triv triv = triv
⊔₄-func {zero} {one} {forth} {half} triv triv = triv
⊔₄-func {zero} {one} {forth} {one} triv triv = triv
⊔₄-func {zero} {one} {half} {zero} triv ()
⊔₄-func {zero} {one} {half} {forth} triv ()
⊔₄-func {zero} {one} {half} {half} triv triv = triv
⊔₄-func {zero} {one} {half} {one} triv triv = triv
⊔₄-func {zero} {one} {one} {zero} triv ()
⊔₄-func {zero} {one} {one} {forth} triv ()
⊔₄-func {zero} {one} {one} {half} triv ()
⊔₄-func {zero} {one} {one} {one} triv triv = triv
⊔₄-func {forth} {zero} {zero} {zero} () p₂
⊔₄-func {forth} {zero} {zero} {forth} () p₂
⊔₄-func {forth} {zero} {zero} {half} () p₂
⊔₄-func {forth} {zero} {zero} {one} () p₂
⊔₄-func {forth} {zero} {forth} {zero} () p₂
⊔₄-func {forth} {zero} {forth} {forth} () p₂
⊔₄-func {forth} {zero} {forth} {half} () p₂
⊔₄-func {forth} {zero} {forth} {one} () p₂
⊔₄-func {forth} {zero} {half} {zero} () p₂
⊔₄-func {forth} {zero} {half} {forth} () p₂
⊔₄-func {forth} {zero} {half} {half} () p₂
⊔₄-func {forth} {zero} {half} {one} () p₂
⊔₄-func {forth} {zero} {one} {zero} () p₂
⊔₄-func {forth} {zero} {one} {forth} () p₂
⊔₄-func {forth} {zero} {one} {half} () p₂
⊔₄-func {forth} {zero} {one} {one} () p₂
⊔₄-func {forth} {forth} {zero} {zero} triv triv = triv
⊔₄-func {forth} {forth} {zero} {forth} triv triv = triv
⊔₄-func {forth} {forth} {zero} {half} triv triv = triv
⊔₄-func {forth} {forth} {zero} {one} triv triv = triv
⊔₄-func {forth} {forth} {forth} {zero} triv ()
⊔₄-func {forth} {forth} {forth} {forth} triv triv = triv
⊔₄-func {forth} {forth} {forth} {half} triv triv = triv
⊔₄-func {forth} {forth} {forth} {one} triv triv = triv
⊔₄-func {forth} {forth} {half} {zero} triv ()
⊔₄-func {forth} {forth} {half} {forth} triv ()
⊔₄-func {forth} {forth} {half} {half} triv triv = triv
⊔₄-func {forth} {forth} {half} {one} triv triv = triv
⊔₄-func {forth} {forth} {one} {zero} triv ()
⊔₄-func {forth} {forth} {one} {forth} triv ()
⊔₄-func {forth} {forth} {one} {half} triv ()
⊔₄-func {forth} {forth} {one} {one} triv triv = triv
⊔₄-func {forth} {half} {zero} {zero} triv triv = triv
⊔₄-func {forth} {half} {zero} {forth} triv triv = triv
⊔₄-func {forth} {half} {zero} {half} triv triv = triv
⊔₄-func {forth} {half} {zero} {one} triv triv = triv
⊔₄-func {forth} {half} {forth} {zero} triv ()
⊔₄-func {forth} {half} {forth} {forth} triv triv = triv
⊔₄-func {forth} {half} {forth} {half} triv triv = triv
⊔₄-func {forth} {half} {forth} {one} triv triv = triv
⊔₄-func {forth} {half} {half} {zero} triv ()
⊔₄-func {forth} {half} {half} {forth} triv ()
⊔₄-func {forth} {half} {half} {half} triv triv = triv
⊔₄-func {forth} {half} {half} {one} triv triv = triv
⊔₄-func {forth} {half} {one} {zero} triv ()
⊔₄-func {forth} {half} {one} {forth} triv ()
⊔₄-func {forth} {half} {one} {half} triv ()
⊔₄-func {forth} {half} {one} {one} triv triv = triv
⊔₄-func {forth} {one} {zero} {zero} triv triv = triv
⊔₄-func {forth} {one} {zero} {forth} triv triv = triv
⊔₄-func {forth} {one} {zero} {half} triv triv = triv
⊔₄-func {forth} {one} {zero} {one} triv triv = triv
⊔₄-func {forth} {one} {forth} {zero} triv ()
⊔₄-func {forth} {one} {forth} {forth} triv triv = triv
⊔₄-func {forth} {one} {forth} {half} triv triv = triv
⊔₄-func {forth} {one} {forth} {one} triv triv = triv
⊔₄-func {forth} {one} {half} {zero} triv ()
⊔₄-func {forth} {one} {half} {forth} triv ()
⊔₄-func {forth} {one} {half} {half} triv triv = triv
⊔₄-func {forth} {one} {half} {one} triv triv = triv
⊔₄-func {forth} {one} {one} {zero} triv ()
⊔₄-func {forth} {one} {one} {forth} triv ()
⊔₄-func {forth} {one} {one} {half} triv ()
⊔₄-func {forth} {one} {one} {one} triv triv = triv
⊔₄-func {half} {zero} {zero} {zero} () p₂
⊔₄-func {half} {zero} {zero} {forth} () p₂
⊔₄-func {half} {zero} {zero} {half} () p₂
⊔₄-func {half} {zero} {zero} {one} () p₂
⊔₄-func {half} {zero} {forth} {zero} () p₂
⊔₄-func {half} {zero} {forth} {forth} () p₂
⊔₄-func {half} {zero} {forth} {half} () p₂
⊔₄-func {half} {zero} {forth} {one} () p₂
⊔₄-func {half} {zero} {half} {zero} () p₂
⊔₄-func {half} {zero} {half} {forth} () p₂
⊔₄-func {half} {zero} {half} {half} () p₂
⊔₄-func {half} {zero} {half} {one} () p₂
⊔₄-func {half} {zero} {one} {zero} () p₂
⊔₄-func {half} {zero} {one} {forth} () p₂
⊔₄-func {half} {zero} {one} {half} () p₂
⊔₄-func {half} {zero} {one} {one} () p₂
⊔₄-func {half} {forth} {zero} {zero} () p₂
⊔₄-func {half} {forth} {zero} {forth} () p₂
⊔₄-func {half} {forth} {zero} {half} () p₂
⊔₄-func {half} {forth} {zero} {one} () p₂
⊔₄-func {half} {forth} {forth} {zero} () p₂
⊔₄-func {half} {forth} {forth} {forth} () p₂
⊔₄-func {half} {forth} {forth} {half} () p₂
⊔₄-func {half} {forth} {forth} {one} () p₂
⊔₄-func {half} {forth} {half} {zero} () p₂
⊔₄-func {half} {forth} {half} {forth} () p₂
⊔₄-func {half} {forth} {half} {half} () p₂
⊔₄-func {half} {forth} {half} {one} () p₂
⊔₄-func {half} {forth} {one} {zero} () p₂
⊔₄-func {half} {forth} {one} {forth} () p₂
⊔₄-func {half} {forth} {one} {half} () p₂
⊔₄-func {half} {forth} {one} {one} () p₂
⊔₄-func {half} {half} {zero} {zero} triv triv = triv
⊔₄-func {half} {half} {zero} {forth} triv triv = triv
⊔₄-func {half} {half} {zero} {half} triv triv = triv
⊔₄-func {half} {half} {zero} {one} triv triv = triv
⊔₄-func {half} {half} {forth} {zero} triv ()
⊔₄-func {half} {half} {forth} {forth} triv triv = triv
⊔₄-func {half} {half} {forth} {half} triv triv = triv
⊔₄-func {half} {half} {forth} {one} triv triv = triv
⊔₄-func {half} {half} {half} {zero} triv ()
⊔₄-func {half} {half} {half} {forth} triv ()
⊔₄-func {half} {half} {half} {half} triv triv = triv
⊔₄-func {half} {half} {half} {one} triv triv = triv
⊔₄-func {half} {half} {one} {zero} triv ()
⊔₄-func {half} {half} {one} {forth} triv ()
⊔₄-func {half} {half} {one} {half} triv ()
⊔₄-func {half} {half} {one} {one} triv triv = triv
⊔₄-func {half} {one} {zero} {zero} triv triv = triv
⊔₄-func {half} {one} {zero} {forth} triv triv = triv
⊔₄-func {half} {one} {zero} {half} triv triv = triv
⊔₄-func {half} {one} {zero} {one} triv triv = triv
⊔₄-func {half} {one} {forth} {zero} triv ()
⊔₄-func {half} {one} {forth} {forth} triv triv = triv
⊔₄-func {half} {one} {forth} {half} triv triv = triv
⊔₄-func {half} {one} {forth} {one} triv triv = triv
⊔₄-func {half} {one} {half} {zero} triv ()
⊔₄-func {half} {one} {half} {forth} triv ()
⊔₄-func {half} {one} {half} {half} triv triv = triv
⊔₄-func {half} {one} {half} {one} triv triv = triv
⊔₄-func {half} {one} {one} {zero} triv ()
⊔₄-func {half} {one} {one} {forth} triv ()
⊔₄-func {half} {one} {one} {half} triv ()
⊔₄-func {half} {one} {one} {one} triv triv = triv
⊔₄-func {one} {zero} {zero} {zero} () p₂
⊔₄-func {one} {zero} {zero} {forth} () p₂
⊔₄-func {one} {zero} {zero} {half} () p₂
⊔₄-func {one} {zero} {zero} {one} () p₂
⊔₄-func {one} {zero} {forth} {zero} () p₂
⊔₄-func {one} {zero} {forth} {forth} () p₂
⊔₄-func {one} {zero} {forth} {half} () p₂
⊔₄-func {one} {zero} {forth} {one} () p₂
⊔₄-func {one} {zero} {half} {zero} () p₂
⊔₄-func {one} {zero} {half} {forth} () p₂
⊔₄-func {one} {zero} {half} {half} () p₂
⊔₄-func {one} {zero} {half} {one} () p₂
⊔₄-func {one} {zero} {one} {zero} () p₂
⊔₄-func {one} {zero} {one} {forth} () p₂
⊔₄-func {one} {zero} {one} {half} () p₂
⊔₄-func {one} {zero} {one} {one} () p₂
⊔₄-func {one} {forth} {zero} {zero} () p₂
⊔₄-func {one} {forth} {zero} {forth} () p₂
⊔₄-func {one} {forth} {zero} {half} () p₂
⊔₄-func {one} {forth} {zero} {one} () p₂
⊔₄-func {one} {forth} {forth} {zero} () p₂
⊔₄-func {one} {forth} {forth} {forth} () p₂
⊔₄-func {one} {forth} {forth} {half} () p₂
⊔₄-func {one} {forth} {forth} {one} () p₂
⊔₄-func {one} {forth} {half} {zero} () p₂
⊔₄-func {one} {forth} {half} {forth} () p₂
⊔₄-func {one} {forth} {half} {half} () p₂
⊔₄-func {one} {forth} {half} {one} () p₂
⊔₄-func {one} {forth} {one} {zero} () p₂
⊔₄-func {one} {forth} {one} {forth} () p₂
⊔₄-func {one} {forth} {one} {half} () p₂
⊔₄-func {one} {forth} {one} {one} () p₂
⊔₄-func {one} {half} {zero} {zero} () p₂
⊔₄-func {one} {half} {zero} {forth} () p₂
⊔₄-func {one} {half} {zero} {half} () p₂
⊔₄-func {one} {half} {zero} {one} () p₂
⊔₄-func {one} {half} {forth} {zero} () p₂
⊔₄-func {one} {half} {forth} {forth} () p₂
⊔₄-func {one} {half} {forth} {half} () p₂
⊔₄-func {one} {half} {forth} {one} () p₂
⊔₄-func {one} {half} {half} {zero} () p₂
⊔₄-func {one} {half} {half} {forth} () p₂
⊔₄-func {one} {half} {half} {half} () p₂
⊔₄-func {one} {half} {half} {one} () p₂
⊔₄-func {one} {half} {one} {zero} () p₂
⊔₄-func {one} {half} {one} {forth} () p₂
⊔₄-func {one} {half} {one} {half} () p₂
⊔₄-func {one} {half} {one} {one} () p₂
⊔₄-func {one} {one} {zero} {zero} triv triv = triv
⊔₄-func {one} {one} {zero} {forth} triv triv = triv
⊔₄-func {one} {one} {zero} {half} triv triv = triv
⊔₄-func {one} {one} {zero} {one} triv triv = triv
⊔₄-func {one} {one} {forth} {zero} triv ()
⊔₄-func {one} {one} {forth} {forth} triv triv = triv
⊔₄-func {one} {one} {forth} {half} triv triv = triv
⊔₄-func {one} {one} {forth} {one} triv triv = triv
⊔₄-func {one} {one} {half} {zero} triv ()
⊔₄-func {one} {one} {half} {forth} triv ()
⊔₄-func {one} {one} {half} {half} triv triv = triv
⊔₄-func {one} {one} {half} {one} triv triv = triv
⊔₄-func {one} {one} {one} {zero} triv ()
⊔₄-func {one} {one} {one} {forth} triv ()
⊔₄-func {one} {one} {one} {half} triv ()
⊔₄-func {one} {one} {one} {one} triv triv = triv

⊔₄-contract : ∀{a} → (a ⊔₄ a) ≡ a
⊔₄-contract {zero} = refl
⊔₄-contract {forth} = refl
⊔₄-contract {half} = refl
⊔₄-contract {one} = refl

⊗₄-func : ∀{a c b d} → a ≤₄ c → b ≤₄ d → (a ⊗₄ b) ≤₄ (c ⊗₄ d)
⊗₄-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
⊗₄-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
⊗₄-func {zero} {zero} {forth} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {forth} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {forth} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {forth} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
⊗₄-func {zero} {forth} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {forth} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
⊗₄-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
⊗₄-func {zero} {forth} {forth} {half} p₁ p₂ = triv
⊗₄-func {zero} {forth} {forth} {one} p₁ p₂ = triv
⊗₄-func {zero} {forth} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {forth} {half} {forth} p₁ p₂ = triv
⊗₄-func {zero} {forth} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {forth} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {forth} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {forth} {one} {forth} p₁ p₂ = triv
⊗₄-func {zero} {forth} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {forth} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {forth} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {forth} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {forth} {forth} p₁ p₂ = triv
⊗₄-func {zero} {half} {forth} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {forth} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {forth} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {forth} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {forth} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {forth} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {forth} {forth} p₁ p₂ = triv
⊗₄-func {zero} {one} {forth} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {forth} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {forth} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {forth} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {zero} {one} {one} {one} p₁ p₂ = triv
⊗₄-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
⊗₄-func {forth} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {forth} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {forth} {zero} {forth} {zero} () ()
⊗₄-func {forth} {zero} {forth} {forth} () p₂
⊗₄-func {forth} {zero} {forth} {half} () p₂
⊗₄-func {forth} {zero} {forth} {one} () p₂
⊗₄-func {forth} {zero} {half} {zero} () p₂
⊗₄-func {forth} {zero} {half} {forth} () p₂
⊗₄-func {forth} {zero} {half} {half} () p₂
⊗₄-func {forth} {zero} {half} {one} () p₂
⊗₄-func {forth} {zero} {one} {zero} () p₂
⊗₄-func {forth} {zero} {one} {forth} () p₂
⊗₄-func {forth} {zero} {one} {half} () p₂
⊗₄-func {forth} {zero} {one} {one} () p₂
⊗₄-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
⊗₄-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
⊗₄-func {forth} {forth} {zero} {half} p₁ p₂ = triv
⊗₄-func {forth} {forth} {zero} {one} p₁ p₂ = triv
⊗₄-func {forth} {forth} {forth} {zero} triv ()
⊗₄-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
⊗₄-func {forth} {forth} {forth} {half} p₁ p₂ = triv
⊗₄-func {forth} {forth} {forth} {one} p₁ p₂ = triv
⊗₄-func {forth} {forth} {half} {zero} triv ()
⊗₄-func {forth} {forth} {half} {forth} triv ()
⊗₄-func {forth} {forth} {half} {half} p₁ p₂ = triv
⊗₄-func {forth} {forth} {half} {one} p₁ p₂ = triv
⊗₄-func {forth} {forth} {one} {zero} triv ()
⊗₄-func {forth} {forth} {one} {forth} triv ()
⊗₄-func {forth} {forth} {one} {half} triv ()
⊗₄-func {forth} {forth} {one} {one} p₁ p₂ = triv
⊗₄-func {forth} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {forth} {half} {zero} {forth} p₁ p₂ = triv
⊗₄-func {forth} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {forth} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {forth} {half} {forth} {zero} triv ()
⊗₄-func {forth} {half} {forth} {forth} p₁ p₂ = triv
⊗₄-func {forth} {half} {forth} {half} p₁ p₂ = triv
⊗₄-func {forth} {half} {forth} {one} p₁ p₂ = triv
⊗₄-func {forth} {half} {half} {zero} triv ()
⊗₄-func {forth} {half} {half} {forth} p₁ p₂ = triv
⊗₄-func {forth} {half} {half} {half} p₁ p₂ = triv
⊗₄-func {forth} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {forth} {half} {one} {zero} triv ()
⊗₄-func {forth} {half} {one} {forth} triv ()
⊗₄-func {forth} {half} {one} {half} triv ()
⊗₄-func {forth} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {forth} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {forth} {one} {zero} {forth} p₁ p₂ = triv
⊗₄-func {forth} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {forth} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {forth} {one} {forth} {zero} triv ()
⊗₄-func {forth} {one} {forth} {forth} p₁ p₂ = triv
⊗₄-func {forth} {one} {forth} {half} p₁ p₂ = triv
⊗₄-func {forth} {one} {forth} {one} p₁ p₂ = triv
⊗₄-func {forth} {one} {half} {zero} triv ()
⊗₄-func {forth} {one} {half} {forth} p₁ p₂ = triv
⊗₄-func {forth} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {forth} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {forth} {one} {one} {zero} triv ()
⊗₄-func {forth} {one} {one} {forth} p₁ p₂ = triv
⊗₄-func {forth} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {forth} {one} {one} {one} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {forth} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {zero} {forth} {zero} () p₂
⊗₄-func {half} {zero} {forth} {forth} () p₂
⊗₄-func {half} {zero} {forth} {half} () p₂
⊗₄-func {half} {zero} {forth} {one} () p₂
⊗₄-func {half} {zero} {half} {zero} () p₂
⊗₄-func {half} {zero} {half} {forth} () p₂
⊗₄-func {half} {zero} {half} {half} () p₂
⊗₄-func {half} {zero} {half} {one} () p₂
⊗₄-func {half} {zero} {one} {zero} () p₂
⊗₄-func {half} {zero} {one} {forth} () p₂
⊗₄-func {half} {zero} {one} {half} () p₂
⊗₄-func {half} {zero} {one} {one} () p₂
⊗₄-func {half} {forth} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {forth} {zero} {forth} p₁ p₂ = triv
⊗₄-func {half} {forth} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {forth} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {forth} {forth} {zero} () p₂
⊗₄-func {half} {forth} {forth} {forth} () p₂
⊗₄-func {half} {forth} {forth} {half} p₁ p₂ = triv
⊗₄-func {half} {forth} {forth} {one} p₁ p₂ = triv
⊗₄-func {half} {forth} {half} {zero} () p₂
⊗₄-func {half} {forth} {half} {forth} () p₂
⊗₄-func {half} {forth} {half} {half} p₁ p₂ = triv
⊗₄-func {half} {forth} {half} {one} p₁ p₂ = triv
⊗₄-func {half} {forth} {one} {zero} () p₂
⊗₄-func {half} {forth} {one} {forth} () p₂
⊗₄-func {half} {forth} {one} {half} () p₂
⊗₄-func {half} {forth} {one} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {forth} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {forth} {zero} triv ()
⊗₄-func {half} {half} {forth} {forth} p₁ p₂ = triv
⊗₄-func {half} {half} {forth} {half} p₁ p₂ = triv
⊗₄-func {half} {half} {forth} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {half} {zero} triv ()
⊗₄-func {half} {half} {half} {forth} p₁ p₂ = triv
⊗₄-func {half} {half} {half} {half} p₁ p₂ = triv
⊗₄-func {half} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {half} {half} {one} {zero} triv ()
⊗₄-func {half} {half} {one} {forth} triv ()
⊗₄-func {half} {half} {one} {half} triv ()
⊗₄-func {half} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {forth} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {forth} {zero} triv ()
⊗₄-func {half} {one} {forth} {forth} p₁ p₂ = triv
⊗₄-func {half} {one} {forth} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {forth} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {half} {zero} triv ()
⊗₄-func {half} {one} {half} {forth} p₁ p₂ = triv
⊗₄-func {half} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {half} {one} {one} {zero} triv ()
⊗₄-func {half} {one} {one} {forth} p₁ p₂ = triv
⊗₄-func {half} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {half} {one} {one} {one} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {forth} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {zero} {forth} {zero} () p₂
⊗₄-func {one} {zero} {forth} {forth} () p₂
⊗₄-func {one} {zero} {forth} {half} () p₂
⊗₄-func {one} {zero} {forth} {one} () p₂
⊗₄-func {one} {zero} {half} {zero} () p₂
⊗₄-func {one} {zero} {half} {forth} () p₂
⊗₄-func {one} {zero} {half} {half} () p₂
⊗₄-func {one} {zero} {half} {one} () p₂
⊗₄-func {one} {zero} {one} {zero} () p₂
⊗₄-func {one} {zero} {one} {forth} () p₂
⊗₄-func {one} {zero} {one} {half} () p₂
⊗₄-func {one} {zero} {one} {one} () p₂
⊗₄-func {one} {forth} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {forth} {zero} {forth} p₁ p₂ = triv
⊗₄-func {one} {forth} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {forth} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {forth} {forth} {zero} () p₂
⊗₄-func {one} {forth} {forth} {forth} () p₂
⊗₄-func {one} {forth} {forth} {half} () p₂
⊗₄-func {one} {forth} {forth} {one} p₁ p₂ = triv
⊗₄-func {one} {forth} {half} {zero} () p₂
⊗₄-func {one} {forth} {half} {forth} () p₂
⊗₄-func {one} {forth} {half} {half} () p₂
⊗₄-func {one} {forth} {half} {one} p₁ p₂ = triv
⊗₄-func {one} {forth} {one} {zero} () p₂
⊗₄-func {one} {forth} {one} {forth} () p₂
⊗₄-func {one} {forth} {one} {half} () p₂
⊗₄-func {one} {forth} {one} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {forth} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {half} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {forth} {zero} () p₂
⊗₄-func {one} {half} {forth} {forth} () p₂
⊗₄-func {one} {half} {forth} {half} () p₂
⊗₄-func {one} {half} {forth} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {half} {zero} () p₂
⊗₄-func {one} {half} {half} {forth} () p₂
⊗₄-func {one} {half} {half} {half} () p₂
⊗₄-func {one} {half} {half} {one} p₁ p₂ = triv
⊗₄-func {one} {half} {one} {zero} () p₂
⊗₄-func {one} {half} {one} {forth} () p₂
⊗₄-func {one} {half} {one} {half} () p₂
⊗₄-func {one} {half} {one} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {zero} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {forth} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {zero} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {forth} {zero} triv ()
⊗₄-func {one} {one} {forth} {forth} p₁ p₂ = triv
⊗₄-func {one} {one} {forth} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {forth} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {half} {zero} triv ()
⊗₄-func {one} {one} {half} {forth} p₁ p₂ = triv
⊗₄-func {one} {one} {half} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {half} {one} p₁ p₂ = triv
⊗₄-func {one} {one} {one} {zero} triv ()
⊗₄-func {one} {one} {one} {forth} p₁ p₂ = triv
⊗₄-func {one} {one} {one} {half} p₁ p₂ = triv
⊗₄-func {one} {one} {one} {one} p₁ p₂ = triv

⊗₄-compat : ∀{a b c} → a ≤₄ b → (a ⊗₄ c) ≤₄ (b ⊗₄ c)
⊗₄-compat {a}{b}{c} p = ⊗₄-func {a}{b}{c}{c} p (refl₄ {c})

⊗₄-unitl : ∀{a} → (a ⊗₄ I₄) ≡ a
⊗₄-unitl {zero} = refl
⊗₄-unitl {forth} = refl
⊗₄-unitl {half} = refl
⊗₄-unitl {one} = refl

⊗₄-unitr : ∀{a} → (I₄ ⊗₄ a) ≡ a
⊗₄-unitr {zero} = refl
⊗₄-unitr {forth} = refl
⊗₄-unitr {half} = refl
⊗₄-unitr {one} = refl

⊗₄-sym : ∀{a b} → (a ⊗₄ b) ≡ (b ⊗₄ a)
⊗₄-sym {zero} {zero} = refl
⊗₄-sym {zero} {forth} = refl
⊗₄-sym {zero} {half} = refl
⊗₄-sym {zero} {one} = refl
⊗₄-sym {forth} {zero} = refl
⊗₄-sym {forth} {forth} = refl
⊗₄-sym {forth} {half} = refl
⊗₄-sym {forth} {one} = refl
⊗₄-sym {half} {zero} = refl
⊗₄-sym {half} {forth} = refl
⊗₄-sym {half} {half} = refl
⊗₄-sym {half} {one} = refl
⊗₄-sym {one} {zero} = refl
⊗₄-sym {one} {forth} = refl
⊗₄-sym {one} {half} = refl
⊗₄-sym {one} {one} = refl

⊗₄-assoc : ∀{a b c} → ((a ⊗₄ b) ⊗₄ c) ≡ (a ⊗₄ (b ⊗₄ c))
⊗₄-assoc {zero} {zero} {zero} = refl
⊗₄-assoc {zero} {zero} {forth} = refl
⊗₄-assoc {zero} {zero} {half} = refl
⊗₄-assoc {zero} {zero} {one} = refl
⊗₄-assoc {zero} {forth} {zero} = refl
⊗₄-assoc {zero} {forth} {forth} = refl
⊗₄-assoc {zero} {forth} {half} = refl
⊗₄-assoc {zero} {forth} {one} = refl
⊗₄-assoc {zero} {half} {zero} = refl
⊗₄-assoc {zero} {half} {forth} = refl
⊗₄-assoc {zero} {half} {half} = refl
⊗₄-assoc {zero} {half} {one} = refl
⊗₄-assoc {zero} {one} {zero} = refl
⊗₄-assoc {zero} {one} {forth} = refl
⊗₄-assoc {zero} {one} {half} = refl
⊗₄-assoc {zero} {one} {one} = refl
⊗₄-assoc {forth} {zero} {zero} = refl
⊗₄-assoc {forth} {zero} {forth} = refl
⊗₄-assoc {forth} {zero} {half} = refl
⊗₄-assoc {forth} {zero} {one} = refl
⊗₄-assoc {forth} {forth} {zero} = refl
⊗₄-assoc {forth} {forth} {forth} = refl
⊗₄-assoc {forth} {forth} {half} = refl
⊗₄-assoc {forth} {forth} {one} = refl
⊗₄-assoc {forth} {half} {zero} = refl
⊗₄-assoc {forth} {half} {forth} = refl
⊗₄-assoc {forth} {half} {half} = refl
⊗₄-assoc {forth} {half} {one} = refl
⊗₄-assoc {forth} {one} {zero} = refl
⊗₄-assoc {forth} {one} {forth} = refl
⊗₄-assoc {forth} {one} {half} = refl
⊗₄-assoc {forth} {one} {one} = refl
⊗₄-assoc {half} {zero} {zero} = refl
⊗₄-assoc {half} {zero} {forth} = refl
⊗₄-assoc {half} {zero} {half} = refl
⊗₄-assoc {half} {zero} {one} = refl
⊗₄-assoc {half} {forth} {zero} = refl
⊗₄-assoc {half} {forth} {forth} = refl
⊗₄-assoc {half} {forth} {half} = refl
⊗₄-assoc {half} {forth} {one} = refl
⊗₄-assoc {half} {half} {zero} = refl
⊗₄-assoc {half} {half} {forth} = refl
⊗₄-assoc {half} {half} {half} = refl
⊗₄-assoc {half} {half} {one} = refl
⊗₄-assoc {half} {one} {zero} = refl
⊗₄-assoc {half} {one} {forth} = refl
⊗₄-assoc {half} {one} {half} = refl
⊗₄-assoc {half} {one} {one} = refl
⊗₄-assoc {one} {zero} {zero} = refl
⊗₄-assoc {one} {zero} {forth} = refl
⊗₄-assoc {one} {zero} {half} = refl
⊗₄-assoc {one} {zero} {one} = refl
⊗₄-assoc {one} {forth} {zero} = refl
⊗₄-assoc {one} {forth} {forth} = refl
⊗₄-assoc {one} {forth} {half} = refl
⊗₄-assoc {one} {forth} {one} = refl
⊗₄-assoc {one} {half} {zero} = refl
⊗₄-assoc {one} {half} {forth} = refl
⊗₄-assoc {one} {half} {half} = refl
⊗₄-assoc {one} {half} {one} = refl
⊗₄-assoc {one} {one} {zero} = refl
⊗₄-assoc {one} {one} {forth} = refl
⊗₄-assoc {one} {one} {half} = refl
⊗₄-assoc {one} {one} {one} = refl

⊸₄-func : ∀{c a b d} → c ≤₄ a → b ≤₄ d → (a ⊸₄ b) ≤₄ (c ⊸₄ d)
⊸₄-func {zero} {zero} {zero} {zero} triv triv = triv
⊸₄-func {zero} {zero} {zero} {forth} triv triv = triv
⊸₄-func {zero} {zero} {zero} {half} triv triv = triv
⊸₄-func {zero} {zero} {zero} {one} triv triv = triv
⊸₄-func {zero} {zero} {forth} {zero} triv ()
⊸₄-func {zero} {zero} {forth} {forth} triv triv = triv
⊸₄-func {zero} {zero} {forth} {half} triv triv = triv
⊸₄-func {zero} {zero} {forth} {one} triv triv = triv
⊸₄-func {zero} {zero} {half} {zero} triv ()
⊸₄-func {zero} {zero} {half} {forth} triv ()
⊸₄-func {zero} {zero} {half} {half} triv triv = triv
⊸₄-func {zero} {zero} {half} {one} triv triv = triv
⊸₄-func {zero} {zero} {one} {zero} triv ()
⊸₄-func {zero} {zero} {one} {forth} triv ()
⊸₄-func {zero} {zero} {one} {half} triv ()
⊸₄-func {zero} {zero} {one} {one} triv triv = triv
⊸₄-func {zero} {forth} {zero} {zero} triv triv = triv
⊸₄-func {zero} {forth} {zero} {forth} triv triv = triv
⊸₄-func {zero} {forth} {zero} {half} triv triv = triv
⊸₄-func {zero} {forth} {zero} {one} triv triv = triv
⊸₄-func {zero} {forth} {forth} {zero} triv ()
⊸₄-func {zero} {forth} {forth} {forth} triv triv = triv
⊸₄-func {zero} {forth} {forth} {half} triv triv = triv
⊸₄-func {zero} {forth} {forth} {one} triv triv = triv
⊸₄-func {zero} {forth} {half} {zero} triv ()
⊸₄-func {zero} {forth} {half} {forth} triv ()
⊸₄-func {zero} {forth} {half} {half} triv triv = triv
⊸₄-func {zero} {forth} {half} {one} triv triv = triv
⊸₄-func {zero} {forth} {one} {zero} triv ()
⊸₄-func {zero} {forth} {one} {forth} triv ()
⊸₄-func {zero} {forth} {one} {half} triv ()
⊸₄-func {zero} {forth} {one} {one} triv triv = triv
⊸₄-func {zero} {half} {zero} {zero} triv triv = triv
⊸₄-func {zero} {half} {zero} {forth} triv triv = triv
⊸₄-func {zero} {half} {zero} {half} triv triv = triv
⊸₄-func {zero} {half} {zero} {one} triv triv = triv
⊸₄-func {zero} {half} {forth} {zero} triv ()
⊸₄-func {zero} {half} {forth} {forth} triv triv = triv
⊸₄-func {zero} {half} {forth} {half} triv triv = triv
⊸₄-func {zero} {half} {forth} {one} triv triv = triv
⊸₄-func {zero} {half} {half} {zero} triv ()
⊸₄-func {zero} {half} {half} {forth} triv ()
⊸₄-func {zero} {half} {half} {half} triv triv = triv
⊸₄-func {zero} {half} {half} {one} triv triv = triv
⊸₄-func {zero} {half} {one} {zero} triv ()
⊸₄-func {zero} {half} {one} {forth} triv ()
⊸₄-func {zero} {half} {one} {half} triv ()
⊸₄-func {zero} {half} {one} {one} triv triv = triv
⊸₄-func {zero} {one} {zero} {zero} triv triv = triv
⊸₄-func {zero} {one} {zero} {forth} triv triv = triv
⊸₄-func {zero} {one} {zero} {half} triv triv = triv
⊸₄-func {zero} {one} {zero} {one} triv triv = triv
⊸₄-func {zero} {one} {forth} {zero} triv ()
⊸₄-func {zero} {one} {forth} {forth} triv triv = triv
⊸₄-func {zero} {one} {forth} {half} triv triv = triv
⊸₄-func {zero} {one} {forth} {one} triv triv = triv
⊸₄-func {zero} {one} {half} {zero} triv ()
⊸₄-func {zero} {one} {half} {forth} triv ()
⊸₄-func {zero} {one} {half} {half} triv triv = triv
⊸₄-func {zero} {one} {half} {one} triv triv = triv
⊸₄-func {zero} {one} {one} {zero} triv ()
⊸₄-func {zero} {one} {one} {forth} triv ()
⊸₄-func {zero} {one} {one} {half} triv ()
⊸₄-func {zero} {one} {one} {one} triv triv = triv
⊸₄-func {forth} {zero} {zero} {zero} () p₂
⊸₄-func {forth} {zero} {zero} {forth} () p₂
⊸₄-func {forth} {zero} {zero} {half} () p₂
⊸₄-func {forth} {zero} {zero} {one} () p₂
⊸₄-func {forth} {zero} {forth} {zero} () p₂
⊸₄-func {forth} {zero} {forth} {forth} () p₂
⊸₄-func {forth} {zero} {forth} {half} () p₂
⊸₄-func {forth} {zero} {forth} {one} () p₂
⊸₄-func {forth} {zero} {half} {zero} () p₂
⊸₄-func {forth} {zero} {half} {forth} () p₂
⊸₄-func {forth} {zero} {half} {half} () p₂
⊸₄-func {forth} {zero} {half} {one} () p₂
⊸₄-func {forth} {zero} {one} {zero} () p₂
⊸₄-func {forth} {zero} {one} {forth} () p₂
⊸₄-func {forth} {zero} {one} {half} () p₂
⊸₄-func {forth} {zero} {one} {one} () p₂
⊸₄-func {forth} {forth} {zero} {zero} triv triv = triv
⊸₄-func {forth} {forth} {zero} {forth} triv triv = triv
⊸₄-func {forth} {forth} {zero} {half} triv triv = triv
⊸₄-func {forth} {forth} {zero} {one} triv triv = triv
⊸₄-func {forth} {forth} {forth} {zero} triv ()
⊸₄-func {forth} {forth} {forth} {forth} triv triv = triv
⊸₄-func {forth} {forth} {forth} {half} triv triv = triv
⊸₄-func {forth} {forth} {forth} {one} triv triv = triv
⊸₄-func {forth} {forth} {half} {zero} triv ()
⊸₄-func {forth} {forth} {half} {forth} triv ()
⊸₄-func {forth} {forth} {half} {half} triv triv = triv
⊸₄-func {forth} {forth} {half} {one} triv triv = triv
⊸₄-func {forth} {forth} {one} {zero} triv ()
⊸₄-func {forth} {forth} {one} {forth} triv ()
⊸₄-func {forth} {forth} {one} {half} triv ()
⊸₄-func {forth} {forth} {one} {one} triv triv = triv
⊸₄-func {forth} {half} {zero} {zero} triv triv = triv
⊸₄-func {forth} {half} {zero} {forth} triv triv = triv
⊸₄-func {forth} {half} {zero} {half} triv triv = triv
⊸₄-func {forth} {half} {zero} {one} triv triv = triv
⊸₄-func {forth} {half} {forth} {zero} triv ()
⊸₄-func {forth} {half} {forth} {forth} triv triv = triv
⊸₄-func {forth} {half} {forth} {half} triv triv = triv
⊸₄-func {forth} {half} {forth} {one} triv triv = triv
⊸₄-func {forth} {half} {half} {zero} triv ()
⊸₄-func {forth} {half} {half} {forth} triv ()
⊸₄-func {forth} {half} {half} {half} triv triv = triv
⊸₄-func {forth} {half} {half} {one} triv triv = triv
⊸₄-func {forth} {half} {one} {zero} triv ()
⊸₄-func {forth} {half} {one} {forth} triv ()
⊸₄-func {forth} {half} {one} {half} triv ()
⊸₄-func {forth} {half} {one} {one} triv triv = triv
⊸₄-func {forth} {one} {zero} {zero} triv triv = triv
⊸₄-func {forth} {one} {zero} {forth} triv triv = triv
⊸₄-func {forth} {one} {zero} {half} triv triv = triv
⊸₄-func {forth} {one} {zero} {one} triv triv = triv
⊸₄-func {forth} {one} {forth} {zero} triv ()
⊸₄-func {forth} {one} {forth} {forth} triv triv = triv
⊸₄-func {forth} {one} {forth} {half} triv triv = triv
⊸₄-func {forth} {one} {forth} {one} triv triv = triv
⊸₄-func {forth} {one} {half} {zero} triv ()
⊸₄-func {forth} {one} {half} {forth} triv ()
⊸₄-func {forth} {one} {half} {half} triv triv = triv
⊸₄-func {forth} {one} {half} {one} triv triv = triv
⊸₄-func {forth} {one} {one} {zero} triv ()
⊸₄-func {forth} {one} {one} {forth} triv ()
⊸₄-func {forth} {one} {one} {half} triv ()
⊸₄-func {forth} {one} {one} {one} triv triv = triv
⊸₄-func {half} {zero} {zero} {zero} () p₂
⊸₄-func {half} {zero} {zero} {forth} () p₂
⊸₄-func {half} {zero} {zero} {half} () p₂
⊸₄-func {half} {zero} {zero} {one} () p₂
⊸₄-func {half} {zero} {forth} {zero} () p₂
⊸₄-func {half} {zero} {forth} {forth} () p₂
⊸₄-func {half} {zero} {forth} {half} () p₂
⊸₄-func {half} {zero} {forth} {one} () p₂
⊸₄-func {half} {zero} {half} {zero} () p₂
⊸₄-func {half} {zero} {half} {forth} () p₂
⊸₄-func {half} {zero} {half} {half} () p₂
⊸₄-func {half} {zero} {half} {one} () p₂
⊸₄-func {half} {zero} {one} {zero} () p₂
⊸₄-func {half} {zero} {one} {forth} () p₂
⊸₄-func {half} {zero} {one} {half} () p₂
⊸₄-func {half} {zero} {one} {one} () p₂
⊸₄-func {half} {forth} {zero} {zero} () p₂
⊸₄-func {half} {forth} {zero} {forth} () p₂
⊸₄-func {half} {forth} {zero} {half} () p₂
⊸₄-func {half} {forth} {zero} {one} () p₂
⊸₄-func {half} {forth} {forth} {zero} () p₂
⊸₄-func {half} {forth} {forth} {forth} () p₂
⊸₄-func {half} {forth} {forth} {half} () p₂
⊸₄-func {half} {forth} {forth} {one} () p₂
⊸₄-func {half} {forth} {half} {zero} () p₂
⊸₄-func {half} {forth} {half} {forth} () p₂
⊸₄-func {half} {forth} {half} {half} () p₂
⊸₄-func {half} {forth} {half} {one} () p₂
⊸₄-func {half} {forth} {one} {zero} () p₂
⊸₄-func {half} {forth} {one} {forth} () p₂
⊸₄-func {half} {forth} {one} {half} () p₂
⊸₄-func {half} {forth} {one} {one} () p₂
⊸₄-func {half} {half} {zero} {zero} triv triv = triv
⊸₄-func {half} {half} {zero} {forth} triv triv = triv
⊸₄-func {half} {half} {zero} {half} triv triv = triv
⊸₄-func {half} {half} {zero} {one} triv triv = triv
⊸₄-func {half} {half} {forth} {zero} triv ()
⊸₄-func {half} {half} {forth} {forth} triv triv = triv
⊸₄-func {half} {half} {forth} {half} triv triv = triv
⊸₄-func {half} {half} {forth} {one} triv triv = triv
⊸₄-func {half} {half} {half} {zero} triv ()
⊸₄-func {half} {half} {half} {forth} triv ()
⊸₄-func {half} {half} {half} {half} triv triv = triv
⊸₄-func {half} {half} {half} {one} triv triv = triv
⊸₄-func {half} {half} {one} {zero} triv ()
⊸₄-func {half} {half} {one} {forth} triv ()
⊸₄-func {half} {half} {one} {half} triv ()
⊸₄-func {half} {half} {one} {one} triv triv = triv
⊸₄-func {half} {one} {zero} {zero} triv triv = triv
⊸₄-func {half} {one} {zero} {forth} triv triv = triv
⊸₄-func {half} {one} {zero} {half} triv triv = triv
⊸₄-func {half} {one} {zero} {one} triv triv = triv
⊸₄-func {half} {one} {forth} {zero} triv ()
⊸₄-func {half} {one} {forth} {forth} triv triv = triv
⊸₄-func {half} {one} {forth} {half} triv triv = triv
⊸₄-func {half} {one} {forth} {one} triv triv = triv
⊸₄-func {half} {one} {half} {zero} triv ()
⊸₄-func {half} {one} {half} {forth} triv ()
⊸₄-func {half} {one} {half} {half} triv triv = triv
⊸₄-func {half} {one} {half} {one} triv triv = triv
⊸₄-func {half} {one} {one} {zero} triv ()
⊸₄-func {half} {one} {one} {forth} triv ()
⊸₄-func {half} {one} {one} {half} triv ()
⊸₄-func {half} {one} {one} {one} triv triv = triv
⊸₄-func {one} {zero} {zero} {zero} () p₂
⊸₄-func {one} {zero} {zero} {forth} () p₂
⊸₄-func {one} {zero} {zero} {half} () p₂
⊸₄-func {one} {zero} {zero} {one} () p₂
⊸₄-func {one} {zero} {forth} {zero} () p₂
⊸₄-func {one} {zero} {forth} {forth} () p₂
⊸₄-func {one} {zero} {forth} {half} () p₂
⊸₄-func {one} {zero} {forth} {one} () p₂
⊸₄-func {one} {zero} {half} {zero} () p₂
⊸₄-func {one} {zero} {half} {forth} () p₂
⊸₄-func {one} {zero} {half} {half} () p₂
⊸₄-func {one} {zero} {half} {one} () p₂
⊸₄-func {one} {zero} {one} {zero} () p₂
⊸₄-func {one} {zero} {one} {forth} () p₂
⊸₄-func {one} {zero} {one} {half} () p₂
⊸₄-func {one} {zero} {one} {one} () p₂
⊸₄-func {one} {forth} {zero} {zero} () p₂
⊸₄-func {one} {forth} {zero} {forth} () p₂
⊸₄-func {one} {forth} {zero} {half} () p₂
⊸₄-func {one} {forth} {zero} {one} () p₂
⊸₄-func {one} {forth} {forth} {zero} () p₂
⊸₄-func {one} {forth} {forth} {forth} () p₂
⊸₄-func {one} {forth} {forth} {half} () p₂
⊸₄-func {one} {forth} {forth} {one} () p₂
⊸₄-func {one} {forth} {half} {zero} () p₂
⊸₄-func {one} {forth} {half} {forth} () p₂
⊸₄-func {one} {forth} {half} {half} () p₂
⊸₄-func {one} {forth} {half} {one} () p₂
⊸₄-func {one} {forth} {one} {zero} () p₂
⊸₄-func {one} {forth} {one} {forth} () p₂
⊸₄-func {one} {forth} {one} {half} () p₂
⊸₄-func {one} {forth} {one} {one} () p₂
⊸₄-func {one} {half} {zero} {zero} () p₂
⊸₄-func {one} {half} {zero} {forth} () p₂
⊸₄-func {one} {half} {zero} {half} () p₂
⊸₄-func {one} {half} {zero} {one} () p₂
⊸₄-func {one} {half} {forth} {zero} () p₂
⊸₄-func {one} {half} {forth} {forth} () p₂
⊸₄-func {one} {half} {forth} {half} () p₂
⊸₄-func {one} {half} {forth} {one} () p₂
⊸₄-func {one} {half} {half} {zero} () p₂
⊸₄-func {one} {half} {half} {forth} () p₂
⊸₄-func {one} {half} {half} {half} () p₂
⊸₄-func {one} {half} {half} {one} () p₂
⊸₄-func {one} {half} {one} {zero} () p₂
⊸₄-func {one} {half} {one} {forth} () p₂
⊸₄-func {one} {half} {one} {half} () p₂
⊸₄-func {one} {half} {one} {one} () p₂
⊸₄-func {one} {one} {zero} {zero} triv triv = triv
⊸₄-func {one} {one} {zero} {forth} triv triv = triv
⊸₄-func {one} {one} {zero} {half} triv triv = triv
⊸₄-func {one} {one} {zero} {one} triv triv = triv
⊸₄-func {one} {one} {forth} {zero} triv ()
⊸₄-func {one} {one} {forth} {forth} triv triv = triv
⊸₄-func {one} {one} {forth} {half} triv triv = triv
⊸₄-func {one} {one} {forth} {one} triv triv = triv
⊸₄-func {one} {one} {half} {zero} triv ()
⊸₄-func {one} {one} {half} {forth} triv ()
⊸₄-func {one} {one} {half} {half} triv triv = triv
⊸₄-func {one} {one} {half} {one} triv triv = triv
⊸₄-func {one} {one} {one} {zero} triv ()
⊸₄-func {one} {one} {one} {forth} triv ()
⊸₄-func {one} {one} {one} {half} triv ()
⊸₄-func {one} {one} {one} {one} triv triv = triv

curry₄ : ∀{a b c} → (a ⊗₄ b) ≤₄ c → a ≤₄ (b ⊸₄ c)
curry₄ {zero} {zero} {zero} p = triv
curry₄ {zero} {zero} {forth} p = triv
curry₄ {zero} {zero} {half} p = triv
curry₄ {zero} {zero} {one} p = triv
curry₄ {zero} {forth} {zero} p = triv
curry₄ {zero} {forth} {forth} p = triv
curry₄ {zero} {forth} {half} p = triv
curry₄ {zero} {forth} {one} p = triv
curry₄ {zero} {half} {zero} p = triv
curry₄ {zero} {half} {forth} p = triv
curry₄ {zero} {half} {half} p = triv
curry₄ {zero} {half} {one} p = triv
curry₄ {zero} {one} {zero} p = triv
curry₄ {zero} {one} {forth} p = triv
curry₄ {zero} {one} {half} p = triv
curry₄ {zero} {one} {one} p = triv
curry₄ {forth} {zero} {zero} p = triv
curry₄ {forth} {zero} {forth} p = triv
curry₄ {forth} {zero} {half} p = triv
curry₄ {forth} {zero} {one} p = triv
curry₄ {forth} {forth} {zero} ()
curry₄ {forth} {forth} {forth} p = triv
curry₄ {forth} {forth} {half} p = triv
curry₄ {forth} {forth} {one} p = triv
curry₄ {forth} {half} {zero} ()
curry₄ {forth} {half} {forth} ()
curry₄ {forth} {half} {half} p = triv
curry₄ {forth} {half} {one} p = triv
curry₄ {forth} {one} {zero} ()
curry₄ {forth} {one} {forth} ()
curry₄ {forth} {one} {half} ()
curry₄ {forth} {one} {one} p = triv
curry₄ {half} {zero} {zero} p = triv
curry₄ {half} {zero} {forth} p = triv
curry₄ {half} {zero} {half} p = triv
curry₄ {half} {zero} {one} p = triv
curry₄ {half} {forth} {zero} ()
curry₄ {half} {forth} {forth} ()
curry₄ {half} {forth} {half} p = triv
curry₄ {half} {forth} {one} p = triv
curry₄ {half} {half} {zero} ()
curry₄ {half} {half} {forth} ()
curry₄ {half} {half} {half} p = triv
curry₄ {half} {half} {one} p = triv
curry₄ {half} {one} {zero} ()
curry₄ {half} {one} {forth} ()
curry₄ {half} {one} {half} ()
curry₄ {half} {one} {one} p = triv
curry₄ {one} {zero} {zero} p = triv
curry₄ {one} {zero} {forth} p = triv
curry₄ {one} {zero} {half} p = triv
curry₄ {one} {zero} {one} p = triv
curry₄ {one} {forth} {zero} ()
curry₄ {one} {forth} {forth} ()
curry₄ {one} {forth} {half} ()
curry₄ {one} {forth} {one} p = triv
curry₄ {one} {half} {zero} ()
curry₄ {one} {half} {forth} ()
curry₄ {one} {half} {half} ()
curry₄ {one} {half} {one} p = triv
curry₄ {one} {one} {zero} ()
curry₄ {one} {one} {forth} ()
curry₄ {one} {one} {half} ()
curry₄ {one} {one} {one} p = triv

curry₄-inv : ∀{a b c} → a ≤₄ (b ⊸₄ c) → (a ⊗₄ b) ≤₄ c
curry₄-inv {zero} {zero} {zero} p = triv
curry₄-inv {zero} {zero} {forth} p = triv
curry₄-inv {zero} {zero} {half} p = triv
curry₄-inv {zero} {zero} {one} p = triv
curry₄-inv {zero} {forth} {zero} p = triv
curry₄-inv {zero} {forth} {forth} p = triv
curry₄-inv {zero} {forth} {half} p = triv
curry₄-inv {zero} {forth} {one} p = triv
curry₄-inv {zero} {half} {zero} p = triv
curry₄-inv {zero} {half} {forth} p = triv
curry₄-inv {zero} {half} {half} p = triv
curry₄-inv {zero} {half} {one} p = triv
curry₄-inv {zero} {one} {zero} p = triv
curry₄-inv {zero} {one} {forth} p = triv
curry₄-inv {zero} {one} {half} p = triv
curry₄-inv {zero} {one} {one} p = triv
curry₄-inv {forth} {zero} {zero} p = triv
curry₄-inv {forth} {zero} {forth} p = triv
curry₄-inv {forth} {zero} {half} p = triv
curry₄-inv {forth} {zero} {one} p = triv
curry₄-inv {forth} {forth} {zero} ()
curry₄-inv {forth} {forth} {forth} p = triv
curry₄-inv {forth} {forth} {half} p = triv
curry₄-inv {forth} {forth} {one} p = triv
curry₄-inv {forth} {half} {zero} ()
curry₄-inv {forth} {half} {forth} ()
curry₄-inv {forth} {half} {half} p = triv
curry₄-inv {forth} {half} {one} p = triv
curry₄-inv {forth} {one} {zero} ()
curry₄-inv {forth} {one} {forth} ()
curry₄-inv {forth} {one} {half} ()
curry₄-inv {forth} {one} {one} p = triv
curry₄-inv {half} {zero} {zero} p = triv
curry₄-inv {half} {zero} {forth} p = triv
curry₄-inv {half} {zero} {half} p = triv
curry₄-inv {half} {zero} {one} p = triv
curry₄-inv {half} {forth} {zero} ()
curry₄-inv {half} {forth} {forth} ()
curry₄-inv {half} {forth} {half} p = triv
curry₄-inv {half} {forth} {one} p = triv
curry₄-inv {half} {half} {zero} ()
curry₄-inv {half} {half} {forth} ()
curry₄-inv {half} {half} {half} p = triv
curry₄-inv {half} {half} {one} p = triv
curry₄-inv {half} {one} {zero} ()
curry₄-inv {half} {one} {forth} ()
curry₄-inv {half} {one} {half} ()
curry₄-inv {half} {one} {one} p = triv
curry₄-inv {one} {zero} {zero} p = triv
curry₄-inv {one} {zero} {forth} p = triv
curry₄-inv {one} {zero} {half} p = triv
curry₄-inv {one} {zero} {one} p = triv
curry₄-inv {one} {forth} {zero} ()
curry₄-inv {one} {forth} {forth} ()
curry₄-inv {one} {forth} {half} ()
curry₄-inv {one} {forth} {one} p = triv
curry₄-inv {one} {half} {zero} ()
curry₄-inv {one} {half} {forth} ()
curry₄-inv {one} {half} {half} ()
curry₄-inv {one} {half} {one} p = triv
curry₄-inv {one} {one} {zero} ()
curry₄-inv {one} {one} {forth} ()
curry₄-inv {one} {one} {half} ()
curry₄-inv {one} {one} {one} p = triv

relative-comp : ∀{a b} → ((a ⊸₄ b) ⊗₄ a) ≤₄ b
relative-comp {a}{b} = curry₄-inv {a ⊸₄ b}{a}{b} (refl₄ {a ⊸₄ b})

points : ∀{a b} → a ≤₄ b → I₄ ≤₄ (a ⊸₄ b)
points {a}{b} p with fst (iso₄-inv (⊗₄-unitr {a}))
... | r = curry₄ {I₄} {a} {b} (trans₄ {I₄ ⊗₄ a}{a}{b} r p)
