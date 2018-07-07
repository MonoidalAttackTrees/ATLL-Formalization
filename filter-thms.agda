module filter-thms where

open import prelude
open import functions
open import quaternary-semantics
open import quaternary-thms
open import filter-semantics

⊙F-zerol : ∀{x} → (zero ⊙F x) ≤₄ zero
⊙F-zerol {zero} = triv
⊙F-zerol {forth} = triv
⊙F-zerol {half} = triv
⊙F-zerol {one} = triv

⊙F-zeror : ∀{x} → (x ⊙F zero) ≤₄ zero
⊙F-zeror {zero} = triv
⊙F-zeror {forth} = triv
⊙F-zeror {half} = triv
⊙F-zeror {one} = triv

⊙F-contract : (∀{a} → (a ⊙F a) ≡ a) → ⊥ {lzero}
⊙F-contract p with p {half} 
... | () 

⊙F-sym : ∀{a b} → a ⊙F b ≡ b ⊙F a
⊙F-sym {zero} {zero} = refl
⊙F-sym {zero} {forth} = refl
⊙F-sym {zero} {half} = refl
⊙F-sym {zero} {one} = refl
⊙F-sym {forth} {zero} = refl
⊙F-sym {forth} {forth} = refl
⊙F-sym {forth} {half} = refl
⊙F-sym {forth} {one} = refl
⊙F-sym {half} {zero} = refl
⊙F-sym {half} {forth} = refl
⊙F-sym {half} {half} = refl
⊙F-sym {half} {one} = refl
⊙F-sym {one} {zero} = refl
⊙F-sym {one} {forth} = refl
⊙F-sym {one} {half} = refl
⊙F-sym {one} {one} = refl

⊙F-assoc : ∀{a b c} → (a ⊙F b) ⊙F c ≡ a ⊙F (b ⊙F c)
⊙F-assoc {zero} {zero} {zero} = refl
⊙F-assoc {zero} {zero} {forth} = refl
⊙F-assoc {zero} {zero} {half} = refl
⊙F-assoc {zero} {zero} {one} = refl
⊙F-assoc {zero} {forth} {zero} = refl
⊙F-assoc {zero} {forth} {forth} = refl
⊙F-assoc {zero} {forth} {half} = refl
⊙F-assoc {zero} {forth} {one} = refl
⊙F-assoc {zero} {half} {zero} = refl
⊙F-assoc {zero} {half} {forth} = refl
⊙F-assoc {zero} {half} {half} = refl
⊙F-assoc {zero} {half} {one} = refl
⊙F-assoc {zero} {one} {zero} = refl
⊙F-assoc {zero} {one} {forth} = refl
⊙F-assoc {zero} {one} {half} = refl
⊙F-assoc {zero} {one} {one} = refl
⊙F-assoc {forth} {zero} {zero} = refl
⊙F-assoc {forth} {zero} {forth} = refl
⊙F-assoc {forth} {zero} {half} = refl
⊙F-assoc {forth} {zero} {one} = refl
⊙F-assoc {forth} {forth} {zero} = refl
⊙F-assoc {forth} {forth} {forth} = refl
⊙F-assoc {forth} {forth} {half} = refl
⊙F-assoc {forth} {forth} {one} = refl
⊙F-assoc {forth} {half} {zero} = refl
⊙F-assoc {forth} {half} {forth} = refl
⊙F-assoc {forth} {half} {half} = refl
⊙F-assoc {forth} {half} {one} = refl
⊙F-assoc {forth} {one} {zero} = refl
⊙F-assoc {forth} {one} {forth} = refl
⊙F-assoc {forth} {one} {half} = refl
⊙F-assoc {forth} {one} {one} = refl
⊙F-assoc {half} {zero} {zero} = refl
⊙F-assoc {half} {zero} {forth} = refl
⊙F-assoc {half} {zero} {half} = refl
⊙F-assoc {half} {zero} {one} = refl
⊙F-assoc {half} {forth} {zero} = refl
⊙F-assoc {half} {forth} {forth} = refl
⊙F-assoc {half} {forth} {half} = refl
⊙F-assoc {half} {forth} {one} = refl
⊙F-assoc {half} {half} {zero} = refl
⊙F-assoc {half} {half} {forth} = refl
⊙F-assoc {half} {half} {half} = refl
⊙F-assoc {half} {half} {one} = refl
⊙F-assoc {half} {one} {zero} = refl
⊙F-assoc {half} {one} {forth} = refl
⊙F-assoc {half} {one} {half} = refl
⊙F-assoc {half} {one} {one} = refl
⊙F-assoc {one} {zero} {zero} = refl
⊙F-assoc {one} {zero} {forth} = refl
⊙F-assoc {one} {zero} {half} = refl
⊙F-assoc {one} {zero} {one} = refl
⊙F-assoc {one} {forth} {zero} = refl
⊙F-assoc {one} {forth} {forth} = refl
⊙F-assoc {one} {forth} {half} = refl
⊙F-assoc {one} {forth} {one} = refl
⊙F-assoc {one} {half} {zero} = refl
⊙F-assoc {one} {half} {forth} = refl
⊙F-assoc {one} {half} {half} = refl
⊙F-assoc {one} {half} {one} = refl
⊙F-assoc {one} {one} {zero} = refl
⊙F-assoc {one} {one} {forth} = refl
⊙F-assoc {one} {one} {half} = refl
⊙F-assoc {one} {one} {one} = refl

⊙F-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ⊙F b) ≤₄ (c ⊙F d)
⊙F-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊙F-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
⊙F-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊙F-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊙F-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
⊙F-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
⊙F-func {zero} {zero} {forth} {half} p₁ p₂ = triv
⊙F-func {zero} {zero} {forth} {one} p₁ p₂ = triv
⊙F-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊙F-func {zero} {zero} {half} {forth} p₁ p₂ = triv
⊙F-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊙F-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊙F-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊙F-func {zero} {zero} {one} {forth} p₁ p₂ = triv
⊙F-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊙F-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊙F-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
⊙F-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
⊙F-func {zero} {forth} {zero} {half} p₁ p₂ = triv
⊙F-func {zero} {forth} {zero} {one} p₁ p₂ = triv
⊙F-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
⊙F-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
⊙F-func {zero} {forth} {forth} {half} p₁ p₂ = triv
⊙F-func {zero} {forth} {forth} {one} p₁ p₂ = triv
⊙F-func {zero} {forth} {half} {zero} p₁ p₂ = triv
⊙F-func {zero} {forth} {half} {forth} p₁ p₂ = triv
⊙F-func {zero} {forth} {half} {half} p₁ p₂ = triv
⊙F-func {zero} {forth} {half} {one} p₁ p₂ = triv
⊙F-func {zero} {forth} {one} {zero} p₁ p₂ = triv
⊙F-func {zero} {forth} {one} {forth} p₁ p₂ = triv
⊙F-func {zero} {forth} {one} {half} p₁ p₂ = triv
⊙F-func {zero} {forth} {one} {one} p₁ p₂ = triv
⊙F-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊙F-func {zero} {half} {zero} {forth} p₁ p₂ = triv
⊙F-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊙F-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊙F-func {zero} {half} {forth} {zero} p₁ p₂ = triv
⊙F-func {zero} {half} {forth} {forth} p₁ p₂ = triv
⊙F-func {zero} {half} {forth} {half} p₁ p₂ = triv
⊙F-func {zero} {half} {forth} {one} p₁ p₂ = triv
⊙F-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊙F-func {zero} {half} {half} {forth} p₁ p₂ = triv
⊙F-func {zero} {half} {half} {half} p₁ p₂ = triv
⊙F-func {zero} {half} {half} {one} p₁ p₂ = triv
⊙F-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊙F-func {zero} {half} {one} {forth} p₁ p₂ = triv
⊙F-func {zero} {half} {one} {half} p₁ p₂ = triv
⊙F-func {zero} {half} {one} {one} p₁ p₂ = triv
⊙F-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊙F-func {zero} {one} {zero} {forth} p₁ p₂ = triv
⊙F-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊙F-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊙F-func {zero} {one} {forth} {zero} p₁ p₂ = triv
⊙F-func {zero} {one} {forth} {forth} p₁ p₂ = triv
⊙F-func {zero} {one} {forth} {half} p₁ p₂ = triv
⊙F-func {zero} {one} {forth} {one} p₁ p₂ = triv
⊙F-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊙F-func {zero} {one} {half} {forth} p₁ p₂ = triv
⊙F-func {zero} {one} {half} {half} p₁ p₂ = triv
⊙F-func {zero} {one} {half} {one} p₁ p₂ = triv
⊙F-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊙F-func {zero} {one} {one} {forth} p₁ p₂ = triv
⊙F-func {zero} {one} {one} {half} p₁ p₂ = triv
⊙F-func {zero} {one} {one} {one} p₁ p₂ = triv
⊙F-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
⊙F-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
⊙F-func {forth} {zero} {zero} {half} p₁ p₂ = triv
⊙F-func {forth} {zero} {zero} {one} p₁ p₂ = triv
⊙F-func {forth} {zero} {forth} {zero} () ()
⊙F-func {forth} {zero} {forth} {forth} () p₂
⊙F-func {forth} {zero} {forth} {half} () p₂
⊙F-func {forth} {zero} {forth} {one} () p₂
⊙F-func {forth} {zero} {half} {zero} () ()
⊙F-func {forth} {zero} {half} {forth} () ()
⊙F-func {forth} {zero} {half} {half} () p₂
⊙F-func {forth} {zero} {half} {one} () p₂
⊙F-func {forth} {zero} {one} {zero} () ()
⊙F-func {forth} {zero} {one} {forth} () ()
⊙F-func {forth} {zero} {one} {half} () ()
⊙F-func {forth} {zero} {one} {one} () p₂
⊙F-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
⊙F-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
⊙F-func {forth} {forth} {zero} {half} p₁ p₂ = triv
⊙F-func {forth} {forth} {zero} {one} p₁ p₂ = triv
⊙F-func {forth} {forth} {forth} {zero} p₁ ()
⊙F-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
⊙F-func {forth} {forth} {forth} {half} p₁ p₂ = triv
⊙F-func {forth} {forth} {forth} {one} p₁ p₂ = triv
⊙F-func {forth} {forth} {half} {zero} p₁ ()
⊙F-func {forth} {forth} {half} {forth} p₁ p₂ = triv
⊙F-func {forth} {forth} {half} {half} p₁ p₂ = triv
⊙F-func {forth} {forth} {half} {one} p₁ p₂ = triv
⊙F-func {forth} {forth} {one} {zero} p₁ ()
⊙F-func {forth} {forth} {one} {forth} p₁ p₂ = triv
⊙F-func {forth} {forth} {one} {half} p₁ p₂ = triv
⊙F-func {forth} {forth} {one} {one} p₁ p₂ = triv
⊙F-func {forth} {half} {zero} {zero} p₁ p₂ = triv
⊙F-func {forth} {half} {zero} {forth} p₁ p₂ = triv
⊙F-func {forth} {half} {zero} {half} p₁ p₂ = triv
⊙F-func {forth} {half} {zero} {one} p₁ p₂ = triv
⊙F-func {forth} {half} {forth} {zero} p₁ ()
⊙F-func {forth} {half} {forth} {forth} p₁ p₂ = triv
⊙F-func {forth} {half} {forth} {half} p₁ p₂ = triv
⊙F-func {forth} {half} {forth} {one} p₁ p₂ = triv
⊙F-func {forth} {half} {half} {zero} p₁ ()
⊙F-func {forth} {half} {half} {forth} p₁ p₂ = triv
⊙F-func {forth} {half} {half} {half} p₁ p₂ = triv
⊙F-func {forth} {half} {half} {one} p₁ p₂ = triv
⊙F-func {forth} {half} {one} {zero} p₁ ()
⊙F-func {forth} {half} {one} {forth} p₁ p₂ = triv
⊙F-func {forth} {half} {one} {half} p₁ p₂ = triv
⊙F-func {forth} {half} {one} {one} p₁ p₂ = triv
⊙F-func {forth} {one} {zero} {zero} p₁ p₂ = triv
⊙F-func {forth} {one} {zero} {forth} p₁ p₂ = triv
⊙F-func {forth} {one} {zero} {half} p₁ p₂ = triv
⊙F-func {forth} {one} {zero} {one} p₁ p₂ = triv
⊙F-func {forth} {one} {forth} {zero} p₁ ()
⊙F-func {forth} {one} {forth} {forth} p₁ p₂ = triv
⊙F-func {forth} {one} {forth} {half} p₁ p₂ = triv
⊙F-func {forth} {one} {forth} {one} p₁ p₂ = triv
⊙F-func {forth} {one} {half} {zero} p₁ ()
⊙F-func {forth} {one} {half} {forth} p₁ p₂ = triv
⊙F-func {forth} {one} {half} {half} p₁ p₂ = triv
⊙F-func {forth} {one} {half} {one} p₁ p₂ = triv
⊙F-func {forth} {one} {one} {zero} p₁ ()
⊙F-func {forth} {one} {one} {forth} p₁ p₂ = triv
⊙F-func {forth} {one} {one} {half} p₁ p₂ = triv
⊙F-func {forth} {one} {one} {one} p₁ p₂ = triv
⊙F-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊙F-func {half} {zero} {zero} {forth} p₁ p₂ = triv
⊙F-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊙F-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊙F-func {half} {zero} {forth} {zero} () ()
⊙F-func {half} {zero} {forth} {forth} () p₂
⊙F-func {half} {zero} {forth} {half} () p₂
⊙F-func {half} {zero} {forth} {one} () p₂
⊙F-func {half} {zero} {half} {zero} () ()
⊙F-func {half} {zero} {half} {forth} () ()
⊙F-func {half} {zero} {half} {half} () p₂
⊙F-func {half} {zero} {half} {one} () p₂
⊙F-func {half} {zero} {one} {zero} () ()
⊙F-func {half} {zero} {one} {forth} () ()
⊙F-func {half} {zero} {one} {half} () ()
⊙F-func {half} {zero} {one} {one} () p₂
⊙F-func {half} {forth} {zero} {zero} p₁ p₂ = triv
⊙F-func {half} {forth} {zero} {forth} p₁ p₂ = triv
⊙F-func {half} {forth} {zero} {half} p₁ p₂ = triv
⊙F-func {half} {forth} {zero} {one} p₁ p₂ = triv
⊙F-func {half} {forth} {forth} {zero} () ()
⊙F-func {half} {forth} {forth} {forth} p₁ p₂ = triv
⊙F-func {half} {forth} {forth} {half} p₁ p₂ = triv
⊙F-func {half} {forth} {forth} {one} p₁ p₂ = triv
⊙F-func {half} {forth} {half} {zero} () ()
⊙F-func {half} {forth} {half} {forth} p₁ p₂ = triv
⊙F-func {half} {forth} {half} {half} p₁ p₂ = triv
⊙F-func {half} {forth} {half} {one} p₁ p₂ = triv
⊙F-func {half} {forth} {one} {zero} () ()
⊙F-func {half} {forth} {one} {forth} () ()
⊙F-func {half} {forth} {one} {half} () ()
⊙F-func {half} {forth} {one} {one} () p₂
⊙F-func {half} {half} {zero} {zero} p₁ p₂ = triv
⊙F-func {half} {half} {zero} {forth} p₁ p₂ = triv
⊙F-func {half} {half} {zero} {half} p₁ p₂ = triv
⊙F-func {half} {half} {zero} {one} p₁ p₂ = triv
⊙F-func {half} {half} {forth} {zero} p₁ ()
⊙F-func {half} {half} {forth} {forth} p₁ p₂ = triv
⊙F-func {half} {half} {forth} {half} p₁ p₂ = triv
⊙F-func {half} {half} {forth} {one} p₁ p₂ = triv
⊙F-func {half} {half} {half} {zero} p₁ ()
⊙F-func {half} {half} {half} {forth} p₁ p₂ = triv
⊙F-func {half} {half} {half} {half} p₁ p₂ = triv
⊙F-func {half} {half} {half} {one} p₁ p₂ = triv
⊙F-func {half} {half} {one} {zero} p₁ ()
⊙F-func {half} {half} {one} {forth} p₁ ()
⊙F-func {half} {half} {one} {half} p₁ ()
⊙F-func {half} {half} {one} {one} p₁ p₂ = triv
⊙F-func {half} {one} {zero} {zero} p₁ p₂ = triv
⊙F-func {half} {one} {zero} {forth} p₁ p₂ = triv
⊙F-func {half} {one} {zero} {half} p₁ p₂ = triv
⊙F-func {half} {one} {zero} {one} p₁ p₂ = triv
⊙F-func {half} {one} {forth} {zero} p₁ ()
⊙F-func {half} {one} {forth} {forth} p₁ p₂ = triv
⊙F-func {half} {one} {forth} {half} p₁ p₂ = triv
⊙F-func {half} {one} {forth} {one} p₁ p₂ = triv
⊙F-func {half} {one} {half} {zero} p₁ ()
⊙F-func {half} {one} {half} {forth} p₁ p₂ = triv
⊙F-func {half} {one} {half} {half} p₁ p₂ = triv
⊙F-func {half} {one} {half} {one} p₁ p₂ = triv
⊙F-func {half} {one} {one} {zero} p₁ ()
⊙F-func {half} {one} {one} {forth} p₁ ()
⊙F-func {half} {one} {one} {half} p₁ p₂ = triv
⊙F-func {half} {one} {one} {one} p₁ p₂ = triv
⊙F-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊙F-func {one} {zero} {zero} {forth} p₁ p₂ = triv
⊙F-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊙F-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊙F-func {one} {zero} {forth} {zero} () ()
⊙F-func {one} {zero} {forth} {forth} () p₂
⊙F-func {one} {zero} {forth} {half} () p₂
⊙F-func {one} {zero} {forth} {one} () p₂
⊙F-func {one} {zero} {half} {zero} () ()
⊙F-func {one} {zero} {half} {forth} () ()
⊙F-func {one} {zero} {half} {half} () p₂
⊙F-func {one} {zero} {half} {one} () p₂
⊙F-func {one} {zero} {one} {zero} () ()
⊙F-func {one} {zero} {one} {forth} () ()
⊙F-func {one} {zero} {one} {half} () ()
⊙F-func {one} {zero} {one} {one} () p₂
⊙F-func {one} {forth} {zero} {zero} p₁ p₂ = triv
⊙F-func {one} {forth} {zero} {forth} p₁ p₂ = triv
⊙F-func {one} {forth} {zero} {half} p₁ p₂ = triv
⊙F-func {one} {forth} {zero} {one} p₁ p₂ = triv
⊙F-func {one} {forth} {forth} {zero} () ()
⊙F-func {one} {forth} {forth} {forth} p₁ p₂ = triv
⊙F-func {one} {forth} {forth} {half} p₁ p₂ = triv
⊙F-func {one} {forth} {forth} {one} p₁ p₂ = triv
⊙F-func {one} {forth} {half} {zero} () ()
⊙F-func {one} {forth} {half} {forth} () ()
⊙F-func {one} {forth} {half} {half} () p₂
⊙F-func {one} {forth} {half} {one} () p₂
⊙F-func {one} {forth} {one} {zero} () ()
⊙F-func {one} {forth} {one} {forth} () ()
⊙F-func {one} {forth} {one} {half} () ()
⊙F-func {one} {forth} {one} {one} () p₂
⊙F-func {one} {half} {zero} {zero} p₁ p₂ = triv
⊙F-func {one} {half} {zero} {forth} p₁ p₂ = triv
⊙F-func {one} {half} {zero} {half} p₁ p₂ = triv
⊙F-func {one} {half} {zero} {one} p₁ p₂ = triv
⊙F-func {one} {half} {forth} {zero} () ()
⊙F-func {one} {half} {forth} {forth} p₁ p₂ = triv
⊙F-func {one} {half} {forth} {half} () p₂
⊙F-func {one} {half} {forth} {one} p₁ p₂ = triv
⊙F-func {one} {half} {half} {zero} () ()
⊙F-func {one} {half} {half} {forth} () ()
⊙F-func {one} {half} {half} {half} () p₂
⊙F-func {one} {half} {half} {one} p₁ p₂ = triv
⊙F-func {one} {half} {one} {zero} () ()
⊙F-func {one} {half} {one} {forth} () ()
⊙F-func {one} {half} {one} {half} () ()
⊙F-func {one} {half} {one} {one} () p₂
⊙F-func {one} {one} {zero} {zero} p₁ p₂ = triv
⊙F-func {one} {one} {zero} {forth} p₁ p₂ = triv
⊙F-func {one} {one} {zero} {half} p₁ p₂ = triv
⊙F-func {one} {one} {zero} {one} p₁ p₂ = triv
⊙F-func {one} {one} {forth} {zero} p₁ ()
⊙F-func {one} {one} {forth} {forth} p₁ p₂ = triv
⊙F-func {one} {one} {forth} {half} p₁ p₂ = triv
⊙F-func {one} {one} {forth} {one} p₁ p₂ = triv
⊙F-func {one} {one} {half} {zero} p₁ ()
⊙F-func {one} {one} {half} {forth} p₁ ()
⊙F-func {one} {one} {half} {half} p₁ p₂ = triv
⊙F-func {one} {one} {half} {one} p₁ p₂ = triv
⊙F-func {one} {one} {one} {zero} p₁ ()
⊙F-func {one} {one} {one} {forth} p₁ ()
⊙F-func {one} {one} {one} {half} p₁ ()
⊙F-func {one} {one} {one} {one} p₁ p₂ = triv

⊙F-distl : {a b c : Four} → (a ⊙F (b ⊔F c)) ≡ ((a ⊙F b) ⊔F (a ⊙F c))
⊙F-distl {zero} {zero} {zero} = refl
⊙F-distl {zero} {zero} {forth} = refl
⊙F-distl {zero} {zero} {half} = refl
⊙F-distl {zero} {zero} {one} = refl
⊙F-distl {zero} {forth} {zero} = refl
⊙F-distl {zero} {forth} {forth} = refl
⊙F-distl {zero} {forth} {half} = refl
⊙F-distl {zero} {forth} {one} = refl
⊙F-distl {zero} {half} {zero} = refl
⊙F-distl {zero} {half} {forth} = refl
⊙F-distl {zero} {half} {half} = refl
⊙F-distl {zero} {half} {one} = refl
⊙F-distl {zero} {one} {zero} = refl
⊙F-distl {zero} {one} {forth} = refl
⊙F-distl {zero} {one} {half} = refl
⊙F-distl {zero} {one} {one} = refl
⊙F-distl {forth} {zero} {zero} = refl
⊙F-distl {forth} {zero} {forth} = refl
⊙F-distl {forth} {zero} {half} = refl
⊙F-distl {forth} {zero} {one} = refl
⊙F-distl {forth} {forth} {zero} = refl
⊙F-distl {forth} {forth} {forth} = refl
⊙F-distl {forth} {forth} {half} = refl
⊙F-distl {forth} {forth} {one} = refl
⊙F-distl {forth} {half} {zero} = refl
⊙F-distl {forth} {half} {forth} = refl
⊙F-distl {forth} {half} {half} = refl
⊙F-distl {forth} {half} {one} = refl
⊙F-distl {forth} {one} {zero} = refl
⊙F-distl {forth} {one} {forth} = refl
⊙F-distl {forth} {one} {half} = refl
⊙F-distl {forth} {one} {one} = refl
⊙F-distl {half} {zero} {zero} = refl
⊙F-distl {half} {zero} {forth} = refl
⊙F-distl {half} {zero} {half} = refl
⊙F-distl {half} {zero} {one} = refl
⊙F-distl {half} {forth} {zero} = refl
⊙F-distl {half} {forth} {forth} = refl
⊙F-distl {half} {forth} {half} = refl
⊙F-distl {half} {forth} {one} = refl
⊙F-distl {half} {half} {zero} = refl
⊙F-distl {half} {half} {forth} = refl
⊙F-distl {half} {half} {half} = refl
⊙F-distl {half} {half} {one} = refl
⊙F-distl {half} {one} {zero} = refl
⊙F-distl {half} {one} {forth} = refl
⊙F-distl {half} {one} {half} = refl
⊙F-distl {half} {one} {one} = refl
⊙F-distl {one} {zero} {zero} = refl
⊙F-distl {one} {zero} {forth} = refl
⊙F-distl {one} {zero} {half} = refl
⊙F-distl {one} {zero} {one} = refl
⊙F-distl {one} {forth} {zero} = refl
⊙F-distl {one} {forth} {forth} = refl
⊙F-distl {one} {forth} {half} = refl
⊙F-distl {one} {forth} {one} = refl
⊙F-distl {one} {half} {zero} = refl
⊙F-distl {one} {half} {forth} = refl
⊙F-distl {one} {half} {half} = refl
⊙F-distl {one} {half} {one} = refl
⊙F-distl {one} {one} {zero} = refl
⊙F-distl {one} {one} {forth} = refl
⊙F-distl {one} {one} {half} = refl
⊙F-distl {one} {one} {one} = refl

⊙F-distr : {a b c : Four} → ((a ⊔F b) ⊙F c) ≡ ((a ⊙F c) ⊔F (b ⊙F c))
⊙F-distr {zero} {zero} {zero} = refl
⊙F-distr {zero} {zero} {forth} = refl
⊙F-distr {zero} {zero} {half} = refl
⊙F-distr {zero} {zero} {one} = refl
⊙F-distr {zero} {forth} {zero} = refl
⊙F-distr {zero} {forth} {forth} = refl
⊙F-distr {zero} {forth} {half} = refl
⊙F-distr {zero} {forth} {one} = refl
⊙F-distr {zero} {half} {zero} = refl
⊙F-distr {zero} {half} {forth} = refl
⊙F-distr {zero} {half} {half} = refl
⊙F-distr {zero} {half} {one} = refl
⊙F-distr {zero} {one} {zero} = refl
⊙F-distr {zero} {one} {forth} = refl
⊙F-distr {zero} {one} {half} = refl
⊙F-distr {zero} {one} {one} = refl
⊙F-distr {forth} {zero} {zero} = refl
⊙F-distr {forth} {zero} {forth} = refl
⊙F-distr {forth} {zero} {half} = refl
⊙F-distr {forth} {zero} {one} = refl
⊙F-distr {forth} {forth} {zero} = refl
⊙F-distr {forth} {forth} {forth} = refl
⊙F-distr {forth} {forth} {half} = refl
⊙F-distr {forth} {forth} {one} = refl
⊙F-distr {forth} {half} {zero} = refl
⊙F-distr {forth} {half} {forth} = refl
⊙F-distr {forth} {half} {half} = refl
⊙F-distr {forth} {half} {one} = refl
⊙F-distr {forth} {one} {zero} = refl
⊙F-distr {forth} {one} {forth} = refl
⊙F-distr {forth} {one} {half} = refl
⊙F-distr {forth} {one} {one} = refl
⊙F-distr {half} {zero} {zero} = refl
⊙F-distr {half} {zero} {forth} = refl
⊙F-distr {half} {zero} {half} = refl
⊙F-distr {half} {zero} {one} = refl
⊙F-distr {half} {forth} {zero} = refl
⊙F-distr {half} {forth} {forth} = refl
⊙F-distr {half} {forth} {half} = refl
⊙F-distr {half} {forth} {one} = refl
⊙F-distr {half} {half} {zero} = refl
⊙F-distr {half} {half} {forth} = refl
⊙F-distr {half} {half} {half} = refl
⊙F-distr {half} {half} {one} = refl
⊙F-distr {half} {one} {zero} = refl
⊙F-distr {half} {one} {forth} = refl
⊙F-distr {half} {one} {half} = refl
⊙F-distr {half} {one} {one} = refl
⊙F-distr {one} {zero} {zero} = refl
⊙F-distr {one} {zero} {forth} = refl
⊙F-distr {one} {zero} {half} = refl
⊙F-distr {one} {zero} {one} = refl
⊙F-distr {one} {forth} {zero} = refl
⊙F-distr {one} {forth} {forth} = refl
⊙F-distr {one} {forth} {half} = refl
⊙F-distr {one} {forth} {one} = refl
⊙F-distr {one} {half} {zero} = refl
⊙F-distr {one} {half} {forth} = refl
⊙F-distr {one} {half} {half} = refl
⊙F-distr {one} {half} {one} = refl
⊙F-distr {one} {one} {zero} = refl
⊙F-distr {one} {one} {forth} = refl
⊙F-distr {one} {one} {half} = refl
⊙F-distr {one} {one} {one} = refl

▷F-sym : (∀{a b} → (a ▷F b) ≡ (b ▷F a)) → ⊥ {lzero}
▷F-sym p with p {forth}{one}
... | () 

-- ▷F-contract : (∀{a} → (a ▷F a) ≡ a) → ⊥ {lzero}
-- ▷F-contract p with p {half}
-- ... | () 

▷F-zerol : ∀{x} → (zero ▷F x) ≤₄ zero
▷F-zerol {zero} = triv
▷F-zerol {forth} = triv
▷F-zerol {half} = triv
▷F-zerol {one} = triv

▷F-zeror : ∀{x} → (x ▷F zero) ≤₄ zero
▷F-zeror {zero} = triv
▷F-zeror {forth} = triv
▷F-zeror {half} = triv
▷F-zeror {one} = triv

▷F-assoc : {a b c : Four} →  a ▷F (b ▷F c) ≡ (a ▷F b) ▷F c
▷F-assoc {zero} {zero} {zero} = refl
▷F-assoc {zero} {zero} {forth} = refl
▷F-assoc {zero} {zero} {half} = refl
▷F-assoc {zero} {zero} {one} = refl
▷F-assoc {zero} {forth} {zero} = refl
▷F-assoc {zero} {forth} {forth} = refl
▷F-assoc {zero} {forth} {half} = refl
▷F-assoc {zero} {forth} {one} = refl
▷F-assoc {zero} {half} {zero} = refl
▷F-assoc {zero} {half} {forth} = refl
▷F-assoc {zero} {half} {half} = refl
▷F-assoc {zero} {half} {one} = refl
▷F-assoc {zero} {one} {zero} = refl
▷F-assoc {zero} {one} {forth} = refl
▷F-assoc {zero} {one} {half} = refl
▷F-assoc {zero} {one} {one} = refl
▷F-assoc {forth} {zero} {zero} = refl
▷F-assoc {forth} {zero} {forth} = refl
▷F-assoc {forth} {zero} {half} = refl
▷F-assoc {forth} {zero} {one} = refl
▷F-assoc {forth} {forth} {zero} = refl
▷F-assoc {forth} {forth} {forth} = refl
▷F-assoc {forth} {forth} {half} = refl
▷F-assoc {forth} {forth} {one} = refl
▷F-assoc {forth} {half} {zero} = refl
▷F-assoc {forth} {half} {forth} = refl
▷F-assoc {forth} {half} {half} = refl
▷F-assoc {forth} {half} {one} = refl
▷F-assoc {forth} {one} {zero} = refl
▷F-assoc {forth} {one} {forth} = refl
▷F-assoc {forth} {one} {half} = refl
▷F-assoc {forth} {one} {one} = refl
▷F-assoc {half} {zero} {zero} = refl
▷F-assoc {half} {zero} {forth} = refl
▷F-assoc {half} {zero} {half} = refl
▷F-assoc {half} {zero} {one} = refl
▷F-assoc {half} {forth} {zero} = refl
▷F-assoc {half} {forth} {forth} = refl
▷F-assoc {half} {forth} {half} = refl
▷F-assoc {half} {forth} {one} = refl
▷F-assoc {half} {half} {zero} = refl
▷F-assoc {half} {half} {forth} = refl
▷F-assoc {half} {half} {half} = refl
▷F-assoc {half} {half} {one} = refl
▷F-assoc {half} {one} {zero} = refl
▷F-assoc {half} {one} {forth} = refl
▷F-assoc {half} {one} {half} = refl
▷F-assoc {half} {one} {one} = refl
▷F-assoc {one} {zero} {zero} = refl
▷F-assoc {one} {zero} {forth} = refl
▷F-assoc {one} {zero} {half} = refl
▷F-assoc {one} {zero} {one} = refl
▷F-assoc {one} {forth} {zero} = refl
▷F-assoc {one} {forth} {forth} = refl
▷F-assoc {one} {forth} {half} = refl
▷F-assoc {one} {forth} {one} = refl
▷F-assoc {one} {half} {zero} = refl
▷F-assoc {one} {half} {forth} = refl
▷F-assoc {one} {half} {half} = refl
▷F-assoc {one} {half} {one} = refl
▷F-assoc {one} {one} {zero} = refl
▷F-assoc {one} {one} {forth} = refl
▷F-assoc {one} {one} {half} = refl
▷F-assoc {one} {one} {one} = refl

▷F-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ▷F b) ≤₄ (c ▷F d)
▷F-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
▷F-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
▷F-func {zero} {zero} {zero} {half} p₁ p₂ = triv
▷F-func {zero} {zero} {zero} {one} p₁ p₂ = triv
▷F-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
▷F-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
▷F-func {zero} {zero} {forth} {half} p₁ p₂ = triv
▷F-func {zero} {zero} {forth} {one} p₁ p₂ = triv
▷F-func {zero} {zero} {half} {zero} p₁ p₂ = triv
▷F-func {zero} {zero} {half} {forth} p₁ p₂ = triv
▷F-func {zero} {zero} {half} {half} p₁ p₂ = triv
▷F-func {zero} {zero} {half} {one} p₁ p₂ = triv
▷F-func {zero} {zero} {one} {zero} p₁ p₂ = triv
▷F-func {zero} {zero} {one} {forth} p₁ p₂ = triv
▷F-func {zero} {zero} {one} {half} p₁ p₂ = triv
▷F-func {zero} {zero} {one} {one} p₁ p₂ = triv
▷F-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
▷F-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
▷F-func {zero} {forth} {zero} {half} p₁ p₂ = triv
▷F-func {zero} {forth} {zero} {one} p₁ p₂ = triv
▷F-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
▷F-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
▷F-func {zero} {forth} {forth} {half} p₁ p₂ = triv
▷F-func {zero} {forth} {forth} {one} p₁ p₂ = triv
▷F-func {zero} {forth} {half} {zero} p₁ p₂ = triv
▷F-func {zero} {forth} {half} {forth} p₁ p₂ = triv
▷F-func {zero} {forth} {half} {half} p₁ p₂ = triv
▷F-func {zero} {forth} {half} {one} p₁ p₂ = triv
▷F-func {zero} {forth} {one} {zero} p₁ p₂ = triv
▷F-func {zero} {forth} {one} {forth} p₁ p₂ = triv
▷F-func {zero} {forth} {one} {half} p₁ p₂ = triv
▷F-func {zero} {forth} {one} {one} p₁ p₂ = triv
▷F-func {zero} {half} {zero} {zero} p₁ p₂ = triv
▷F-func {zero} {half} {zero} {forth} p₁ p₂ = triv
▷F-func {zero} {half} {zero} {half} p₁ p₂ = triv
▷F-func {zero} {half} {zero} {one} p₁ p₂ = triv
▷F-func {zero} {half} {forth} {zero} p₁ p₂ = triv
▷F-func {zero} {half} {forth} {forth} p₁ p₂ = triv
▷F-func {zero} {half} {forth} {half} p₁ p₂ = triv
▷F-func {zero} {half} {forth} {one} p₁ p₂ = triv
▷F-func {zero} {half} {half} {zero} p₁ p₂ = triv
▷F-func {zero} {half} {half} {forth} p₁ p₂ = triv
▷F-func {zero} {half} {half} {half} p₁ p₂ = triv
▷F-func {zero} {half} {half} {one} p₁ p₂ = triv
▷F-func {zero} {half} {one} {zero} p₁ p₂ = triv
▷F-func {zero} {half} {one} {forth} p₁ p₂ = triv
▷F-func {zero} {half} {one} {half} p₁ p₂ = triv
▷F-func {zero} {half} {one} {one} p₁ p₂ = triv
▷F-func {zero} {one} {zero} {zero} p₁ p₂ = triv
▷F-func {zero} {one} {zero} {forth} p₁ p₂ = triv
▷F-func {zero} {one} {zero} {half} p₁ p₂ = triv
▷F-func {zero} {one} {zero} {one} p₁ p₂ = triv
▷F-func {zero} {one} {forth} {zero} p₁ p₂ = triv
▷F-func {zero} {one} {forth} {forth} p₁ p₂ = triv
▷F-func {zero} {one} {forth} {half} p₁ p₂ = triv
▷F-func {zero} {one} {forth} {one} p₁ p₂ = triv
▷F-func {zero} {one} {half} {zero} p₁ p₂ = triv
▷F-func {zero} {one} {half} {forth} p₁ p₂ = triv
▷F-func {zero} {one} {half} {half} p₁ p₂ = triv
▷F-func {zero} {one} {half} {one} p₁ p₂ = triv
▷F-func {zero} {one} {one} {zero} p₁ p₂ = triv
▷F-func {zero} {one} {one} {forth} p₁ p₂ = triv
▷F-func {zero} {one} {one} {half} p₁ p₂ = triv
▷F-func {zero} {one} {one} {one} p₁ p₂ = triv
▷F-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
▷F-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
▷F-func {forth} {zero} {zero} {half} p₁ p₂ = triv
▷F-func {forth} {zero} {zero} {one} p₁ p₂ = triv
▷F-func {forth} {zero} {forth} {zero} () ()
▷F-func {forth} {zero} {forth} {forth} () p₂
▷F-func {forth} {zero} {forth} {half} () p₂
▷F-func {forth} {zero} {forth} {one} () p₂
▷F-func {forth} {zero} {half} {zero} () ()
▷F-func {forth} {zero} {half} {forth} () ()
▷F-func {forth} {zero} {half} {half} () p₂
▷F-func {forth} {zero} {half} {one} () p₂
▷F-func {forth} {zero} {one} {zero} () ()
▷F-func {forth} {zero} {one} {forth} () ()
▷F-func {forth} {zero} {one} {half} () ()
▷F-func {forth} {zero} {one} {one} () p₂
▷F-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
▷F-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
▷F-func {forth} {forth} {zero} {half} p₁ p₂ = triv
▷F-func {forth} {forth} {zero} {one} p₁ p₂ = triv
▷F-func {forth} {forth} {forth} {zero} p₁ ()
▷F-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
▷F-func {forth} {forth} {forth} {half} p₁ p₂ = triv
▷F-func {forth} {forth} {forth} {one} p₁ p₂ = triv
▷F-func {forth} {forth} {half} {zero} p₁ ()
▷F-func {forth} {forth} {half} {forth} p₁ ()
▷F-func {forth} {forth} {half} {half} p₁ p₂ = triv
▷F-func {forth} {forth} {half} {one} p₁ p₂ = triv
▷F-func {forth} {forth} {one} {zero} p₁ ()
▷F-func {forth} {forth} {one} {forth} p₁ ()
▷F-func {forth} {forth} {one} {half} p₁ p₂ = triv
▷F-func {forth} {forth} {one} {one} p₁ p₂ = triv
▷F-func {forth} {half} {zero} {zero} p₁ p₂ = triv
▷F-func {forth} {half} {zero} {forth} p₁ p₂ = triv
▷F-func {forth} {half} {zero} {half} p₁ p₂ = triv
▷F-func {forth} {half} {zero} {one} p₁ p₂ = triv
▷F-func {forth} {half} {forth} {zero} p₁ ()
▷F-func {forth} {half} {forth} {forth} p₁ p₂ = triv
▷F-func {forth} {half} {forth} {half} p₁ p₂ = triv
▷F-func {forth} {half} {forth} {one} p₁ p₂ = triv
▷F-func {forth} {half} {half} {zero} p₁ ()
▷F-func {forth} {half} {half} {forth} p₁ p₂ = triv
▷F-func {forth} {half} {half} {half} p₁ p₂ = triv
▷F-func {forth} {half} {half} {one} p₁ p₂ = triv
▷F-func {forth} {half} {one} {zero} p₁ ()
▷F-func {forth} {half} {one} {forth} p₁ p₂ = triv
▷F-func {forth} {half} {one} {half} p₁ p₂ = triv
▷F-func {forth} {half} {one} {one} p₁ p₂ = triv
▷F-func {forth} {one} {zero} {zero} p₁ p₂ = triv
▷F-func {forth} {one} {zero} {forth} p₁ p₂ = triv
▷F-func {forth} {one} {zero} {half} p₁ p₂ = triv
▷F-func {forth} {one} {zero} {one} p₁ p₂ = triv
▷F-func {forth} {one} {forth} {zero} p₁ ()
▷F-func {forth} {one} {forth} {forth} p₁ p₂ = triv
▷F-func {forth} {one} {forth} {half} p₁ p₂ = triv
▷F-func {forth} {one} {forth} {one} p₁ p₂ = triv
▷F-func {forth} {one} {half} {zero} p₁ ()
▷F-func {forth} {one} {half} {forth} p₁ p₂ = triv
▷F-func {forth} {one} {half} {half} p₁ p₂ = triv
▷F-func {forth} {one} {half} {one} p₁ p₂ = triv
▷F-func {forth} {one} {one} {zero} p₁ ()
▷F-func {forth} {one} {one} {forth} p₁ p₂ = triv
▷F-func {forth} {one} {one} {half} p₁ p₂ = triv
▷F-func {forth} {one} {one} {one} p₁ p₂ = triv
▷F-func {half} {zero} {zero} {zero} p₁ p₂ = triv
▷F-func {half} {zero} {zero} {forth} p₁ p₂ = triv
▷F-func {half} {zero} {zero} {half} p₁ p₂ = triv
▷F-func {half} {zero} {zero} {one} p₁ p₂ = triv
▷F-func {half} {zero} {forth} {zero} () ()
▷F-func {half} {zero} {forth} {forth} () p₂
▷F-func {half} {zero} {forth} {half} () p₂
▷F-func {half} {zero} {forth} {one} () p₂
▷F-func {half} {zero} {half} {zero} () ()
▷F-func {half} {zero} {half} {forth} () ()
▷F-func {half} {zero} {half} {half} () p₂
▷F-func {half} {zero} {half} {one} () p₂
▷F-func {half} {zero} {one} {zero} () ()
▷F-func {half} {zero} {one} {forth} () ()
▷F-func {half} {zero} {one} {half} () ()
▷F-func {half} {zero} {one} {one} () p₂
▷F-func {half} {forth} {zero} {zero} p₁ p₂ = triv
▷F-func {half} {forth} {zero} {forth} p₁ p₂ = triv
▷F-func {half} {forth} {zero} {half} p₁ p₂ = triv
▷F-func {half} {forth} {zero} {one} p₁ p₂ = triv
▷F-func {half} {forth} {forth} {zero} () ()
▷F-func {half} {forth} {forth} {forth} () p₂
▷F-func {half} {forth} {forth} {half} () p₂
▷F-func {half} {forth} {forth} {one} () p₂
▷F-func {half} {forth} {half} {zero} () ()
▷F-func {half} {forth} {half} {forth} () ()
▷F-func {half} {forth} {half} {half} () p₂
▷F-func {half} {forth} {half} {one} () p₂
▷F-func {half} {forth} {one} {zero} () ()
▷F-func {half} {forth} {one} {forth} () ()
▷F-func {half} {forth} {one} {half} () ()
▷F-func {half} {forth} {one} {one} () p₂
▷F-func {half} {half} {zero} {zero} p₁ p₂ = triv
▷F-func {half} {half} {zero} {forth} p₁ p₂ = triv
▷F-func {half} {half} {zero} {half} p₁ p₂ = triv
▷F-func {half} {half} {zero} {one} p₁ p₂ = triv
▷F-func {half} {half} {forth} {zero} p₁ ()
▷F-func {half} {half} {forth} {forth} p₁ p₂ = triv
▷F-func {half} {half} {forth} {half} p₁ p₂ = triv
▷F-func {half} {half} {forth} {one} p₁ p₂ = triv
▷F-func {half} {half} {half} {zero} p₁ ()
▷F-func {half} {half} {half} {forth} p₁ p₂ = triv
▷F-func {half} {half} {half} {half} p₁ p₂ = triv
▷F-func {half} {half} {half} {one} p₁ p₂ = triv
▷F-func {half} {half} {one} {zero} p₁ ()
▷F-func {half} {half} {one} {forth} p₁ p₂ = triv
▷F-func {half} {half} {one} {half} p₁ p₂ = triv
▷F-func {half} {half} {one} {one} p₁ p₂ = triv
▷F-func {half} {one} {zero} {zero} p₁ p₂ = triv
▷F-func {half} {one} {zero} {forth} p₁ p₂ = triv
▷F-func {half} {one} {zero} {half} p₁ p₂ = triv
▷F-func {half} {one} {zero} {one} p₁ p₂ = triv
▷F-func {half} {one} {forth} {zero} p₁ ()
▷F-func {half} {one} {forth} {forth} p₁ p₂ = triv
▷F-func {half} {one} {forth} {half} p₁ p₂ = triv
▷F-func {half} {one} {forth} {one} p₁ p₂ = triv
▷F-func {half} {one} {half} {zero} p₁ ()
▷F-func {half} {one} {half} {forth} p₁ p₂ = triv
▷F-func {half} {one} {half} {half} p₁ p₂ = triv
▷F-func {half} {one} {half} {one} p₁ p₂ = triv
▷F-func {half} {one} {one} {zero} p₁ ()
▷F-func {half} {one} {one} {forth} p₁ p₂ = triv
▷F-func {half} {one} {one} {half} p₁ p₂ = triv
▷F-func {half} {one} {one} {one} p₁ p₂ = triv
▷F-func {one} {zero} {zero} {zero} p₁ p₂ = triv
▷F-func {one} {zero} {zero} {forth} p₁ p₂ = triv
▷F-func {one} {zero} {zero} {half} p₁ p₂ = triv
▷F-func {one} {zero} {zero} {one} p₁ p₂ = triv
▷F-func {one} {zero} {forth} {zero} p₁ ()
▷F-func {one} {zero} {forth} {forth} () p₂
▷F-func {one} {zero} {forth} {half} () p₂
▷F-func {one} {zero} {forth} {one} () p₂
▷F-func {one} {zero} {half} {zero} () ()
▷F-func {one} {zero} {half} {forth} () ()
▷F-func {one} {zero} {half} {half} () p₂
▷F-func {one} {zero} {half} {one} () p₂
▷F-func {one} {zero} {one} {zero} () ()
▷F-func {one} {zero} {one} {forth} () ()
▷F-func {one} {zero} {one} {half} () ()
▷F-func {one} {zero} {one} {one} () p₂
▷F-func {one} {forth} {zero} {zero} p₁ p₂ = triv
▷F-func {one} {forth} {zero} {forth} p₁ p₂ = triv
▷F-func {one} {forth} {zero} {half} p₁ p₂ = triv
▷F-func {one} {forth} {zero} {one} p₁ p₂ = triv
▷F-func {one} {forth} {forth} {zero} () ()
▷F-func {one} {forth} {forth} {forth} () p₂
▷F-func {one} {forth} {forth} {half} () p₂
▷F-func {one} {forth} {forth} {one} () p₂
▷F-func {one} {forth} {half} {zero} () ()
▷F-func {one} {forth} {half} {forth} () ()
▷F-func {one} {forth} {half} {half} () p₂
▷F-func {one} {forth} {half} {one} () p₂
▷F-func {one} {forth} {one} {zero} () ()
▷F-func {one} {forth} {one} {forth} () ()
▷F-func {one} {forth} {one} {half} () ()
▷F-func {one} {forth} {one} {one} () p₂
▷F-func {one} {half} {zero} {zero} p₁ p₂ = triv
▷F-func {one} {half} {zero} {forth} p₁ p₂ = triv
▷F-func {one} {half} {zero} {half} p₁ p₂ = triv
▷F-func {one} {half} {zero} {one} p₁ p₂ = triv
▷F-func {one} {half} {forth} {zero} () ()
▷F-func {one} {half} {forth} {forth} () p₂
▷F-func {one} {half} {forth} {half} () p₂
▷F-func {one} {half} {forth} {one} () p₂
▷F-func {one} {half} {half} {zero} () ()
▷F-func {one} {half} {half} {forth} p₁ p₂ = triv
▷F-func {one} {half} {half} {half} p₁ p₂ = triv
▷F-func {one} {half} {half} {one} p₁ p₂ = triv
▷F-func {one} {half} {one} {zero} () ()
▷F-func {one} {half} {one} {forth} p₁ p₂ = triv
▷F-func {one} {half} {one} {half} p₁ p₂ = triv
▷F-func {one} {half} {one} {one} p₁ p₂ = triv
▷F-func {one} {one} {zero} {zero} p₁ p₂ = triv
▷F-func {one} {one} {zero} {forth} p₁ p₂ = triv
▷F-func {one} {one} {zero} {half} p₁ p₂ = triv
▷F-func {one} {one} {zero} {one} p₁ p₂ = triv
▷F-func {one} {one} {forth} {zero} p₁ ()
▷F-func {one} {one} {forth} {forth} p₁ p₂ = triv
▷F-func {one} {one} {forth} {half} p₁ p₂ = triv
▷F-func {one} {one} {forth} {one} p₁ p₂ = triv
▷F-func {one} {one} {half} {zero} p₁ ()
▷F-func {one} {one} {half} {forth} p₁ p₂ = triv
▷F-func {one} {one} {half} {half} p₁ p₂ = triv
▷F-func {one} {one} {half} {one} p₁ p₂ = triv
▷F-func {one} {one} {one} {zero} p₁ ()
▷F-func {one} {one} {one} {forth} p₁ p₂ = triv
▷F-func {one} {one} {one} {half} p₁ p₂ = triv
▷F-func {one} {one} {one} {one} p₁ p₂ = triv

▷F-distl : {a b c : Four} → (a ▷F (b ⊔F c)) ≡ ((a ▷F b) ⊔F (a ▷F c))
▷F-distl {zero} {zero} {zero} = refl
▷F-distl {zero} {zero} {forth} = refl
▷F-distl {zero} {zero} {half} = refl
▷F-distl {zero} {zero} {one} = refl
▷F-distl {zero} {forth} {zero} = refl
▷F-distl {zero} {forth} {forth} = refl
▷F-distl {zero} {forth} {half} = refl
▷F-distl {zero} {forth} {one} = refl
▷F-distl {zero} {half} {zero} = refl
▷F-distl {zero} {half} {forth} = refl
▷F-distl {zero} {half} {half} = refl
▷F-distl {zero} {half} {one} = refl
▷F-distl {zero} {one} {zero} = refl
▷F-distl {zero} {one} {forth} = refl
▷F-distl {zero} {one} {half} = refl
▷F-distl {zero} {one} {one} = refl
▷F-distl {forth} {zero} {zero} = refl
▷F-distl {forth} {zero} {forth} = refl
▷F-distl {forth} {zero} {half} = refl
▷F-distl {forth} {zero} {one} = refl
▷F-distl {forth} {forth} {zero} = refl
▷F-distl {forth} {forth} {forth} = refl
▷F-distl {forth} {forth} {half} = refl
▷F-distl {forth} {forth} {one} = refl
▷F-distl {forth} {half} {zero} = refl
▷F-distl {forth} {half} {forth} = refl
▷F-distl {forth} {half} {half} = refl
▷F-distl {forth} {half} {one} = refl
▷F-distl {forth} {one} {zero} = refl
▷F-distl {forth} {one} {forth} = refl
▷F-distl {forth} {one} {half} = refl
▷F-distl {forth} {one} {one} = refl
▷F-distl {half} {zero} {zero} = refl
▷F-distl {half} {zero} {forth} = refl
▷F-distl {half} {zero} {half} = refl
▷F-distl {half} {zero} {one} = refl
▷F-distl {half} {forth} {zero} = refl
▷F-distl {half} {forth} {forth} = refl
▷F-distl {half} {forth} {half} = refl
▷F-distl {half} {forth} {one} = refl
▷F-distl {half} {half} {zero} = refl
▷F-distl {half} {half} {forth} = refl
▷F-distl {half} {half} {half} = refl
▷F-distl {half} {half} {one} = refl
▷F-distl {half} {one} {zero} = refl
▷F-distl {half} {one} {forth} = refl
▷F-distl {half} {one} {half} = refl
▷F-distl {half} {one} {one} = refl
▷F-distl {one} {zero} {zero} = refl
▷F-distl {one} {zero} {forth} = refl
▷F-distl {one} {zero} {half} = refl
▷F-distl {one} {zero} {one} = refl
▷F-distl {one} {forth} {zero} = refl
▷F-distl {one} {forth} {forth} = refl
▷F-distl {one} {forth} {half} = refl
▷F-distl {one} {forth} {one} = refl
▷F-distl {one} {half} {zero} = refl
▷F-distl {one} {half} {forth} = refl
▷F-distl {one} {half} {half} = refl
▷F-distl {one} {half} {one} = refl
▷F-distl {one} {one} {zero} = refl
▷F-distl {one} {one} {forth} = refl
▷F-distl {one} {one} {half} = refl
▷F-distl {one} {one} {one} = refl

▷F-distr : {a b c : Four} → ((a ⊔F b) ▷F c) ≡ ((a ▷F c) ⊔F (b ▷F c))
▷F-distr {zero} {zero} {zero} = refl
▷F-distr {zero} {zero} {forth} = refl
▷F-distr {zero} {zero} {half} = refl
▷F-distr {zero} {zero} {one} = refl
▷F-distr {zero} {forth} {zero} = refl
▷F-distr {zero} {forth} {forth} = refl
▷F-distr {zero} {forth} {half} = refl
▷F-distr {zero} {forth} {one} = refl
▷F-distr {zero} {half} {zero} = refl
▷F-distr {zero} {half} {forth} = refl
▷F-distr {zero} {half} {half} = refl
▷F-distr {zero} {half} {one} = refl
▷F-distr {zero} {one} {zero} = refl
▷F-distr {zero} {one} {forth} = refl
▷F-distr {zero} {one} {half} = refl
▷F-distr {zero} {one} {one} = refl
▷F-distr {forth} {zero} {zero} = refl
▷F-distr {forth} {zero} {forth} = refl
▷F-distr {forth} {zero} {half} = refl
▷F-distr {forth} {zero} {one} = refl
▷F-distr {forth} {forth} {zero} = refl
▷F-distr {forth} {forth} {forth} = refl
▷F-distr {forth} {forth} {half} = refl
▷F-distr {forth} {forth} {one} = refl
▷F-distr {forth} {half} {zero} = refl
▷F-distr {forth} {half} {forth} = refl
▷F-distr {forth} {half} {half} = refl
▷F-distr {forth} {half} {one} = refl
▷F-distr {forth} {one} {zero} = refl
▷F-distr {forth} {one} {forth} = refl
▷F-distr {forth} {one} {half} = refl
▷F-distr {forth} {one} {one} = refl
▷F-distr {half} {zero} {zero} = refl
▷F-distr {half} {zero} {forth} = refl
▷F-distr {half} {zero} {half} = refl
▷F-distr {half} {zero} {one} = refl
▷F-distr {half} {forth} {zero} = refl
▷F-distr {half} {forth} {forth} = refl
▷F-distr {half} {forth} {half} = refl
▷F-distr {half} {forth} {one} = refl
▷F-distr {half} {half} {zero} = refl
▷F-distr {half} {half} {forth} = refl
▷F-distr {half} {half} {half} = refl
▷F-distr {half} {half} {one} = refl
▷F-distr {half} {one} {zero} = refl
▷F-distr {half} {one} {forth} = refl
▷F-distr {half} {one} {half} = refl
▷F-distr {half} {one} {one} = refl
▷F-distr {one} {zero} {zero} = refl
▷F-distr {one} {zero} {forth} = refl
▷F-distr {one} {zero} {half} = refl
▷F-distr {one} {zero} {one} = refl
▷F-distr {one} {forth} {zero} = refl
▷F-distr {one} {forth} {forth} = refl
▷F-distr {one} {forth} {half} = refl
▷F-distr {one} {forth} {one} = refl
▷F-distr {one} {half} {zero} = refl
▷F-distr {one} {half} {forth} = refl
▷F-distr {one} {half} {half} = refl
▷F-distr {one} {half} {one} = refl
▷F-distr {one} {one} {zero} = refl
▷F-distr {one} {one} {forth} = refl
▷F-distr {one} {one} {half} = refl
▷F-distr {one} {one} {one} = refl

⊔F-sym : ∀{a b} → (a ⊔F b) ≡ (b ⊔F a)
⊔F-sym {zero} {zero} = refl
⊔F-sym {zero} {forth} = refl
⊔F-sym {zero} {half} = refl
⊔F-sym {zero} {one} = refl
⊔F-sym {forth} {zero} = refl
⊔F-sym {forth} {forth} = refl
⊔F-sym {forth} {half} = refl
⊔F-sym {forth} {one} = refl
⊔F-sym {half} {zero} = refl
⊔F-sym {half} {forth} = refl
⊔F-sym {half} {half} = refl
⊔F-sym {half} {one} = refl
⊔F-sym {one} {zero} = refl
⊔F-sym {one} {forth} = refl
⊔F-sym {one} {half} = refl
⊔F-sym {one} {one} = refl

⊔F-assoc : ∀{a b c} → (a ⊔F b) ⊔F c ≡ a ⊔F (b ⊔F c)
⊔F-assoc {zero} {zero} {zero} = refl
⊔F-assoc {zero} {zero} {forth} = refl
⊔F-assoc {zero} {zero} {half} = refl
⊔F-assoc {zero} {zero} {one} = refl
⊔F-assoc {zero} {forth} {zero} = refl
⊔F-assoc {zero} {forth} {forth} = refl
⊔F-assoc {zero} {forth} {half} = refl
⊔F-assoc {zero} {forth} {one} = refl
⊔F-assoc {zero} {half} {zero} = refl
⊔F-assoc {zero} {half} {forth} = refl
⊔F-assoc {zero} {half} {half} = refl
⊔F-assoc {zero} {half} {one} = refl
⊔F-assoc {zero} {one} {zero} = refl
⊔F-assoc {zero} {one} {forth} = refl
⊔F-assoc {zero} {one} {half} = refl
⊔F-assoc {zero} {one} {one} = refl
⊔F-assoc {forth} {zero} {zero} = refl
⊔F-assoc {forth} {zero} {forth} = refl
⊔F-assoc {forth} {zero} {half} = refl
⊔F-assoc {forth} {zero} {one} = refl
⊔F-assoc {forth} {forth} {zero} = refl
⊔F-assoc {forth} {forth} {forth} = refl
⊔F-assoc {forth} {forth} {half} = refl
⊔F-assoc {forth} {forth} {one} = refl
⊔F-assoc {forth} {half} {zero} = refl
⊔F-assoc {forth} {half} {forth} = refl
⊔F-assoc {forth} {half} {half} = refl
⊔F-assoc {forth} {half} {one} = refl
⊔F-assoc {forth} {one} {zero} = refl
⊔F-assoc {forth} {one} {forth} = refl
⊔F-assoc {forth} {one} {half} = refl
⊔F-assoc {forth} {one} {one} = refl
⊔F-assoc {half} {zero} {zero} = refl
⊔F-assoc {half} {zero} {forth} = refl
⊔F-assoc {half} {zero} {half} = refl
⊔F-assoc {half} {zero} {one} = refl
⊔F-assoc {half} {forth} {zero} = refl
⊔F-assoc {half} {forth} {forth} = refl
⊔F-assoc {half} {forth} {half} = refl
⊔F-assoc {half} {forth} {one} = refl
⊔F-assoc {half} {half} {zero} = refl
⊔F-assoc {half} {half} {forth} = refl
⊔F-assoc {half} {half} {half} = refl
⊔F-assoc {half} {half} {one} = refl
⊔F-assoc {half} {one} {zero} = refl
⊔F-assoc {half} {one} {forth} = refl
⊔F-assoc {half} {one} {half} = refl
⊔F-assoc {half} {one} {one} = refl
⊔F-assoc {one} {zero} {zero} = refl
⊔F-assoc {one} {zero} {forth} = refl
⊔F-assoc {one} {zero} {half} = refl
⊔F-assoc {one} {zero} {one} = refl
⊔F-assoc {one} {forth} {zero} = refl
⊔F-assoc {one} {forth} {forth} = refl
⊔F-assoc {one} {forth} {half} = refl
⊔F-assoc {one} {forth} {one} = refl
⊔F-assoc {one} {half} {zero} = refl
⊔F-assoc {one} {half} {forth} = refl
⊔F-assoc {one} {half} {half} = refl
⊔F-assoc {one} {half} {one} = refl
⊔F-assoc {one} {one} {zero} = refl
⊔F-assoc {one} {one} {forth} = refl
⊔F-assoc {one} {one} {half} = refl
⊔F-assoc {one} {one} {one} = refl

⊔F-func : ∀{a c b d} → a ≤₄ c → b ≤₄ d → (a ⊔F b) ≤₄ (c ⊔F d)
⊔F-func {zero} {zero} {zero} {zero} triv triv = triv
⊔F-func {zero} {zero} {zero} {forth} triv triv = triv
⊔F-func {zero} {zero} {zero} {half} triv triv = triv
⊔F-func {zero} {zero} {zero} {one} triv triv = triv
⊔F-func {zero} {zero} {forth} {zero} triv ()
⊔F-func {zero} {zero} {forth} {forth} triv triv = triv
⊔F-func {zero} {zero} {forth} {half} triv triv = triv
⊔F-func {zero} {zero} {forth} {one} triv triv = triv
⊔F-func {zero} {zero} {half} {zero} triv ()
⊔F-func {zero} {zero} {half} {forth} triv ()
⊔F-func {zero} {zero} {half} {half} triv triv = triv
⊔F-func {zero} {zero} {half} {one} triv triv = triv
⊔F-func {zero} {zero} {one} {zero} triv ()
⊔F-func {zero} {zero} {one} {forth} triv ()
⊔F-func {zero} {zero} {one} {half} triv ()
⊔F-func {zero} {zero} {one} {one} triv triv = triv
⊔F-func {zero} {forth} {zero} {zero} triv triv = triv
⊔F-func {zero} {forth} {zero} {forth} triv triv = triv
⊔F-func {zero} {forth} {zero} {half} triv triv = triv
⊔F-func {zero} {forth} {zero} {one} triv triv = triv
⊔F-func {zero} {forth} {forth} {zero} triv ()
⊔F-func {zero} {forth} {forth} {forth} triv triv = triv
⊔F-func {zero} {forth} {forth} {half} triv triv = triv
⊔F-func {zero} {forth} {forth} {one} triv triv = triv
⊔F-func {zero} {forth} {half} {zero} triv ()
⊔F-func {zero} {forth} {half} {forth} triv ()
⊔F-func {zero} {forth} {half} {half} triv triv = triv
⊔F-func {zero} {forth} {half} {one} triv triv = triv
⊔F-func {zero} {forth} {one} {zero} triv ()
⊔F-func {zero} {forth} {one} {forth} triv ()
⊔F-func {zero} {forth} {one} {half} triv ()
⊔F-func {zero} {forth} {one} {one} triv triv = triv
⊔F-func {zero} {half} {zero} {zero} triv triv = triv
⊔F-func {zero} {half} {zero} {forth} triv triv = triv
⊔F-func {zero} {half} {zero} {half} triv triv = triv
⊔F-func {zero} {half} {zero} {one} triv triv = triv
⊔F-func {zero} {half} {forth} {zero} triv ()
⊔F-func {zero} {half} {forth} {forth} triv triv = triv
⊔F-func {zero} {half} {forth} {half} triv triv = triv
⊔F-func {zero} {half} {forth} {one} triv triv = triv
⊔F-func {zero} {half} {half} {zero} triv ()
⊔F-func {zero} {half} {half} {forth} triv ()
⊔F-func {zero} {half} {half} {half} triv triv = triv
⊔F-func {zero} {half} {half} {one} triv triv = triv
⊔F-func {zero} {half} {one} {zero} triv ()
⊔F-func {zero} {half} {one} {forth} triv ()
⊔F-func {zero} {half} {one} {half} triv ()
⊔F-func {zero} {half} {one} {one} triv triv = triv
⊔F-func {zero} {one} {zero} {zero} triv triv = triv
⊔F-func {zero} {one} {zero} {forth} triv triv = triv
⊔F-func {zero} {one} {zero} {half} triv triv = triv
⊔F-func {zero} {one} {zero} {one} triv triv = triv
⊔F-func {zero} {one} {forth} {zero} triv ()
⊔F-func {zero} {one} {forth} {forth} triv triv = triv
⊔F-func {zero} {one} {forth} {half} triv triv = triv
⊔F-func {zero} {one} {forth} {one} triv triv = triv
⊔F-func {zero} {one} {half} {zero} triv ()
⊔F-func {zero} {one} {half} {forth} triv ()
⊔F-func {zero} {one} {half} {half} triv triv = triv
⊔F-func {zero} {one} {half} {one} triv triv = triv
⊔F-func {zero} {one} {one} {zero} triv ()
⊔F-func {zero} {one} {one} {forth} triv ()
⊔F-func {zero} {one} {one} {half} triv ()
⊔F-func {zero} {one} {one} {one} triv triv = triv
⊔F-func {forth} {zero} {zero} {zero} () p₂
⊔F-func {forth} {zero} {zero} {forth} () p₂
⊔F-func {forth} {zero} {zero} {half} () p₂
⊔F-func {forth} {zero} {zero} {one} () p₂
⊔F-func {forth} {zero} {forth} {zero} () p₂
⊔F-func {forth} {zero} {forth} {forth} () p₂
⊔F-func {forth} {zero} {forth} {half} () p₂
⊔F-func {forth} {zero} {forth} {one} () p₂
⊔F-func {forth} {zero} {half} {zero} () p₂
⊔F-func {forth} {zero} {half} {forth} () p₂
⊔F-func {forth} {zero} {half} {half} () p₂
⊔F-func {forth} {zero} {half} {one} () p₂
⊔F-func {forth} {zero} {one} {zero} () p₂
⊔F-func {forth} {zero} {one} {forth} () p₂
⊔F-func {forth} {zero} {one} {half} () p₂
⊔F-func {forth} {zero} {one} {one} () p₂
⊔F-func {forth} {forth} {zero} {zero} triv triv = triv
⊔F-func {forth} {forth} {zero} {forth} triv triv = triv
⊔F-func {forth} {forth} {zero} {half} triv triv = triv
⊔F-func {forth} {forth} {zero} {one} triv triv = triv
⊔F-func {forth} {forth} {forth} {zero} triv ()
⊔F-func {forth} {forth} {forth} {forth} triv triv = triv
⊔F-func {forth} {forth} {forth} {half} triv triv = triv
⊔F-func {forth} {forth} {forth} {one} triv triv = triv
⊔F-func {forth} {forth} {half} {zero} triv ()
⊔F-func {forth} {forth} {half} {forth} triv ()
⊔F-func {forth} {forth} {half} {half} triv triv = triv
⊔F-func {forth} {forth} {half} {one} triv triv = triv
⊔F-func {forth} {forth} {one} {zero} triv ()
⊔F-func {forth} {forth} {one} {forth} triv ()
⊔F-func {forth} {forth} {one} {half} triv ()
⊔F-func {forth} {forth} {one} {one} triv triv = triv
⊔F-func {forth} {half} {zero} {zero} triv triv = triv
⊔F-func {forth} {half} {zero} {forth} triv triv = triv
⊔F-func {forth} {half} {zero} {half} triv triv = triv
⊔F-func {forth} {half} {zero} {one} triv triv = triv
⊔F-func {forth} {half} {forth} {zero} triv ()
⊔F-func {forth} {half} {forth} {forth} triv triv = triv
⊔F-func {forth} {half} {forth} {half} triv triv = triv
⊔F-func {forth} {half} {forth} {one} triv triv = triv
⊔F-func {forth} {half} {half} {zero} triv ()
⊔F-func {forth} {half} {half} {forth} triv ()
⊔F-func {forth} {half} {half} {half} triv triv = triv
⊔F-func {forth} {half} {half} {one} triv triv = triv
⊔F-func {forth} {half} {one} {zero} triv ()
⊔F-func {forth} {half} {one} {forth} triv ()
⊔F-func {forth} {half} {one} {half} triv ()
⊔F-func {forth} {half} {one} {one} triv triv = triv
⊔F-func {forth} {one} {zero} {zero} triv triv = triv
⊔F-func {forth} {one} {zero} {forth} triv triv = triv
⊔F-func {forth} {one} {zero} {half} triv triv = triv
⊔F-func {forth} {one} {zero} {one} triv triv = triv
⊔F-func {forth} {one} {forth} {zero} triv ()
⊔F-func {forth} {one} {forth} {forth} triv triv = triv
⊔F-func {forth} {one} {forth} {half} triv triv = triv
⊔F-func {forth} {one} {forth} {one} triv triv = triv
⊔F-func {forth} {one} {half} {zero} triv ()
⊔F-func {forth} {one} {half} {forth} triv ()
⊔F-func {forth} {one} {half} {half} triv triv = triv
⊔F-func {forth} {one} {half} {one} triv triv = triv
⊔F-func {forth} {one} {one} {zero} triv ()
⊔F-func {forth} {one} {one} {forth} triv ()
⊔F-func {forth} {one} {one} {half} triv ()
⊔F-func {forth} {one} {one} {one} triv triv = triv
⊔F-func {half} {zero} {zero} {zero} () p₂
⊔F-func {half} {zero} {zero} {forth} () p₂
⊔F-func {half} {zero} {zero} {half} () p₂
⊔F-func {half} {zero} {zero} {one} () p₂
⊔F-func {half} {zero} {forth} {zero} () p₂
⊔F-func {half} {zero} {forth} {forth} () p₂
⊔F-func {half} {zero} {forth} {half} () p₂
⊔F-func {half} {zero} {forth} {one} () p₂
⊔F-func {half} {zero} {half} {zero} () p₂
⊔F-func {half} {zero} {half} {forth} () p₂
⊔F-func {half} {zero} {half} {half} () p₂
⊔F-func {half} {zero} {half} {one} () p₂
⊔F-func {half} {zero} {one} {zero} () p₂
⊔F-func {half} {zero} {one} {forth} () p₂
⊔F-func {half} {zero} {one} {half} () p₂
⊔F-func {half} {zero} {one} {one} () p₂
⊔F-func {half} {forth} {zero} {zero} () p₂
⊔F-func {half} {forth} {zero} {forth} () p₂
⊔F-func {half} {forth} {zero} {half} () p₂
⊔F-func {half} {forth} {zero} {one} () p₂
⊔F-func {half} {forth} {forth} {zero} () p₂
⊔F-func {half} {forth} {forth} {forth} () p₂
⊔F-func {half} {forth} {forth} {half} () p₂
⊔F-func {half} {forth} {forth} {one} () p₂
⊔F-func {half} {forth} {half} {zero} () p₂
⊔F-func {half} {forth} {half} {forth} () p₂
⊔F-func {half} {forth} {half} {half} () p₂
⊔F-func {half} {forth} {half} {one} () p₂
⊔F-func {half} {forth} {one} {zero} () p₂
⊔F-func {half} {forth} {one} {forth} () p₂
⊔F-func {half} {forth} {one} {half} () p₂
⊔F-func {half} {forth} {one} {one} () p₂
⊔F-func {half} {half} {zero} {zero} triv triv = triv
⊔F-func {half} {half} {zero} {forth} triv triv = triv
⊔F-func {half} {half} {zero} {half} triv triv = triv
⊔F-func {half} {half} {zero} {one} triv triv = triv
⊔F-func {half} {half} {forth} {zero} triv ()
⊔F-func {half} {half} {forth} {forth} triv triv = triv
⊔F-func {half} {half} {forth} {half} triv triv = triv
⊔F-func {half} {half} {forth} {one} triv triv = triv
⊔F-func {half} {half} {half} {zero} triv ()
⊔F-func {half} {half} {half} {forth} triv ()
⊔F-func {half} {half} {half} {half} triv triv = triv
⊔F-func {half} {half} {half} {one} triv triv = triv
⊔F-func {half} {half} {one} {zero} triv ()
⊔F-func {half} {half} {one} {forth} triv ()
⊔F-func {half} {half} {one} {half} triv ()
⊔F-func {half} {half} {one} {one} triv triv = triv
⊔F-func {half} {one} {zero} {zero} triv triv = triv
⊔F-func {half} {one} {zero} {forth} triv triv = triv
⊔F-func {half} {one} {zero} {half} triv triv = triv
⊔F-func {half} {one} {zero} {one} triv triv = triv
⊔F-func {half} {one} {forth} {zero} triv ()
⊔F-func {half} {one} {forth} {forth} triv triv = triv
⊔F-func {half} {one} {forth} {half} triv triv = triv
⊔F-func {half} {one} {forth} {one} triv triv = triv
⊔F-func {half} {one} {half} {zero} triv ()
⊔F-func {half} {one} {half} {forth} triv ()
⊔F-func {half} {one} {half} {half} triv triv = triv
⊔F-func {half} {one} {half} {one} triv triv = triv
⊔F-func {half} {one} {one} {zero} triv ()
⊔F-func {half} {one} {one} {forth} triv ()
⊔F-func {half} {one} {one} {half} triv ()
⊔F-func {half} {one} {one} {one} triv triv = triv
⊔F-func {one} {zero} {zero} {zero} () p₂
⊔F-func {one} {zero} {zero} {forth} () p₂
⊔F-func {one} {zero} {zero} {half} () p₂
⊔F-func {one} {zero} {zero} {one} () p₂
⊔F-func {one} {zero} {forth} {zero} () p₂
⊔F-func {one} {zero} {forth} {forth} () p₂
⊔F-func {one} {zero} {forth} {half} () p₂
⊔F-func {one} {zero} {forth} {one} () p₂
⊔F-func {one} {zero} {half} {zero} () p₂
⊔F-func {one} {zero} {half} {forth} () p₂
⊔F-func {one} {zero} {half} {half} () p₂
⊔F-func {one} {zero} {half} {one} () p₂
⊔F-func {one} {zero} {one} {zero} () p₂
⊔F-func {one} {zero} {one} {forth} () p₂
⊔F-func {one} {zero} {one} {half} () p₂
⊔F-func {one} {zero} {one} {one} () p₂
⊔F-func {one} {forth} {zero} {zero} () p₂
⊔F-func {one} {forth} {zero} {forth} () p₂
⊔F-func {one} {forth} {zero} {half} () p₂
⊔F-func {one} {forth} {zero} {one} () p₂
⊔F-func {one} {forth} {forth} {zero} () p₂
⊔F-func {one} {forth} {forth} {forth} () p₂
⊔F-func {one} {forth} {forth} {half} () p₂
⊔F-func {one} {forth} {forth} {one} () p₂
⊔F-func {one} {forth} {half} {zero} () p₂
⊔F-func {one} {forth} {half} {forth} () p₂
⊔F-func {one} {forth} {half} {half} () p₂
⊔F-func {one} {forth} {half} {one} () p₂
⊔F-func {one} {forth} {one} {zero} () p₂
⊔F-func {one} {forth} {one} {forth} () p₂
⊔F-func {one} {forth} {one} {half} () p₂
⊔F-func {one} {forth} {one} {one} () p₂
⊔F-func {one} {half} {zero} {zero} () p₂
⊔F-func {one} {half} {zero} {forth} () p₂
⊔F-func {one} {half} {zero} {half} () p₂
⊔F-func {one} {half} {zero} {one} () p₂
⊔F-func {one} {half} {forth} {zero} () p₂
⊔F-func {one} {half} {forth} {forth} () p₂
⊔F-func {one} {half} {forth} {half} () p₂
⊔F-func {one} {half} {forth} {one} () p₂
⊔F-func {one} {half} {half} {zero} () p₂
⊔F-func {one} {half} {half} {forth} () p₂
⊔F-func {one} {half} {half} {half} () p₂
⊔F-func {one} {half} {half} {one} () p₂
⊔F-func {one} {half} {one} {zero} () p₂
⊔F-func {one} {half} {one} {forth} () p₂
⊔F-func {one} {half} {one} {half} () p₂
⊔F-func {one} {half} {one} {one} () p₂
⊔F-func {one} {one} {zero} {zero} triv triv = triv
⊔F-func {one} {one} {zero} {forth} triv triv = triv
⊔F-func {one} {one} {zero} {half} triv triv = triv
⊔F-func {one} {one} {zero} {one} triv triv = triv
⊔F-func {one} {one} {forth} {zero} triv ()
⊔F-func {one} {one} {forth} {forth} triv triv = triv
⊔F-func {one} {one} {forth} {half} triv triv = triv
⊔F-func {one} {one} {forth} {one} triv triv = triv
⊔F-func {one} {one} {half} {zero} triv ()
⊔F-func {one} {one} {half} {forth} triv ()
⊔F-func {one} {one} {half} {half} triv triv = triv
⊔F-func {one} {one} {half} {one} triv triv = triv
⊔F-func {one} {one} {one} {zero} triv ()
⊔F-func {one} {one} {one} {forth} triv ()
⊔F-func {one} {one} {one} {half} triv ()
⊔F-func {one} {one} {one} {one} triv triv = triv

⊔F-contract : ∀{a} → (a ⊔F a) ≡ a
⊔F-contract {zero} = refl
⊔F-contract {forth} = refl
⊔F-contract {half} = refl
⊔F-contract {one} = refl

⊔F-inl : ∀{a b} → a ≤₄ (a ⊔F b)
⊔F-inl {zero} {zero} = triv
⊔F-inl {zero} {forth} = triv
⊔F-inl {zero} {half} = triv
⊔F-inl {zero} {one} = triv
⊔F-inl {forth} {zero} = triv
⊔F-inl {forth} {forth} = triv
⊔F-inl {forth} {half} = triv
⊔F-inl {forth} {one} = triv
⊔F-inl {half} {zero} = triv
⊔F-inl {half} {forth} = triv
⊔F-inl {half} {half} = triv
⊔F-inl {half} {one} = triv
⊔F-inl {one} {zero} = triv
⊔F-inl {one} {forth} = triv
⊔F-inl {one} {half} = triv
⊔F-inl {one} {one} = triv

⊔F-inr : ∀{a b} → b ≤₄ (a ⊔F b)
⊔F-inr {zero} {zero} = triv
⊔F-inr {zero} {forth} = triv
⊔F-inr {zero} {half} = triv
⊔F-inr {zero} {one} = triv
⊔F-inr {forth} {zero} = triv
⊔F-inr {forth} {forth} = triv
⊔F-inr {forth} {half} = triv
⊔F-inr {forth} {one} = triv
⊔F-inr {half} {zero} = triv
⊔F-inr {half} {forth} = triv
⊔F-inr {half} {half} = triv
⊔F-inr {half} {one} = triv
⊔F-inr {one} {zero} = triv
⊔F-inr {one} {forth} = triv
⊔F-inr {one} {half} = triv
⊔F-inr {one} {one} = triv

-- Exchange Implications (Fig. 9, top of p. 18):

ax₁-inv : ∀{a b c d} → (a ⊙F b) ▷F (c ⊙F d) ≤₄ (a ▷F c) ⊙F (b ▷F d)
ax₁-inv {zero} {zero} {zero} {zero} = triv
ax₁-inv {zero} {zero} {zero} {forth} = triv
ax₁-inv {zero} {zero} {zero} {half} = triv
ax₁-inv {zero} {zero} {zero} {one} = triv
ax₁-inv {zero} {zero} {forth} {zero} = triv
ax₁-inv {zero} {zero} {forth} {forth} = triv
ax₁-inv {zero} {zero} {forth} {half} = triv
ax₁-inv {zero} {zero} {forth} {one} = triv
ax₁-inv {zero} {zero} {half} {zero} = triv
ax₁-inv {zero} {zero} {half} {forth} = triv
ax₁-inv {zero} {zero} {half} {half} = triv
ax₁-inv {zero} {zero} {half} {one} = triv
ax₁-inv {zero} {zero} {one} {zero} = triv
ax₁-inv {zero} {zero} {one} {forth} = triv
ax₁-inv {zero} {zero} {one} {half} = triv
ax₁-inv {zero} {zero} {one} {one} = triv
ax₁-inv {zero} {forth} {zero} {zero} = triv
ax₁-inv {zero} {forth} {zero} {forth} = triv
ax₁-inv {zero} {forth} {zero} {half} = triv
ax₁-inv {zero} {forth} {zero} {one} = triv
ax₁-inv {zero} {forth} {forth} {zero} = triv
ax₁-inv {zero} {forth} {forth} {forth} = triv
ax₁-inv {zero} {forth} {forth} {half} = triv
ax₁-inv {zero} {forth} {forth} {one} = triv
ax₁-inv {zero} {forth} {half} {zero} = triv
ax₁-inv {zero} {forth} {half} {forth} = triv
ax₁-inv {zero} {forth} {half} {half} = triv
ax₁-inv {zero} {forth} {half} {one} = triv
ax₁-inv {zero} {forth} {one} {zero} = triv
ax₁-inv {zero} {forth} {one} {forth} = triv
ax₁-inv {zero} {forth} {one} {half} = triv
ax₁-inv {zero} {forth} {one} {one} = triv
ax₁-inv {zero} {half} {zero} {zero} = triv
ax₁-inv {zero} {half} {zero} {forth} = triv
ax₁-inv {zero} {half} {zero} {half} = triv
ax₁-inv {zero} {half} {zero} {one} = triv
ax₁-inv {zero} {half} {forth} {zero} = triv
ax₁-inv {zero} {half} {forth} {forth} = triv
ax₁-inv {zero} {half} {forth} {half} = triv
ax₁-inv {zero} {half} {forth} {one} = triv
ax₁-inv {zero} {half} {half} {zero} = triv
ax₁-inv {zero} {half} {half} {forth} = triv
ax₁-inv {zero} {half} {half} {half} = triv
ax₁-inv {zero} {half} {half} {one} = triv
ax₁-inv {zero} {half} {one} {zero} = triv
ax₁-inv {zero} {half} {one} {forth} = triv
ax₁-inv {zero} {half} {one} {half} = triv
ax₁-inv {zero} {half} {one} {one} = triv
ax₁-inv {zero} {one} {zero} {zero} = triv
ax₁-inv {zero} {one} {zero} {forth} = triv
ax₁-inv {zero} {one} {zero} {half} = triv
ax₁-inv {zero} {one} {zero} {one} = triv
ax₁-inv {zero} {one} {forth} {zero} = triv
ax₁-inv {zero} {one} {forth} {forth} = triv
ax₁-inv {zero} {one} {forth} {half} = triv
ax₁-inv {zero} {one} {forth} {one} = triv
ax₁-inv {zero} {one} {half} {zero} = triv
ax₁-inv {zero} {one} {half} {forth} = triv
ax₁-inv {zero} {one} {half} {half} = triv
ax₁-inv {zero} {one} {half} {one} = triv
ax₁-inv {zero} {one} {one} {zero} = triv
ax₁-inv {zero} {one} {one} {forth} = triv
ax₁-inv {zero} {one} {one} {half} = triv
ax₁-inv {zero} {one} {one} {one} = triv
ax₁-inv {forth} {zero} {zero} {zero} = triv
ax₁-inv {forth} {zero} {zero} {forth} = triv
ax₁-inv {forth} {zero} {zero} {half} = triv
ax₁-inv {forth} {zero} {zero} {one} = triv
ax₁-inv {forth} {zero} {forth} {zero} = triv
ax₁-inv {forth} {zero} {forth} {forth} = triv
ax₁-inv {forth} {zero} {forth} {half} = triv
ax₁-inv {forth} {zero} {forth} {one} = triv
ax₁-inv {forth} {zero} {half} {zero} = triv
ax₁-inv {forth} {zero} {half} {forth} = triv
ax₁-inv {forth} {zero} {half} {half} = triv
ax₁-inv {forth} {zero} {half} {one} = triv
ax₁-inv {forth} {zero} {one} {zero} = triv
ax₁-inv {forth} {zero} {one} {forth} = triv
ax₁-inv {forth} {zero} {one} {half} = triv
ax₁-inv {forth} {zero} {one} {one} = triv
ax₁-inv {forth} {forth} {zero} {zero} = triv
ax₁-inv {forth} {forth} {zero} {forth} = triv
ax₁-inv {forth} {forth} {zero} {half} = triv
ax₁-inv {forth} {forth} {zero} {one} = triv
ax₁-inv {forth} {forth} {forth} {zero} = triv
ax₁-inv {forth} {forth} {forth} {forth} = triv
ax₁-inv {forth} {forth} {forth} {half} = triv
ax₁-inv {forth} {forth} {forth} {one} = triv
ax₁-inv {forth} {forth} {half} {zero} = triv
ax₁-inv {forth} {forth} {half} {forth} = triv
ax₁-inv {forth} {forth} {half} {half} = triv
ax₁-inv {forth} {forth} {half} {one} = triv
ax₁-inv {forth} {forth} {one} {zero} = triv
ax₁-inv {forth} {forth} {one} {forth} = triv
ax₁-inv {forth} {forth} {one} {half} = triv
ax₁-inv {forth} {forth} {one} {one} = triv
ax₁-inv {forth} {half} {zero} {zero} = triv
ax₁-inv {forth} {half} {zero} {forth} = triv
ax₁-inv {forth} {half} {zero} {half} = triv
ax₁-inv {forth} {half} {zero} {one} = triv
ax₁-inv {forth} {half} {forth} {zero} = triv
ax₁-inv {forth} {half} {forth} {forth} = triv
ax₁-inv {forth} {half} {forth} {half} = triv
ax₁-inv {forth} {half} {forth} {one} = triv
ax₁-inv {forth} {half} {half} {zero} = triv
ax₁-inv {forth} {half} {half} {forth} = triv
ax₁-inv {forth} {half} {half} {half} = triv
ax₁-inv {forth} {half} {half} {one} = triv
ax₁-inv {forth} {half} {one} {zero} = triv
ax₁-inv {forth} {half} {one} {forth} = triv
ax₁-inv {forth} {half} {one} {half} = triv
ax₁-inv {forth} {half} {one} {one} = triv
ax₁-inv {forth} {one} {zero} {zero} = triv
ax₁-inv {forth} {one} {zero} {forth} = triv
ax₁-inv {forth} {one} {zero} {half} = triv
ax₁-inv {forth} {one} {zero} {one} = triv
ax₁-inv {forth} {one} {forth} {zero} = triv
ax₁-inv {forth} {one} {forth} {forth} = triv
ax₁-inv {forth} {one} {forth} {half} = triv
ax₁-inv {forth} {one} {forth} {one} = triv
ax₁-inv {forth} {one} {half} {zero} = triv
ax₁-inv {forth} {one} {half} {forth} = triv
ax₁-inv {forth} {one} {half} {half} = triv
ax₁-inv {forth} {one} {half} {one} = triv
ax₁-inv {forth} {one} {one} {zero} = triv
ax₁-inv {forth} {one} {one} {forth} = triv
ax₁-inv {forth} {one} {one} {half} = triv
ax₁-inv {forth} {one} {one} {one} = triv
ax₁-inv {half} {zero} {zero} {zero} = triv
ax₁-inv {half} {zero} {zero} {forth} = triv
ax₁-inv {half} {zero} {zero} {half} = triv
ax₁-inv {half} {zero} {zero} {one} = triv
ax₁-inv {half} {zero} {forth} {zero} = triv
ax₁-inv {half} {zero} {forth} {forth} = triv
ax₁-inv {half} {zero} {forth} {half} = triv
ax₁-inv {half} {zero} {forth} {one} = triv
ax₁-inv {half} {zero} {half} {zero} = triv
ax₁-inv {half} {zero} {half} {forth} = triv
ax₁-inv {half} {zero} {half} {half} = triv
ax₁-inv {half} {zero} {half} {one} = triv
ax₁-inv {half} {zero} {one} {zero} = triv
ax₁-inv {half} {zero} {one} {forth} = triv
ax₁-inv {half} {zero} {one} {half} = triv
ax₁-inv {half} {zero} {one} {one} = triv
ax₁-inv {half} {forth} {zero} {zero} = triv
ax₁-inv {half} {forth} {zero} {forth} = triv
ax₁-inv {half} {forth} {zero} {half} = triv
ax₁-inv {half} {forth} {zero} {one} = triv
ax₁-inv {half} {forth} {forth} {zero} = triv
ax₁-inv {half} {forth} {forth} {forth} = triv
ax₁-inv {half} {forth} {forth} {half} = triv
ax₁-inv {half} {forth} {forth} {one} = triv
ax₁-inv {half} {forth} {half} {zero} = triv
ax₁-inv {half} {forth} {half} {forth} = triv
ax₁-inv {half} {forth} {half} {half} = triv
ax₁-inv {half} {forth} {half} {one} = triv
ax₁-inv {half} {forth} {one} {zero} = triv
ax₁-inv {half} {forth} {one} {forth} = triv
ax₁-inv {half} {forth} {one} {half} = triv
ax₁-inv {half} {forth} {one} {one} = triv
ax₁-inv {half} {half} {zero} {zero} = triv
ax₁-inv {half} {half} {zero} {forth} = triv
ax₁-inv {half} {half} {zero} {half} = triv
ax₁-inv {half} {half} {zero} {one} = triv
ax₁-inv {half} {half} {forth} {zero} = triv
ax₁-inv {half} {half} {forth} {forth} = triv
ax₁-inv {half} {half} {forth} {half} = triv
ax₁-inv {half} {half} {forth} {one} = triv
ax₁-inv {half} {half} {half} {zero} = triv
ax₁-inv {half} {half} {half} {forth} = triv
ax₁-inv {half} {half} {half} {half} = triv
ax₁-inv {half} {half} {half} {one} = triv
ax₁-inv {half} {half} {one} {zero} = triv
ax₁-inv {half} {half} {one} {forth} = triv
ax₁-inv {half} {half} {one} {half} = triv
ax₁-inv {half} {half} {one} {one} = triv
ax₁-inv {half} {one} {zero} {zero} = triv
ax₁-inv {half} {one} {zero} {forth} = triv
ax₁-inv {half} {one} {zero} {half} = triv
ax₁-inv {half} {one} {zero} {one} = triv
ax₁-inv {half} {one} {forth} {zero} = triv
ax₁-inv {half} {one} {forth} {forth} = triv
ax₁-inv {half} {one} {forth} {half} = triv
ax₁-inv {half} {one} {forth} {one} = triv
ax₁-inv {half} {one} {half} {zero} = triv
ax₁-inv {half} {one} {half} {forth} = triv
ax₁-inv {half} {one} {half} {half} = triv
ax₁-inv {half} {one} {half} {one} = triv
ax₁-inv {half} {one} {one} {zero} = triv
ax₁-inv {half} {one} {one} {forth} = triv
ax₁-inv {half} {one} {one} {half} = triv
ax₁-inv {half} {one} {one} {one} = triv
ax₁-inv {one} {zero} {zero} {zero} = triv
ax₁-inv {one} {zero} {zero} {forth} = triv
ax₁-inv {one} {zero} {zero} {half} = triv
ax₁-inv {one} {zero} {zero} {one} = triv
ax₁-inv {one} {zero} {forth} {zero} = triv
ax₁-inv {one} {zero} {forth} {forth} = triv
ax₁-inv {one} {zero} {forth} {half} = triv
ax₁-inv {one} {zero} {forth} {one} = triv
ax₁-inv {one} {zero} {half} {zero} = triv
ax₁-inv {one} {zero} {half} {forth} = triv
ax₁-inv {one} {zero} {half} {half} = triv
ax₁-inv {one} {zero} {half} {one} = triv
ax₁-inv {one} {zero} {one} {zero} = triv
ax₁-inv {one} {zero} {one} {forth} = triv
ax₁-inv {one} {zero} {one} {half} = triv
ax₁-inv {one} {zero} {one} {one} = triv
ax₁-inv {one} {forth} {zero} {zero} = triv
ax₁-inv {one} {forth} {zero} {forth} = triv
ax₁-inv {one} {forth} {zero} {half} = triv
ax₁-inv {one} {forth} {zero} {one} = triv
ax₁-inv {one} {forth} {forth} {zero} = triv
ax₁-inv {one} {forth} {forth} {forth} = triv
ax₁-inv {one} {forth} {forth} {half} = triv
ax₁-inv {one} {forth} {forth} {one} = triv
ax₁-inv {one} {forth} {half} {zero} = triv
ax₁-inv {one} {forth} {half} {forth} = triv
ax₁-inv {one} {forth} {half} {half} = triv
ax₁-inv {one} {forth} {half} {one} = triv
ax₁-inv {one} {forth} {one} {zero} = triv
ax₁-inv {one} {forth} {one} {forth} = triv
ax₁-inv {one} {forth} {one} {half} = triv
ax₁-inv {one} {forth} {one} {one} = triv
ax₁-inv {one} {half} {zero} {zero} = triv
ax₁-inv {one} {half} {zero} {forth} = triv
ax₁-inv {one} {half} {zero} {half} = triv
ax₁-inv {one} {half} {zero} {one} = triv
ax₁-inv {one} {half} {forth} {zero} = triv
ax₁-inv {one} {half} {forth} {forth} = triv
ax₁-inv {one} {half} {forth} {half} = triv
ax₁-inv {one} {half} {forth} {one} = triv
ax₁-inv {one} {half} {half} {zero} = triv
ax₁-inv {one} {half} {half} {forth} = triv
ax₁-inv {one} {half} {half} {half} = triv
ax₁-inv {one} {half} {half} {one} = triv
ax₁-inv {one} {half} {one} {zero} = triv
ax₁-inv {one} {half} {one} {forth} = triv
ax₁-inv {one} {half} {one} {half} = triv
ax₁-inv {one} {half} {one} {one} = triv
ax₁-inv {one} {one} {zero} {zero} = triv
ax₁-inv {one} {one} {zero} {forth} = triv
ax₁-inv {one} {one} {zero} {half} = triv
ax₁-inv {one} {one} {zero} {one} = triv
ax₁-inv {one} {one} {forth} {zero} = triv
ax₁-inv {one} {one} {forth} {forth} = triv
ax₁-inv {one} {one} {forth} {half} = triv
ax₁-inv {one} {one} {forth} {one} = triv
ax₁-inv {one} {one} {half} {zero} = triv
ax₁-inv {one} {one} {half} {forth} = triv
ax₁-inv {one} {one} {half} {half} = triv
ax₁-inv {one} {one} {half} {one} = triv
ax₁-inv {one} {one} {one} {zero} = triv
ax₁-inv {one} {one} {one} {forth} = triv
ax₁-inv {one} {one} {one} {half} = triv
ax₁-inv {one} {one} {one} {one} = triv

-- Filter
ax₁ : ∀{a b c d} → (a ▷F c) ⊙F (b ▷F d) ≤₄ (a ⊙F b) ▷F (c ⊙F d)
ax₁ {zero} {zero} {zero} {zero} = triv
ax₁ {zero} {zero} {zero} {forth} = triv
ax₁ {zero} {zero} {zero} {half} = triv
ax₁ {zero} {zero} {zero} {one} = triv
ax₁ {zero} {zero} {forth} {zero} = triv
ax₁ {zero} {zero} {forth} {forth} = triv
ax₁ {zero} {zero} {forth} {half} = triv
ax₁ {zero} {zero} {forth} {one} = triv
ax₁ {zero} {zero} {half} {zero} = triv
ax₁ {zero} {zero} {half} {forth} = triv
ax₁ {zero} {zero} {half} {half} = triv
ax₁ {zero} {zero} {half} {one} = triv
ax₁ {zero} {zero} {one} {zero} = triv
ax₁ {zero} {zero} {one} {forth} = triv
ax₁ {zero} {zero} {one} {half} = triv
ax₁ {zero} {zero} {one} {one} = triv
ax₁ {zero} {forth} {zero} {zero} = triv
ax₁ {zero} {forth} {zero} {forth} = triv
ax₁ {zero} {forth} {zero} {half} = triv
ax₁ {zero} {forth} {zero} {one} = triv
ax₁ {zero} {forth} {forth} {zero} = triv
ax₁ {zero} {forth} {forth} {forth} = triv
ax₁ {zero} {forth} {forth} {half} = triv
ax₁ {zero} {forth} {forth} {one} = triv
ax₁ {zero} {forth} {half} {zero} = triv
ax₁ {zero} {forth} {half} {forth} = triv
ax₁ {zero} {forth} {half} {half} = triv
ax₁ {zero} {forth} {half} {one} = triv
ax₁ {zero} {forth} {one} {zero} = triv
ax₁ {zero} {forth} {one} {forth} = triv
ax₁ {zero} {forth} {one} {half} = triv
ax₁ {zero} {forth} {one} {one} = triv
ax₁ {zero} {half} {zero} {zero} = triv
ax₁ {zero} {half} {zero} {forth} = triv
ax₁ {zero} {half} {zero} {half} = triv
ax₁ {zero} {half} {zero} {one} = triv
ax₁ {zero} {half} {forth} {zero} = triv
ax₁ {zero} {half} {forth} {forth} = triv
ax₁ {zero} {half} {forth} {half} = triv
ax₁ {zero} {half} {forth} {one} = triv
ax₁ {zero} {half} {half} {zero} = triv
ax₁ {zero} {half} {half} {forth} = triv
ax₁ {zero} {half} {half} {half} = triv
ax₁ {zero} {half} {half} {one} = triv
ax₁ {zero} {half} {one} {zero} = triv
ax₁ {zero} {half} {one} {forth} = triv
ax₁ {zero} {half} {one} {half} = triv
ax₁ {zero} {half} {one} {one} = triv
ax₁ {zero} {one} {zero} {zero} = triv
ax₁ {zero} {one} {zero} {forth} = triv
ax₁ {zero} {one} {zero} {half} = triv
ax₁ {zero} {one} {zero} {one} = triv
ax₁ {zero} {one} {forth} {zero} = triv
ax₁ {zero} {one} {forth} {forth} = triv
ax₁ {zero} {one} {forth} {half} = triv
ax₁ {zero} {one} {forth} {one} = triv
ax₁ {zero} {one} {half} {zero} = triv
ax₁ {zero} {one} {half} {forth} = triv
ax₁ {zero} {one} {half} {half} = triv
ax₁ {zero} {one} {half} {one} = triv
ax₁ {zero} {one} {one} {zero} = triv
ax₁ {zero} {one} {one} {forth} = triv
ax₁ {zero} {one} {one} {half} = triv
ax₁ {zero} {one} {one} {one} = triv
ax₁ {forth} {zero} {zero} {zero} = triv
ax₁ {forth} {zero} {zero} {forth} = triv
ax₁ {forth} {zero} {zero} {half} = triv
ax₁ {forth} {zero} {zero} {one} = triv
ax₁ {forth} {zero} {forth} {zero} = triv
ax₁ {forth} {zero} {forth} {forth} = triv
ax₁ {forth} {zero} {forth} {half} = triv
ax₁ {forth} {zero} {forth} {one} = triv
ax₁ {forth} {zero} {half} {zero} = triv
ax₁ {forth} {zero} {half} {forth} = triv
ax₁ {forth} {zero} {half} {half} = triv
ax₁ {forth} {zero} {half} {one} = triv
ax₁ {forth} {zero} {one} {zero} = triv
ax₁ {forth} {zero} {one} {forth} = triv
ax₁ {forth} {zero} {one} {half} = triv
ax₁ {forth} {zero} {one} {one} = triv
ax₁ {forth} {forth} {zero} {zero} = triv
ax₁ {forth} {forth} {zero} {forth} = triv
ax₁ {forth} {forth} {zero} {half} = triv
ax₁ {forth} {forth} {zero} {one} = triv
ax₁ {forth} {forth} {forth} {zero} = triv
ax₁ {forth} {forth} {forth} {forth} = triv
ax₁ {forth} {forth} {forth} {half} = triv
ax₁ {forth} {forth} {forth} {one} = triv
ax₁ {forth} {forth} {half} {zero} = triv
ax₁ {forth} {forth} {half} {forth} = triv
ax₁ {forth} {forth} {half} {half} = triv
ax₁ {forth} {forth} {half} {one} = triv
ax₁ {forth} {forth} {one} {zero} = triv
ax₁ {forth} {forth} {one} {forth} = triv
ax₁ {forth} {forth} {one} {half} = triv
ax₁ {forth} {forth} {one} {one} = triv
ax₁ {forth} {half} {zero} {zero} = triv
ax₁ {forth} {half} {zero} {forth} = triv
ax₁ {forth} {half} {zero} {half} = triv
ax₁ {forth} {half} {zero} {one} = triv
ax₁ {forth} {half} {forth} {zero} = triv
ax₁ {forth} {half} {forth} {forth} = triv
ax₁ {forth} {half} {forth} {half} = triv
ax₁ {forth} {half} {forth} {one} = triv
ax₁ {forth} {half} {half} {zero} = triv
ax₁ {forth} {half} {half} {forth} = triv
ax₁ {forth} {half} {half} {half} = triv
ax₁ {forth} {half} {half} {one} = triv
ax₁ {forth} {half} {one} {zero} = triv
ax₁ {forth} {half} {one} {forth} = triv
ax₁ {forth} {half} {one} {half} = triv
ax₁ {forth} {half} {one} {one} = triv
ax₁ {forth} {one} {zero} {zero} = triv
ax₁ {forth} {one} {zero} {forth} = triv
ax₁ {forth} {one} {zero} {half} = triv
ax₁ {forth} {one} {zero} {one} = triv
ax₁ {forth} {one} {forth} {zero} = triv
ax₁ {forth} {one} {forth} {forth} = triv
ax₁ {forth} {one} {forth} {half} = triv
ax₁ {forth} {one} {forth} {one} = triv
ax₁ {forth} {one} {half} {zero} = triv
ax₁ {forth} {one} {half} {forth} = triv
ax₁ {forth} {one} {half} {half} = triv
ax₁ {forth} {one} {half} {one} = triv
ax₁ {forth} {one} {one} {zero} = triv
ax₁ {forth} {one} {one} {forth} = triv
ax₁ {forth} {one} {one} {half} = triv
ax₁ {forth} {one} {one} {one} = triv
ax₁ {half} {zero} {zero} {zero} = triv
ax₁ {half} {zero} {zero} {forth} = triv
ax₁ {half} {zero} {zero} {half} = triv
ax₁ {half} {zero} {zero} {one} = triv
ax₁ {half} {zero} {forth} {zero} = triv
ax₁ {half} {zero} {forth} {forth} = triv
ax₁ {half} {zero} {forth} {half} = triv
ax₁ {half} {zero} {forth} {one} = triv
ax₁ {half} {zero} {half} {zero} = triv
ax₁ {half} {zero} {half} {forth} = triv
ax₁ {half} {zero} {half} {half} = triv
ax₁ {half} {zero} {half} {one} = triv
ax₁ {half} {zero} {one} {zero} = triv
ax₁ {half} {zero} {one} {forth} = triv
ax₁ {half} {zero} {one} {half} = triv
ax₁ {half} {zero} {one} {one} = triv
ax₁ {half} {forth} {zero} {zero} = triv
ax₁ {half} {forth} {zero} {forth} = triv
ax₁ {half} {forth} {zero} {half} = triv
ax₁ {half} {forth} {zero} {one} = triv
ax₁ {half} {forth} {forth} {zero} = triv
ax₁ {half} {forth} {forth} {forth} = triv
ax₁ {half} {forth} {forth} {half} = triv
ax₁ {half} {forth} {forth} {one} = triv
ax₁ {half} {forth} {half} {zero} = triv
ax₁ {half} {forth} {half} {forth} = triv
ax₁ {half} {forth} {half} {half} = triv
ax₁ {half} {forth} {half} {one} = triv
ax₁ {half} {forth} {one} {zero} = triv
ax₁ {half} {forth} {one} {forth} = triv
ax₁ {half} {forth} {one} {half} = triv
ax₁ {half} {forth} {one} {one} = triv
ax₁ {half} {half} {zero} {zero} = triv
ax₁ {half} {half} {zero} {forth} = triv
ax₁ {half} {half} {zero} {half} = triv
ax₁ {half} {half} {zero} {one} = triv
ax₁ {half} {half} {forth} {zero} = triv
ax₁ {half} {half} {forth} {forth} = triv
ax₁ {half} {half} {forth} {half} = triv
ax₁ {half} {half} {forth} {one} = triv
ax₁ {half} {half} {half} {zero} = triv
ax₁ {half} {half} {half} {forth} = triv
ax₁ {half} {half} {half} {half} = triv
ax₁ {half} {half} {half} {one} = triv
ax₁ {half} {half} {one} {zero} = triv
ax₁ {half} {half} {one} {forth} = triv
ax₁ {half} {half} {one} {half} = triv
ax₁ {half} {half} {one} {one} = triv
ax₁ {half} {one} {zero} {zero} = triv
ax₁ {half} {one} {zero} {forth} = triv
ax₁ {half} {one} {zero} {half} = triv
ax₁ {half} {one} {zero} {one} = triv
ax₁ {half} {one} {forth} {zero} = triv
ax₁ {half} {one} {forth} {forth} = triv
ax₁ {half} {one} {forth} {half} = triv
ax₁ {half} {one} {forth} {one} = triv
ax₁ {half} {one} {half} {zero} = triv
ax₁ {half} {one} {half} {forth} = triv
ax₁ {half} {one} {half} {half} = triv
ax₁ {half} {one} {half} {one} = triv
ax₁ {half} {one} {one} {zero} = triv
ax₁ {half} {one} {one} {forth} = triv
ax₁ {half} {one} {one} {half} = triv
ax₁ {half} {one} {one} {one} = triv
ax₁ {one} {zero} {zero} {zero} = triv
ax₁ {one} {zero} {zero} {forth} = triv
ax₁ {one} {zero} {zero} {half} = triv
ax₁ {one} {zero} {zero} {one} = triv
ax₁ {one} {zero} {forth} {zero} = triv
ax₁ {one} {zero} {forth} {forth} = triv
ax₁ {one} {zero} {forth} {half} = triv
ax₁ {one} {zero} {forth} {one} = triv
ax₁ {one} {zero} {half} {zero} = triv
ax₁ {one} {zero} {half} {forth} = triv
ax₁ {one} {zero} {half} {half} = triv
ax₁ {one} {zero} {half} {one} = triv
ax₁ {one} {zero} {one} {zero} = triv
ax₁ {one} {zero} {one} {forth} = triv
ax₁ {one} {zero} {one} {half} = triv
ax₁ {one} {zero} {one} {one} = triv
ax₁ {one} {forth} {zero} {zero} = triv
ax₁ {one} {forth} {zero} {forth} = triv
ax₁ {one} {forth} {zero} {half} = triv
ax₁ {one} {forth} {zero} {one} = triv
ax₁ {one} {forth} {forth} {zero} = triv
ax₁ {one} {forth} {forth} {forth} = triv
ax₁ {one} {forth} {forth} {half} = triv
ax₁ {one} {forth} {forth} {one} = triv
ax₁ {one} {forth} {half} {zero} = triv
ax₁ {one} {forth} {half} {forth} = triv
ax₁ {one} {forth} {half} {half} = triv
ax₁ {one} {forth} {half} {one} = triv
ax₁ {one} {forth} {one} {zero} = triv
ax₁ {one} {forth} {one} {forth} = triv
ax₁ {one} {forth} {one} {half} = triv
ax₁ {one} {forth} {one} {one} = triv
ax₁ {one} {half} {zero} {zero} = triv
ax₁ {one} {half} {zero} {forth} = triv
ax₁ {one} {half} {zero} {half} = triv
ax₁ {one} {half} {zero} {one} = triv
ax₁ {one} {half} {forth} {zero} = triv
ax₁ {one} {half} {forth} {forth} = triv
ax₁ {one} {half} {forth} {half} = triv
ax₁ {one} {half} {forth} {one} = triv
ax₁ {one} {half} {half} {zero} = triv
ax₁ {one} {half} {half} {forth} = triv
ax₁ {one} {half} {half} {half} = triv
ax₁ {one} {half} {half} {one} = triv
ax₁ {one} {half} {one} {zero} = triv
ax₁ {one} {half} {one} {forth} = triv
ax₁ {one} {half} {one} {half} = triv
ax₁ {one} {half} {one} {one} = triv
ax₁ {one} {one} {zero} {zero} = triv
ax₁ {one} {one} {zero} {forth} = triv
ax₁ {one} {one} {zero} {half} = triv
ax₁ {one} {one} {zero} {one} = triv
ax₁ {one} {one} {forth} {zero} = triv
ax₁ {one} {one} {forth} {forth} = triv
ax₁ {one} {one} {forth} {half} = triv
ax₁ {one} {one} {forth} {one} = triv
ax₁ {one} {one} {half} {zero} = triv
ax₁ {one} {one} {half} {forth} = triv
ax₁ {one} {one} {half} {half} = triv
ax₁ {one} {one} {half} {one} = triv
ax₁ {one} {one} {one} {zero} = triv
ax₁ {one} {one} {one} {forth} = triv
ax₁ {one} {one} {one} {half} = triv
ax₁ {one} {one} {one} {one} = triv

-- Filter
ax₂-inv : ∀{a b c} → (a ⊙F b) ▷F c ≤₄ a ⊙F (b ▷F c)
ax₂-inv {zero} {zero} {zero} = triv
ax₂-inv {zero} {zero} {forth} = triv
ax₂-inv {zero} {zero} {half} = triv
ax₂-inv {zero} {zero} {one} = triv
ax₂-inv {zero} {forth} {zero} = triv
ax₂-inv {zero} {forth} {forth} = triv
ax₂-inv {zero} {forth} {half} = triv
ax₂-inv {zero} {forth} {one} = triv
ax₂-inv {zero} {half} {zero} = triv
ax₂-inv {zero} {half} {forth} = triv
ax₂-inv {zero} {half} {half} = triv
ax₂-inv {zero} {half} {one} = triv
ax₂-inv {zero} {one} {zero} = triv
ax₂-inv {zero} {one} {forth} = triv
ax₂-inv {zero} {one} {half} = triv
ax₂-inv {zero} {one} {one} = triv
ax₂-inv {forth} {zero} {zero} = triv
ax₂-inv {forth} {zero} {forth} = triv
ax₂-inv {forth} {zero} {half} = triv
ax₂-inv {forth} {zero} {one} = triv
ax₂-inv {forth} {forth} {zero} = triv
ax₂-inv {forth} {forth} {forth} = triv
ax₂-inv {forth} {forth} {half} = triv
ax₂-inv {forth} {forth} {one} = triv
ax₂-inv {forth} {half} {zero} = triv
ax₂-inv {forth} {half} {forth} = triv
ax₂-inv {forth} {half} {half} = triv
ax₂-inv {forth} {half} {one} = triv
ax₂-inv {forth} {one} {zero} = triv
ax₂-inv {forth} {one} {forth} = triv
ax₂-inv {forth} {one} {half} = triv
ax₂-inv {forth} {one} {one} = triv
ax₂-inv {half} {zero} {zero} = triv
ax₂-inv {half} {zero} {forth} = triv
ax₂-inv {half} {zero} {half} = triv
ax₂-inv {half} {zero} {one} = triv
ax₂-inv {half} {forth} {zero} = triv
ax₂-inv {half} {forth} {forth} = triv
ax₂-inv {half} {forth} {half} = triv
ax₂-inv {half} {forth} {one} = triv
ax₂-inv {half} {half} {zero} = triv
ax₂-inv {half} {half} {forth} = triv
ax₂-inv {half} {half} {half} = triv
ax₂-inv {half} {half} {one} = triv
ax₂-inv {half} {one} {zero} = triv
ax₂-inv {half} {one} {forth} = triv
ax₂-inv {half} {one} {half} = triv
ax₂-inv {half} {one} {one} = triv
ax₂-inv {one} {zero} {zero} = triv
ax₂-inv {one} {zero} {forth} = triv
ax₂-inv {one} {zero} {half} = triv
ax₂-inv {one} {zero} {one} = triv
ax₂-inv {one} {forth} {zero} = triv
ax₂-inv {one} {forth} {forth} = triv
ax₂-inv {one} {forth} {half} = triv
ax₂-inv {one} {forth} {one} = triv
ax₂-inv {one} {half} {zero} = triv
ax₂-inv {one} {half} {forth} = triv
ax₂-inv {one} {half} {half} = triv
ax₂-inv {one} {half} {one} = triv
ax₂-inv {one} {one} {zero} = triv
ax₂-inv {one} {one} {forth} = triv
ax₂-inv {one} {one} {half} = triv
ax₂-inv {one} {one} {one} = triv

ax₂ : ∀{a b c} → a ⊙F (b ▷F c) ≤₄ (a ⊙F b) ▷F c
ax₂ {zero} {zero} {zero} = triv
ax₂ {zero} {zero} {forth} = triv
ax₂ {zero} {zero} {half} = triv
ax₂ {zero} {zero} {one} = triv
ax₂ {zero} {forth} {zero} = triv
ax₂ {zero} {forth} {forth} = triv
ax₂ {zero} {forth} {half} = triv
ax₂ {zero} {forth} {one} = triv
ax₂ {zero} {half} {zero} = triv
ax₂ {zero} {half} {forth} = triv
ax₂ {zero} {half} {half} = triv
ax₂ {zero} {half} {one} = triv
ax₂ {zero} {one} {zero} = triv
ax₂ {zero} {one} {forth} = triv
ax₂ {zero} {one} {half} = triv
ax₂ {zero} {one} {one} = triv
ax₂ {forth} {zero} {zero} = triv
ax₂ {forth} {zero} {forth} = triv
ax₂ {forth} {zero} {half} = triv
ax₂ {forth} {zero} {one} = triv
ax₂ {forth} {forth} {zero} = triv
ax₂ {forth} {forth} {forth} = triv
ax₂ {forth} {forth} {half} = triv
ax₂ {forth} {forth} {one} = triv
ax₂ {forth} {half} {zero} = triv
ax₂ {forth} {half} {forth} = triv
ax₂ {forth} {half} {half} = triv
ax₂ {forth} {half} {one} = triv
ax₂ {forth} {one} {zero} = triv
ax₂ {forth} {one} {forth} = triv
ax₂ {forth} {one} {half} = triv
ax₂ {forth} {one} {one} = triv
ax₂ {half} {zero} {zero} = triv
ax₂ {half} {zero} {forth} = triv
ax₂ {half} {zero} {half} = triv
ax₂ {half} {zero} {one} = triv
ax₂ {half} {forth} {zero} = triv
ax₂ {half} {forth} {forth} = triv
ax₂ {half} {forth} {half} = triv
ax₂ {half} {forth} {one} = triv
ax₂ {half} {half} {zero} = triv
ax₂ {half} {half} {forth} = triv
ax₂ {half} {half} {half} = triv
ax₂ {half} {half} {one} = triv
ax₂ {half} {one} {zero} = triv
ax₂ {half} {one} {forth} = triv
ax₂ {half} {one} {half} = triv
ax₂ {half} {one} {one} = triv
ax₂ {one} {zero} {zero} = triv
ax₂ {one} {zero} {forth} = triv
ax₂ {one} {zero} {half} = triv
ax₂ {one} {zero} {one} = triv
ax₂ {one} {forth} {zero} = triv
ax₂ {one} {forth} {forth} = triv
ax₂ {one} {forth} {half} = triv
ax₂ {one} {forth} {one} = triv
ax₂ {one} {half} {zero} = triv
ax₂ {one} {half} {forth} = triv
ax₂ {one} {half} {half} = triv
ax₂ {one} {half} {one} = triv
ax₂ {one} {one} {zero} = triv
ax₂ {one} {one} {forth} = triv
ax₂ {one} {one} {half} = triv
ax₂ {one} {one} {one} = triv

-- Filter
ax₃-inv : Σ[ a ∈ Four ](Σ[ b ∈ Four ](Σ[ c ∈ Four ](a ▷F (b ⊙F c) ≤₄ b ⊙F (a ▷F c) → ⊥ {lzero})))
ax₃-inv = half , (forth , (forth , id))

ax₃ : ∀{a b c} → b ⊙F (a ▷F c) ≤₄ a ▷F (b ⊙F c)
ax₃ {zero} {zero} {zero} = triv
ax₃ {zero} {zero} {forth} = triv
ax₃ {zero} {zero} {half} = triv
ax₃ {zero} {zero} {one} = triv
ax₃ {zero} {forth} {zero} = triv
ax₃ {zero} {forth} {forth} = triv
ax₃ {zero} {forth} {half} = triv
ax₃ {zero} {forth} {one} = triv
ax₃ {zero} {half} {zero} = triv
ax₃ {zero} {half} {forth} = triv
ax₃ {zero} {half} {half} = triv
ax₃ {zero} {half} {one} = triv
ax₃ {zero} {one} {zero} = triv
ax₃ {zero} {one} {forth} = triv
ax₃ {zero} {one} {half} = triv
ax₃ {zero} {one} {one} = triv
ax₃ {forth} {zero} {zero} = triv
ax₃ {forth} {zero} {forth} = triv
ax₃ {forth} {zero} {half} = triv
ax₃ {forth} {zero} {one} = triv
ax₃ {forth} {forth} {zero} = triv
ax₃ {forth} {forth} {forth} = triv
ax₃ {forth} {forth} {half} = triv
ax₃ {forth} {forth} {one} = triv
ax₃ {forth} {half} {zero} = triv
ax₃ {forth} {half} {forth} = triv
ax₃ {forth} {half} {half} = triv
ax₃ {forth} {half} {one} = triv
ax₃ {forth} {one} {zero} = triv
ax₃ {forth} {one} {forth} = triv
ax₃ {forth} {one} {half} = triv
ax₃ {forth} {one} {one} = triv
ax₃ {half} {zero} {zero} = triv
ax₃ {half} {zero} {forth} = triv
ax₃ {half} {zero} {half} = triv
ax₃ {half} {zero} {one} = triv
ax₃ {half} {forth} {zero} = triv
ax₃ {half} {forth} {forth} = triv
ax₃ {half} {forth} {half} = triv
ax₃ {half} {forth} {one} = triv
ax₃ {half} {half} {zero} = triv
ax₃ {half} {half} {forth} = triv
ax₃ {half} {half} {half} = triv
ax₃ {half} {half} {one} = triv
ax₃ {half} {one} {zero} = triv
ax₃ {half} {one} {forth} = triv
ax₃ {half} {one} {half} = triv
ax₃ {half} {one} {one} = triv
ax₃ {one} {zero} {zero} = triv
ax₃ {one} {zero} {forth} = triv
ax₃ {one} {zero} {half} = triv
ax₃ {one} {zero} {one} = triv
ax₃ {one} {forth} {zero} = triv
ax₃ {one} {forth} {forth} = triv
ax₃ {one} {forth} {half} = triv
ax₃ {one} {forth} {one} = triv
ax₃ {one} {half} {zero} = triv
ax₃ {one} {half} {forth} = triv
ax₃ {one} {half} {half} = triv
ax₃ {one} {half} {one} = triv
ax₃ {one} {one} {zero} = triv
ax₃ {one} {one} {forth} = triv
ax₃ {one} {one} {half} = triv
ax₃ {one} {one} {one} = triv

-- Filter

ax₄-inv : Σ[ a ∈ Four ](Σ[ b ∈ Four ](a ▷F b ≤₄ a ⊙F b  → ⊥ {lzero}))
ax₄-inv = half , (forth , id)

ax₄ : ∀{a b} → a ⊙F b ≤₄ a ▷F b
ax₄ {zero} {zero} = triv
ax₄ {zero} {forth} = triv
ax₄ {zero} {half} = triv
ax₄ {zero} {one} = triv
ax₄ {forth} {zero} = triv
ax₄ {forth} {forth} = triv
ax₄ {forth} {half}  = triv
ax₄ {forth} {one}   = triv
ax₄ {half} {zero} = triv
ax₄ {half} {forth} = triv
ax₄ {half} {half} = triv
ax₄ {half} {one} = triv
ax₄ {one} {zero} = triv
ax₄ {one} {forth} = triv
ax₄ {one} {half} = triv
ax₄ {one} {one} = triv

