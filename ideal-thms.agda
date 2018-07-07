module ideal-thms where

open import prelude
open import functions
open import quaternary-semantics
open import quaternary-thms
open import ideal-semantics

⊙I-zerol : ∀{x} → (zero ⊙I x) ≤₄ zero
⊙I-zerol {zero} = triv
⊙I-zerol {forth} = triv
⊙I-zerol {half} = triv
⊙I-zerol {one} = triv

⊙I-zeror : ∀{x} → (x ⊙I zero) ≤₄ zero
⊙I-zeror {zero} = triv
⊙I-zeror {forth} = triv
⊙I-zeror {half} = triv
⊙I-zeror {one} = triv

⊙I-contract : (∀{a} → (a ⊙I a) ≡ a) → ⊥ {lzero}
⊙I-contract p with p {forth} 
... | () 

⊙I-sym : ∀{a b} → a ⊙I b ≡ b ⊙I a
⊙I-sym {zero} {zero} = refl
⊙I-sym {zero} {forth} = refl
⊙I-sym {zero} {half} = refl
⊙I-sym {zero} {one} = refl
⊙I-sym {forth} {zero} = refl
⊙I-sym {forth} {forth} = refl
⊙I-sym {forth} {half} = refl
⊙I-sym {forth} {one} = refl
⊙I-sym {half} {zero} = refl
⊙I-sym {half} {forth} = refl
⊙I-sym {half} {half} = refl
⊙I-sym {half} {one} = refl
⊙I-sym {one} {zero} = refl
⊙I-sym {one} {forth} = refl
⊙I-sym {one} {half} = refl
⊙I-sym {one} {one} = refl

⊙I-assoc : ∀{a b c} → (a ⊙I b) ⊙I c ≡ a ⊙I (b ⊙I c)
⊙I-assoc {zero} {zero} {zero} = refl
⊙I-assoc {zero} {zero} {forth} = refl
⊙I-assoc {zero} {zero} {half} = refl
⊙I-assoc {zero} {zero} {one} = refl
⊙I-assoc {zero} {forth} {zero} = refl
⊙I-assoc {zero} {forth} {forth} = refl
⊙I-assoc {zero} {forth} {half} = refl
⊙I-assoc {zero} {forth} {one} = refl
⊙I-assoc {zero} {half} {zero} = refl
⊙I-assoc {zero} {half} {forth} = refl
⊙I-assoc {zero} {half} {half} = refl
⊙I-assoc {zero} {half} {one} = refl
⊙I-assoc {zero} {one} {zero} = refl
⊙I-assoc {zero} {one} {forth} = refl
⊙I-assoc {zero} {one} {half} = refl
⊙I-assoc {zero} {one} {one} = refl
⊙I-assoc {forth} {zero} {zero} = refl
⊙I-assoc {forth} {zero} {forth} = refl
⊙I-assoc {forth} {zero} {half} = refl
⊙I-assoc {forth} {zero} {one} = refl
⊙I-assoc {forth} {forth} {zero} = refl
⊙I-assoc {forth} {forth} {forth} = refl
⊙I-assoc {forth} {forth} {half} = refl
⊙I-assoc {forth} {forth} {one} = refl
⊙I-assoc {forth} {half} {zero} = refl
⊙I-assoc {forth} {half} {forth} = refl
⊙I-assoc {forth} {half} {half} = refl
⊙I-assoc {forth} {half} {one} = refl
⊙I-assoc {forth} {one} {zero} = refl
⊙I-assoc {forth} {one} {forth} = refl
⊙I-assoc {forth} {one} {half} = refl
⊙I-assoc {forth} {one} {one} = refl
⊙I-assoc {half} {zero} {zero} = refl
⊙I-assoc {half} {zero} {forth} = refl
⊙I-assoc {half} {zero} {half} = refl
⊙I-assoc {half} {zero} {one} = refl
⊙I-assoc {half} {forth} {zero} = refl
⊙I-assoc {half} {forth} {forth} = refl
⊙I-assoc {half} {forth} {half} = refl
⊙I-assoc {half} {forth} {one} = refl
⊙I-assoc {half} {half} {zero} = refl
⊙I-assoc {half} {half} {forth} = refl
⊙I-assoc {half} {half} {half} = refl
⊙I-assoc {half} {half} {one} = refl
⊙I-assoc {half} {one} {zero} = refl
⊙I-assoc {half} {one} {forth} = refl
⊙I-assoc {half} {one} {half} = refl
⊙I-assoc {half} {one} {one} = refl
⊙I-assoc {one} {zero} {zero} = refl
⊙I-assoc {one} {zero} {forth} = refl
⊙I-assoc {one} {zero} {half} = refl
⊙I-assoc {one} {zero} {one} = refl
⊙I-assoc {one} {forth} {zero} = refl
⊙I-assoc {one} {forth} {forth} = refl
⊙I-assoc {one} {forth} {half} = refl
⊙I-assoc {one} {forth} {one} = refl
⊙I-assoc {one} {half} {zero} = refl
⊙I-assoc {one} {half} {forth} = refl
⊙I-assoc {one} {half} {half} = refl
⊙I-assoc {one} {half} {one} = refl
⊙I-assoc {one} {one} {zero} = refl
⊙I-assoc {one} {one} {forth} = refl
⊙I-assoc {one} {one} {half} = refl
⊙I-assoc {one} {one} {one} = refl

⊙I-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ⊙I b) ≤₄ (c ⊙I d)
⊙I-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
⊙I-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
⊙I-func {zero} {zero} {zero} {half} p₁ p₂ = triv
⊙I-func {zero} {zero} {zero} {one} p₁ p₂ = triv
⊙I-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
⊙I-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
⊙I-func {zero} {zero} {forth} {half} p₁ p₂ = triv
⊙I-func {zero} {zero} {forth} {one} p₁ p₂ = triv
⊙I-func {zero} {zero} {half} {zero} p₁ p₂ = triv
⊙I-func {zero} {zero} {half} {forth} p₁ p₂ = triv
⊙I-func {zero} {zero} {half} {half} p₁ p₂ = triv
⊙I-func {zero} {zero} {half} {one} p₁ p₂ = triv
⊙I-func {zero} {zero} {one} {zero} p₁ p₂ = triv
⊙I-func {zero} {zero} {one} {forth} p₁ p₂ = triv
⊙I-func {zero} {zero} {one} {half} p₁ p₂ = triv
⊙I-func {zero} {zero} {one} {one} p₁ p₂ = triv
⊙I-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
⊙I-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
⊙I-func {zero} {forth} {zero} {half} p₁ p₂ = triv
⊙I-func {zero} {forth} {zero} {one} p₁ p₂ = triv
⊙I-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
⊙I-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
⊙I-func {zero} {forth} {forth} {half} p₁ p₂ = triv
⊙I-func {zero} {forth} {forth} {one} p₁ p₂ = triv
⊙I-func {zero} {forth} {half} {zero} p₁ p₂ = triv
⊙I-func {zero} {forth} {half} {forth} p₁ p₂ = triv
⊙I-func {zero} {forth} {half} {half} p₁ p₂ = triv
⊙I-func {zero} {forth} {half} {one} p₁ p₂ = triv
⊙I-func {zero} {forth} {one} {zero} p₁ p₂ = triv
⊙I-func {zero} {forth} {one} {forth} p₁ p₂ = triv
⊙I-func {zero} {forth} {one} {half} p₁ p₂ = triv
⊙I-func {zero} {forth} {one} {one} p₁ p₂ = triv
⊙I-func {zero} {half} {zero} {zero} p₁ p₂ = triv
⊙I-func {zero} {half} {zero} {forth} p₁ p₂ = triv
⊙I-func {zero} {half} {zero} {half} p₁ p₂ = triv
⊙I-func {zero} {half} {zero} {one} p₁ p₂ = triv
⊙I-func {zero} {half} {forth} {zero} p₁ p₂ = triv
⊙I-func {zero} {half} {forth} {forth} p₁ p₂ = triv
⊙I-func {zero} {half} {forth} {half} p₁ p₂ = triv
⊙I-func {zero} {half} {forth} {one} p₁ p₂ = triv
⊙I-func {zero} {half} {half} {zero} p₁ p₂ = triv
⊙I-func {zero} {half} {half} {forth} p₁ p₂ = triv
⊙I-func {zero} {half} {half} {half} p₁ p₂ = triv
⊙I-func {zero} {half} {half} {one} p₁ p₂ = triv
⊙I-func {zero} {half} {one} {zero} p₁ p₂ = triv
⊙I-func {zero} {half} {one} {forth} p₁ p₂ = triv
⊙I-func {zero} {half} {one} {half} p₁ p₂ = triv
⊙I-func {zero} {half} {one} {one} p₁ p₂ = triv
⊙I-func {zero} {one} {zero} {zero} p₁ p₂ = triv
⊙I-func {zero} {one} {zero} {forth} p₁ p₂ = triv
⊙I-func {zero} {one} {zero} {half} p₁ p₂ = triv
⊙I-func {zero} {one} {zero} {one} p₁ p₂ = triv
⊙I-func {zero} {one} {forth} {zero} p₁ p₂ = triv
⊙I-func {zero} {one} {forth} {forth} p₁ p₂ = triv
⊙I-func {zero} {one} {forth} {half} p₁ p₂ = triv
⊙I-func {zero} {one} {forth} {one} p₁ p₂ = triv
⊙I-func {zero} {one} {half} {zero} p₁ p₂ = triv
⊙I-func {zero} {one} {half} {forth} p₁ p₂ = triv
⊙I-func {zero} {one} {half} {half} p₁ p₂ = triv
⊙I-func {zero} {one} {half} {one} p₁ p₂ = triv
⊙I-func {zero} {one} {one} {zero} p₁ p₂ = triv
⊙I-func {zero} {one} {one} {forth} p₁ p₂ = triv
⊙I-func {zero} {one} {one} {half} p₁ p₂ = triv
⊙I-func {zero} {one} {one} {one} p₁ p₂ = triv
⊙I-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
⊙I-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
⊙I-func {forth} {zero} {zero} {half} p₁ p₂ = triv
⊙I-func {forth} {zero} {zero} {one} p₁ p₂ = triv
⊙I-func {forth} {zero} {forth} {zero} () ()
⊙I-func {forth} {zero} {forth} {forth} () p₂
⊙I-func {forth} {zero} {forth} {half} () p₂
⊙I-func {forth} {zero} {forth} {one} () p₂
⊙I-func {forth} {zero} {half} {zero} () ()
⊙I-func {forth} {zero} {half} {forth} () ()
⊙I-func {forth} {zero} {half} {half} () p₂
⊙I-func {forth} {zero} {half} {one} () p₂
⊙I-func {forth} {zero} {one} {zero} () ()
⊙I-func {forth} {zero} {one} {forth} () ()
⊙I-func {forth} {zero} {one} {half} () ()
⊙I-func {forth} {zero} {one} {one} () p₂
⊙I-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
⊙I-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
⊙I-func {forth} {forth} {zero} {half} p₁ p₂ = triv
⊙I-func {forth} {forth} {zero} {one} p₁ p₂ = triv
⊙I-func {forth} {forth} {forth} {zero} p₁ ()
⊙I-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
⊙I-func {forth} {forth} {forth} {half} p₁ p₂ = triv
⊙I-func {forth} {forth} {forth} {one} p₁ p₂ = triv
⊙I-func {forth} {forth} {half} {zero} p₁ ()
⊙I-func {forth} {forth} {half} {forth} p₁ p₂ = triv
⊙I-func {forth} {forth} {half} {half} p₁ p₂ = triv
⊙I-func {forth} {forth} {half} {one} p₁ p₂ = triv
⊙I-func {forth} {forth} {one} {zero} p₁ ()
⊙I-func {forth} {forth} {one} {forth} p₁ p₂ = triv
⊙I-func {forth} {forth} {one} {half} p₁ p₂ = triv
⊙I-func {forth} {forth} {one} {one} p₁ p₂ = triv
⊙I-func {forth} {half} {zero} {zero} p₁ p₂ = triv
⊙I-func {forth} {half} {zero} {forth} p₁ p₂ = triv
⊙I-func {forth} {half} {zero} {half} p₁ p₂ = triv
⊙I-func {forth} {half} {zero} {one} p₁ p₂ = triv
⊙I-func {forth} {half} {forth} {zero} p₁ ()
⊙I-func {forth} {half} {forth} {forth} p₁ p₂ = triv
⊙I-func {forth} {half} {forth} {half} p₁ p₂ = triv
⊙I-func {forth} {half} {forth} {one} p₁ p₂ = triv
⊙I-func {forth} {half} {half} {zero} p₁ ()
⊙I-func {forth} {half} {half} {forth} p₁ p₂ = triv
⊙I-func {forth} {half} {half} {half} p₁ p₂ = triv
⊙I-func {forth} {half} {half} {one} p₁ p₂ = triv
⊙I-func {forth} {half} {one} {zero} p₁ ()
⊙I-func {forth} {half} {one} {forth} p₁ p₂ = triv
⊙I-func {forth} {half} {one} {half} p₁ p₂ = triv
⊙I-func {forth} {half} {one} {one} p₁ p₂ = triv
⊙I-func {forth} {one} {zero} {zero} p₁ p₂ = triv
⊙I-func {forth} {one} {zero} {forth} p₁ p₂ = triv
⊙I-func {forth} {one} {zero} {half} p₁ p₂ = triv
⊙I-func {forth} {one} {zero} {one} p₁ p₂ = triv
⊙I-func {forth} {one} {forth} {zero} p₁ ()
⊙I-func {forth} {one} {forth} {forth} p₁ p₂ = triv
⊙I-func {forth} {one} {forth} {half} p₁ p₂ = triv
⊙I-func {forth} {one} {forth} {one} p₁ p₂ = triv
⊙I-func {forth} {one} {half} {zero} p₁ ()
⊙I-func {forth} {one} {half} {forth} p₁ p₂ = triv
⊙I-func {forth} {one} {half} {half} p₁ p₂ = triv
⊙I-func {forth} {one} {half} {one} p₁ p₂ = triv
⊙I-func {forth} {one} {one} {zero} p₁ ()
⊙I-func {forth} {one} {one} {forth} p₁ p₂ = triv
⊙I-func {forth} {one} {one} {half} p₁ p₂ = triv
⊙I-func {forth} {one} {one} {one} p₁ p₂ = triv
⊙I-func {half} {zero} {zero} {zero} p₁ p₂ = triv
⊙I-func {half} {zero} {zero} {forth} p₁ p₂ = triv
⊙I-func {half} {zero} {zero} {half} p₁ p₂ = triv
⊙I-func {half} {zero} {zero} {one} p₁ p₂ = triv
⊙I-func {half} {zero} {forth} {zero} () ()
⊙I-func {half} {zero} {forth} {forth} () p₂
⊙I-func {half} {zero} {forth} {half} () p₂
⊙I-func {half} {zero} {forth} {one} () p₂
⊙I-func {half} {zero} {half} {zero} () ()
⊙I-func {half} {zero} {half} {forth} () ()
⊙I-func {half} {zero} {half} {half} () p₂
⊙I-func {half} {zero} {half} {one} () p₂
⊙I-func {half} {zero} {one} {zero} () ()
⊙I-func {half} {zero} {one} {forth} () ()
⊙I-func {half} {zero} {one} {half} () ()
⊙I-func {half} {zero} {one} {one} () p₂
⊙I-func {half} {forth} {zero} {zero} p₁ p₂ = triv
⊙I-func {half} {forth} {zero} {forth} p₁ p₂ = triv
⊙I-func {half} {forth} {zero} {half} p₁ p₂ = triv
⊙I-func {half} {forth} {zero} {one} p₁ p₂ = triv
⊙I-func {half} {forth} {forth} {zero} () ()
⊙I-func {half} {forth} {forth} {forth} p₁ p₂ = triv
⊙I-func {half} {forth} {forth} {half} p₁ p₂ = triv
⊙I-func {half} {forth} {forth} {one} p₁ p₂ = triv
⊙I-func {half} {forth} {half} {zero} () ()
⊙I-func {half} {forth} {half} {forth} p₁ p₂ = triv
⊙I-func {half} {forth} {half} {half} p₁ p₂ = triv
⊙I-func {half} {forth} {half} {one} p₁ p₂ = triv
⊙I-func {half} {forth} {one} {zero} () ()
⊙I-func {half} {forth} {one} {forth} () ()
⊙I-func {half} {forth} {one} {half} () ()
⊙I-func {half} {forth} {one} {one} () p₂
⊙I-func {half} {half} {zero} {zero} p₁ p₂ = triv
⊙I-func {half} {half} {zero} {forth} p₁ p₂ = triv
⊙I-func {half} {half} {zero} {half} p₁ p₂ = triv
⊙I-func {half} {half} {zero} {one} p₁ p₂ = triv
⊙I-func {half} {half} {forth} {zero} p₁ ()
⊙I-func {half} {half} {forth} {forth} p₁ p₂ = triv
⊙I-func {half} {half} {forth} {half} p₁ p₂ = triv
⊙I-func {half} {half} {forth} {one} p₁ p₂ = triv
⊙I-func {half} {half} {half} {zero} p₁ ()
⊙I-func {half} {half} {half} {forth} p₁ p₂ = triv
⊙I-func {half} {half} {half} {half} p₁ p₂ = triv
⊙I-func {half} {half} {half} {one} p₁ p₂ = triv
⊙I-func {half} {half} {one} {zero} p₁ ()
⊙I-func {half} {half} {one} {forth} p₁ ()
⊙I-func {half} {half} {one} {half} p₁ ()
⊙I-func {half} {half} {one} {one} p₁ p₂ = triv
⊙I-func {half} {one} {zero} {zero} p₁ p₂ = triv
⊙I-func {half} {one} {zero} {forth} p₁ p₂ = triv
⊙I-func {half} {one} {zero} {half} p₁ p₂ = triv
⊙I-func {half} {one} {zero} {one} p₁ p₂ = triv
⊙I-func {half} {one} {forth} {zero} p₁ ()
⊙I-func {half} {one} {forth} {forth} p₁ p₂ = triv
⊙I-func {half} {one} {forth} {half} p₁ p₂ = triv
⊙I-func {half} {one} {forth} {one} p₁ p₂ = triv
⊙I-func {half} {one} {half} {zero} p₁ ()
⊙I-func {half} {one} {half} {forth} p₁ p₂ = triv
⊙I-func {half} {one} {half} {half} p₁ p₂ = triv
⊙I-func {half} {one} {half} {one} p₁ p₂ = triv
⊙I-func {half} {one} {one} {zero} p₁ ()
⊙I-func {half} {one} {one} {forth} p₁ ()
⊙I-func {half} {one} {one} {half} p₁ p₂ = triv
⊙I-func {half} {one} {one} {one} p₁ p₂ = triv
⊙I-func {one} {zero} {zero} {zero} p₁ p₂ = triv
⊙I-func {one} {zero} {zero} {forth} p₁ p₂ = triv
⊙I-func {one} {zero} {zero} {half} p₁ p₂ = triv
⊙I-func {one} {zero} {zero} {one} p₁ p₂ = triv
⊙I-func {one} {zero} {forth} {zero} () ()
⊙I-func {one} {zero} {forth} {forth} () p₂
⊙I-func {one} {zero} {forth} {half} () p₂
⊙I-func {one} {zero} {forth} {one} () p₂
⊙I-func {one} {zero} {half} {zero} () ()
⊙I-func {one} {zero} {half} {forth} () ()
⊙I-func {one} {zero} {half} {half} () p₂
⊙I-func {one} {zero} {half} {one} () p₂
⊙I-func {one} {zero} {one} {zero} () ()
⊙I-func {one} {zero} {one} {forth} () ()
⊙I-func {one} {zero} {one} {half} () ()
⊙I-func {one} {zero} {one} {one} () p₂
⊙I-func {one} {forth} {zero} {zero} p₁ p₂ = triv
⊙I-func {one} {forth} {zero} {forth} p₁ p₂ = triv
⊙I-func {one} {forth} {zero} {half} p₁ p₂ = triv
⊙I-func {one} {forth} {zero} {one} p₁ p₂ = triv
⊙I-func {one} {forth} {forth} {zero} () ()
⊙I-func {one} {forth} {forth} {forth} p₁ p₂ = triv
⊙I-func {one} {forth} {forth} {half} p₁ p₂ = triv
⊙I-func {one} {forth} {forth} {one} p₁ p₂ = triv
⊙I-func {one} {forth} {half} {zero} () ()
⊙I-func {one} {forth} {half} {forth} () ()
⊙I-func {one} {forth} {half} {half} () p₂
⊙I-func {one} {forth} {half} {one} () p₂
⊙I-func {one} {forth} {one} {zero} () ()
⊙I-func {one} {forth} {one} {forth} () ()
⊙I-func {one} {forth} {one} {half} () ()
⊙I-func {one} {forth} {one} {one} () p₂
⊙I-func {one} {half} {zero} {zero} p₁ p₂ = triv
⊙I-func {one} {half} {zero} {forth} p₁ p₂ = triv
⊙I-func {one} {half} {zero} {half} p₁ p₂ = triv
⊙I-func {one} {half} {zero} {one} p₁ p₂ = triv
⊙I-func {one} {half} {forth} {zero} () ()
⊙I-func {one} {half} {forth} {forth} p₁ p₂ = triv
⊙I-func {one} {half} {forth} {half} () p₂
⊙I-func {one} {half} {forth} {one} p₁ p₂ = triv
⊙I-func {one} {half} {half} {zero} () ()
⊙I-func {one} {half} {half} {forth} () ()
⊙I-func {one} {half} {half} {half} () p₂
⊙I-func {one} {half} {half} {one} p₁ p₂ = triv
⊙I-func {one} {half} {one} {zero} () ()
⊙I-func {one} {half} {one} {forth} () ()
⊙I-func {one} {half} {one} {half} () ()
⊙I-func {one} {half} {one} {one} () p₂
⊙I-func {one} {one} {zero} {zero} p₁ p₂ = triv
⊙I-func {one} {one} {zero} {forth} p₁ p₂ = triv
⊙I-func {one} {one} {zero} {half} p₁ p₂ = triv
⊙I-func {one} {one} {zero} {one} p₁ p₂ = triv
⊙I-func {one} {one} {forth} {zero} p₁ ()
⊙I-func {one} {one} {forth} {forth} p₁ p₂ = triv
⊙I-func {one} {one} {forth} {half} p₁ p₂ = triv
⊙I-func {one} {one} {forth} {one} p₁ p₂ = triv
⊙I-func {one} {one} {half} {zero} p₁ ()
⊙I-func {one} {one} {half} {forth} p₁ ()
⊙I-func {one} {one} {half} {half} p₁ p₂ = triv
⊙I-func {one} {one} {half} {one} p₁ p₂ = triv
⊙I-func {one} {one} {one} {zero} p₁ ()
⊙I-func {one} {one} {one} {forth} p₁ ()
⊙I-func {one} {one} {one} {half} p₁ ()
⊙I-func {one} {one} {one} {one} p₁ p₂ = triv

⊙I-distl : {a b c : Four} → (a ⊙I (b ⊔I c)) ≡ ((a ⊙I b) ⊔I (a ⊙I c))
⊙I-distl {zero} {zero} {zero} = refl
⊙I-distl {zero} {zero} {forth} = refl
⊙I-distl {zero} {zero} {half} = refl
⊙I-distl {zero} {zero} {one} = refl
⊙I-distl {zero} {forth} {zero} = refl
⊙I-distl {zero} {forth} {forth} = refl
⊙I-distl {zero} {forth} {half} = refl
⊙I-distl {zero} {forth} {one} = refl
⊙I-distl {zero} {half} {zero} = refl
⊙I-distl {zero} {half} {forth} = refl
⊙I-distl {zero} {half} {half} = refl
⊙I-distl {zero} {half} {one} = refl
⊙I-distl {zero} {one} {zero} = refl
⊙I-distl {zero} {one} {forth} = refl
⊙I-distl {zero} {one} {half} = refl
⊙I-distl {zero} {one} {one} = refl
⊙I-distl {forth} {zero} {zero} = refl
⊙I-distl {forth} {zero} {forth} = refl
⊙I-distl {forth} {zero} {half} = refl
⊙I-distl {forth} {zero} {one} = refl
⊙I-distl {forth} {forth} {zero} = refl
⊙I-distl {forth} {forth} {forth} = refl
⊙I-distl {forth} {forth} {half} = refl
⊙I-distl {forth} {forth} {one} = refl
⊙I-distl {forth} {half} {zero} = refl
⊙I-distl {forth} {half} {forth} = refl
⊙I-distl {forth} {half} {half} = refl
⊙I-distl {forth} {half} {one} = refl
⊙I-distl {forth} {one} {zero} = refl
⊙I-distl {forth} {one} {forth} = refl
⊙I-distl {forth} {one} {half} = refl
⊙I-distl {forth} {one} {one} = refl
⊙I-distl {half} {zero} {zero} = refl
⊙I-distl {half} {zero} {forth} = refl
⊙I-distl {half} {zero} {half} = refl
⊙I-distl {half} {zero} {one} = refl
⊙I-distl {half} {forth} {zero} = refl
⊙I-distl {half} {forth} {forth} = refl
⊙I-distl {half} {forth} {half} = refl
⊙I-distl {half} {forth} {one} = refl
⊙I-distl {half} {half} {zero} = refl
⊙I-distl {half} {half} {forth} = refl
⊙I-distl {half} {half} {half} = refl
⊙I-distl {half} {half} {one} = refl
⊙I-distl {half} {one} {zero} = refl
⊙I-distl {half} {one} {forth} = refl
⊙I-distl {half} {one} {half} = refl
⊙I-distl {half} {one} {one} = refl
⊙I-distl {one} {zero} {zero} = refl
⊙I-distl {one} {zero} {forth} = refl
⊙I-distl {one} {zero} {half} = refl
⊙I-distl {one} {zero} {one} = refl
⊙I-distl {one} {forth} {zero} = refl
⊙I-distl {one} {forth} {forth} = refl
⊙I-distl {one} {forth} {half} = refl
⊙I-distl {one} {forth} {one} = refl
⊙I-distl {one} {half} {zero} = refl
⊙I-distl {one} {half} {forth} = refl
⊙I-distl {one} {half} {half} = refl
⊙I-distl {one} {half} {one} = refl
⊙I-distl {one} {one} {zero} = refl
⊙I-distl {one} {one} {forth} = refl
⊙I-distl {one} {one} {half} = refl
⊙I-distl {one} {one} {one} = refl

⊙I-distr : {a b c : Four} → ((a ⊔I b) ⊙I c) ≡ ((a ⊙I c) ⊔I (b ⊙I c))
⊙I-distr {zero} {zero} {zero} = refl
⊙I-distr {zero} {zero} {forth} = refl
⊙I-distr {zero} {zero} {half} = refl
⊙I-distr {zero} {zero} {one} = refl
⊙I-distr {zero} {forth} {zero} = refl
⊙I-distr {zero} {forth} {forth} = refl
⊙I-distr {zero} {forth} {half} = refl
⊙I-distr {zero} {forth} {one} = refl
⊙I-distr {zero} {half} {zero} = refl
⊙I-distr {zero} {half} {forth} = refl
⊙I-distr {zero} {half} {half} = refl
⊙I-distr {zero} {half} {one} = refl
⊙I-distr {zero} {one} {zero} = refl
⊙I-distr {zero} {one} {forth} = refl
⊙I-distr {zero} {one} {half} = refl
⊙I-distr {zero} {one} {one} = refl
⊙I-distr {forth} {zero} {zero} = refl
⊙I-distr {forth} {zero} {forth} = refl
⊙I-distr {forth} {zero} {half} = refl
⊙I-distr {forth} {zero} {one} = refl
⊙I-distr {forth} {forth} {zero} = refl
⊙I-distr {forth} {forth} {forth} = refl
⊙I-distr {forth} {forth} {half} = refl
⊙I-distr {forth} {forth} {one} = refl
⊙I-distr {forth} {half} {zero} = refl
⊙I-distr {forth} {half} {forth} = refl
⊙I-distr {forth} {half} {half} = refl
⊙I-distr {forth} {half} {one} = refl
⊙I-distr {forth} {one} {zero} = refl
⊙I-distr {forth} {one} {forth} = refl
⊙I-distr {forth} {one} {half} = refl
⊙I-distr {forth} {one} {one} = refl
⊙I-distr {half} {zero} {zero} = refl
⊙I-distr {half} {zero} {forth} = refl
⊙I-distr {half} {zero} {half} = refl
⊙I-distr {half} {zero} {one} = refl
⊙I-distr {half} {forth} {zero} = refl
⊙I-distr {half} {forth} {forth} = refl
⊙I-distr {half} {forth} {half} = refl
⊙I-distr {half} {forth} {one} = refl
⊙I-distr {half} {half} {zero} = refl
⊙I-distr {half} {half} {forth} = refl
⊙I-distr {half} {half} {half} = refl
⊙I-distr {half} {half} {one} = refl
⊙I-distr {half} {one} {zero} = refl
⊙I-distr {half} {one} {forth} = refl
⊙I-distr {half} {one} {half} = refl
⊙I-distr {half} {one} {one} = refl
⊙I-distr {one} {zero} {zero} = refl
⊙I-distr {one} {zero} {forth} = refl
⊙I-distr {one} {zero} {half} = refl
⊙I-distr {one} {zero} {one} = refl
⊙I-distr {one} {forth} {zero} = refl
⊙I-distr {one} {forth} {forth} = refl
⊙I-distr {one} {forth} {half} = refl
⊙I-distr {one} {forth} {one} = refl
⊙I-distr {one} {half} {zero} = refl
⊙I-distr {one} {half} {forth} = refl
⊙I-distr {one} {half} {half} = refl
⊙I-distr {one} {half} {one} = refl
⊙I-distr {one} {one} {zero} = refl
⊙I-distr {one} {one} {forth} = refl
⊙I-distr {one} {one} {half} = refl
⊙I-distr {one} {one} {one} = refl

▷I-sym : (∀{a b} → (a ▷I b) ≡ (b ▷I a)) → ⊥ {lzero}
▷I-sym p with p {forth}{half}
... | () 

▷I-contract : (∀{a} → (a ▷I a) ≡ a) → ⊥ {lzero}
▷I-contract p with p {one}
... | () 

▷I-zerol : ∀{x} → (zero ▷I x) ≤₄ zero
▷I-zerol {zero} = triv
▷I-zerol {forth} = triv
▷I-zerol {half} = triv
▷I-zerol {one} = triv

▷I-zeror : ∀{x} → (x ▷I zero) ≤₄ zero
▷I-zeror {zero} = triv
▷I-zeror {forth} = triv
▷I-zeror {half} = triv
▷I-zeror {one} = triv

▷I-assoc : {a b c : Four} →  a ▷I (b ▷I c) ≡ (a ▷I b) ▷I c
▷I-assoc {zero} {zero} {zero} = refl
▷I-assoc {zero} {zero} {forth} = refl
▷I-assoc {zero} {zero} {half} = refl
▷I-assoc {zero} {zero} {one} = refl
▷I-assoc {zero} {forth} {zero} = refl
▷I-assoc {zero} {forth} {forth} = refl
▷I-assoc {zero} {forth} {half} = refl
▷I-assoc {zero} {forth} {one} = refl
▷I-assoc {zero} {half} {zero} = refl
▷I-assoc {zero} {half} {forth} = refl
▷I-assoc {zero} {half} {half} = refl
▷I-assoc {zero} {half} {one} = refl
▷I-assoc {zero} {one} {zero} = refl
▷I-assoc {zero} {one} {forth} = refl
▷I-assoc {zero} {one} {half} = refl
▷I-assoc {zero} {one} {one} = refl
▷I-assoc {forth} {zero} {zero} = refl
▷I-assoc {forth} {zero} {forth} = refl
▷I-assoc {forth} {zero} {half} = refl
▷I-assoc {forth} {zero} {one} = refl
▷I-assoc {forth} {forth} {zero} = refl
▷I-assoc {forth} {forth} {forth} = refl
▷I-assoc {forth} {forth} {half} = refl
▷I-assoc {forth} {forth} {one} = refl
▷I-assoc {forth} {half} {zero} = refl
▷I-assoc {forth} {half} {forth} = refl
▷I-assoc {forth} {half} {half} = refl
▷I-assoc {forth} {half} {one} = refl
▷I-assoc {forth} {one} {zero} = refl
▷I-assoc {forth} {one} {forth} = refl
▷I-assoc {forth} {one} {half} = refl
▷I-assoc {forth} {one} {one} = refl
▷I-assoc {half} {zero} {zero} = refl
▷I-assoc {half} {zero} {forth} = refl
▷I-assoc {half} {zero} {half} = refl
▷I-assoc {half} {zero} {one} = refl
▷I-assoc {half} {forth} {zero} = refl
▷I-assoc {half} {forth} {forth} = refl
▷I-assoc {half} {forth} {half} = refl
▷I-assoc {half} {forth} {one} = refl
▷I-assoc {half} {half} {zero} = refl
▷I-assoc {half} {half} {forth} = refl
▷I-assoc {half} {half} {half} = refl
▷I-assoc {half} {half} {one} = refl
▷I-assoc {half} {one} {zero} = refl
▷I-assoc {half} {one} {forth} = refl
▷I-assoc {half} {one} {half} = refl
▷I-assoc {half} {one} {one} = refl
▷I-assoc {one} {zero} {zero} = refl
▷I-assoc {one} {zero} {forth} = refl
▷I-assoc {one} {zero} {half} = refl
▷I-assoc {one} {zero} {one} = refl
▷I-assoc {one} {forth} {zero} = refl
▷I-assoc {one} {forth} {forth} = refl
▷I-assoc {one} {forth} {half} = refl
▷I-assoc {one} {forth} {one} = refl
▷I-assoc {one} {half} {zero} = refl
▷I-assoc {one} {half} {forth} = refl
▷I-assoc {one} {half} {half} = refl
▷I-assoc {one} {half} {one} = refl
▷I-assoc {one} {one} {zero} = refl
▷I-assoc {one} {one} {forth} = refl
▷I-assoc {one} {one} {half} = refl
▷I-assoc {one} {one} {one} = refl

▷I-func : {a c b d : Four} → a ≤₄ c → b ≤₄ d → (a ▷I b) ≤₄ (c ▷I d)
▷I-func {zero} {zero} {zero} {zero} p₁ p₂ = triv
▷I-func {zero} {zero} {zero} {forth} p₁ p₂ = triv
▷I-func {zero} {zero} {zero} {half} p₁ p₂ = triv
▷I-func {zero} {zero} {zero} {one} p₁ p₂ = triv
▷I-func {zero} {zero} {forth} {zero} p₁ p₂ = triv
▷I-func {zero} {zero} {forth} {forth} p₁ p₂ = triv
▷I-func {zero} {zero} {forth} {half} p₁ p₂ = triv
▷I-func {zero} {zero} {forth} {one} p₁ p₂ = triv
▷I-func {zero} {zero} {half} {zero} p₁ p₂ = triv
▷I-func {zero} {zero} {half} {forth} p₁ p₂ = triv
▷I-func {zero} {zero} {half} {half} p₁ p₂ = triv
▷I-func {zero} {zero} {half} {one} p₁ p₂ = triv
▷I-func {zero} {zero} {one} {zero} p₁ p₂ = triv
▷I-func {zero} {zero} {one} {forth} p₁ p₂ = triv
▷I-func {zero} {zero} {one} {half} p₁ p₂ = triv
▷I-func {zero} {zero} {one} {one} p₁ p₂ = triv
▷I-func {zero} {forth} {zero} {zero} p₁ p₂ = triv
▷I-func {zero} {forth} {zero} {forth} p₁ p₂ = triv
▷I-func {zero} {forth} {zero} {half} p₁ p₂ = triv
▷I-func {zero} {forth} {zero} {one} p₁ p₂ = triv
▷I-func {zero} {forth} {forth} {zero} p₁ p₂ = triv
▷I-func {zero} {forth} {forth} {forth} p₁ p₂ = triv
▷I-func {zero} {forth} {forth} {half} p₁ p₂ = triv
▷I-func {zero} {forth} {forth} {one} p₁ p₂ = triv
▷I-func {zero} {forth} {half} {zero} p₁ p₂ = triv
▷I-func {zero} {forth} {half} {forth} p₁ p₂ = triv
▷I-func {zero} {forth} {half} {half} p₁ p₂ = triv
▷I-func {zero} {forth} {half} {one} p₁ p₂ = triv
▷I-func {zero} {forth} {one} {zero} p₁ p₂ = triv
▷I-func {zero} {forth} {one} {forth} p₁ p₂ = triv
▷I-func {zero} {forth} {one} {half} p₁ p₂ = triv
▷I-func {zero} {forth} {one} {one} p₁ p₂ = triv
▷I-func {zero} {half} {zero} {zero} p₁ p₂ = triv
▷I-func {zero} {half} {zero} {forth} p₁ p₂ = triv
▷I-func {zero} {half} {zero} {half} p₁ p₂ = triv
▷I-func {zero} {half} {zero} {one} p₁ p₂ = triv
▷I-func {zero} {half} {forth} {zero} p₁ p₂ = triv
▷I-func {zero} {half} {forth} {forth} p₁ p₂ = triv
▷I-func {zero} {half} {forth} {half} p₁ p₂ = triv
▷I-func {zero} {half} {forth} {one} p₁ p₂ = triv
▷I-func {zero} {half} {half} {zero} p₁ p₂ = triv
▷I-func {zero} {half} {half} {forth} p₁ p₂ = triv
▷I-func {zero} {half} {half} {half} p₁ p₂ = triv
▷I-func {zero} {half} {half} {one} p₁ p₂ = triv
▷I-func {zero} {half} {one} {zero} p₁ p₂ = triv
▷I-func {zero} {half} {one} {forth} p₁ p₂ = triv
▷I-func {zero} {half} {one} {half} p₁ p₂ = triv
▷I-func {zero} {half} {one} {one} p₁ p₂ = triv
▷I-func {zero} {one} {zero} {zero} p₁ p₂ = triv
▷I-func {zero} {one} {zero} {forth} p₁ p₂ = triv
▷I-func {zero} {one} {zero} {half} p₁ p₂ = triv
▷I-func {zero} {one} {zero} {one} p₁ p₂ = triv
▷I-func {zero} {one} {forth} {zero} p₁ p₂ = triv
▷I-func {zero} {one} {forth} {forth} p₁ p₂ = triv
▷I-func {zero} {one} {forth} {half} p₁ p₂ = triv
▷I-func {zero} {one} {forth} {one} p₁ p₂ = triv
▷I-func {zero} {one} {half} {zero} p₁ p₂ = triv
▷I-func {zero} {one} {half} {forth} p₁ p₂ = triv
▷I-func {zero} {one} {half} {half} p₁ p₂ = triv
▷I-func {zero} {one} {half} {one} p₁ p₂ = triv
▷I-func {zero} {one} {one} {zero} p₁ p₂ = triv
▷I-func {zero} {one} {one} {forth} p₁ p₂ = triv
▷I-func {zero} {one} {one} {half} p₁ p₂ = triv
▷I-func {zero} {one} {one} {one} p₁ p₂ = triv
▷I-func {forth} {zero} {zero} {zero} p₁ p₂ = triv
▷I-func {forth} {zero} {zero} {forth} p₁ p₂ = triv
▷I-func {forth} {zero} {zero} {half} p₁ p₂ = triv
▷I-func {forth} {zero} {zero} {one} p₁ p₂ = triv
▷I-func {forth} {zero} {forth} {zero} () ()
▷I-func {forth} {zero} {forth} {forth} () p₂
▷I-func {forth} {zero} {forth} {half} () p₂
▷I-func {forth} {zero} {forth} {one} () p₂
▷I-func {forth} {zero} {half} {zero} () ()
▷I-func {forth} {zero} {half} {forth} () ()
▷I-func {forth} {zero} {half} {half} () p₂
▷I-func {forth} {zero} {half} {one} () p₂
▷I-func {forth} {zero} {one} {zero} () ()
▷I-func {forth} {zero} {one} {forth} () ()
▷I-func {forth} {zero} {one} {half} () ()
▷I-func {forth} {zero} {one} {one} () p₂
▷I-func {forth} {forth} {zero} {zero} p₁ p₂ = triv
▷I-func {forth} {forth} {zero} {forth} p₁ p₂ = triv
▷I-func {forth} {forth} {zero} {half} p₁ p₂ = triv
▷I-func {forth} {forth} {zero} {one} p₁ p₂ = triv
▷I-func {forth} {forth} {forth} {zero} p₁ ()
▷I-func {forth} {forth} {forth} {forth} p₁ p₂ = triv
▷I-func {forth} {forth} {forth} {half} p₁ p₂ = triv
▷I-func {forth} {forth} {forth} {one} p₁ p₂ = triv
▷I-func {forth} {forth} {half} {zero} p₁ ()
▷I-func {forth} {forth} {half} {forth} p₁ ()
▷I-func {forth} {forth} {half} {half} p₁ p₂ = triv
▷I-func {forth} {forth} {half} {one} p₁ p₂ = triv
▷I-func {forth} {forth} {one} {zero} p₁ ()
▷I-func {forth} {forth} {one} {forth} p₁ ()
▷I-func {forth} {forth} {one} {half} p₁ p₂ = triv
▷I-func {forth} {forth} {one} {one} p₁ p₂ = triv
▷I-func {forth} {half} {zero} {zero} p₁ p₂ = triv
▷I-func {forth} {half} {zero} {forth} p₁ p₂ = triv
▷I-func {forth} {half} {zero} {half} p₁ p₂ = triv
▷I-func {forth} {half} {zero} {one} p₁ p₂ = triv
▷I-func {forth} {half} {forth} {zero} p₁ ()
▷I-func {forth} {half} {forth} {forth} p₁ p₂ = triv
▷I-func {forth} {half} {forth} {half} p₁ p₂ = triv
▷I-func {forth} {half} {forth} {one} p₁ p₂ = triv
▷I-func {forth} {half} {half} {zero} p₁ ()
▷I-func {forth} {half} {half} {forth} p₁ p₂ = triv
▷I-func {forth} {half} {half} {half} p₁ p₂ = triv
▷I-func {forth} {half} {half} {one} p₁ p₂ = triv
▷I-func {forth} {half} {one} {zero} p₁ ()
▷I-func {forth} {half} {one} {forth} p₁ p₂ = triv
▷I-func {forth} {half} {one} {half} p₁ p₂ = triv
▷I-func {forth} {half} {one} {one} p₁ p₂ = triv
▷I-func {forth} {one} {zero} {zero} p₁ p₂ = triv
▷I-func {forth} {one} {zero} {forth} p₁ p₂ = triv
▷I-func {forth} {one} {zero} {half} p₁ p₂ = triv
▷I-func {forth} {one} {zero} {one} p₁ p₂ = triv
▷I-func {forth} {one} {forth} {zero} p₁ ()
▷I-func {forth} {one} {forth} {forth} p₁ p₂ = triv
▷I-func {forth} {one} {forth} {half} p₁ p₂ = triv
▷I-func {forth} {one} {forth} {one} p₁ p₂ = triv
▷I-func {forth} {one} {half} {zero} p₁ ()
▷I-func {forth} {one} {half} {forth} p₁ p₂ = triv
▷I-func {forth} {one} {half} {half} p₁ p₂ = triv
▷I-func {forth} {one} {half} {one} p₁ p₂ = triv
▷I-func {forth} {one} {one} {zero} p₁ ()
▷I-func {forth} {one} {one} {forth} p₁ p₂ = triv
▷I-func {forth} {one} {one} {half} p₁ p₂ = triv
▷I-func {forth} {one} {one} {one} p₁ p₂ = triv
▷I-func {half} {zero} {zero} {zero} p₁ p₂ = triv
▷I-func {half} {zero} {zero} {forth} p₁ p₂ = triv
▷I-func {half} {zero} {zero} {half} p₁ p₂ = triv
▷I-func {half} {zero} {zero} {one} p₁ p₂ = triv
▷I-func {half} {zero} {forth} {zero} () ()
▷I-func {half} {zero} {forth} {forth} () p₂
▷I-func {half} {zero} {forth} {half} () p₂
▷I-func {half} {zero} {forth} {one} () p₂
▷I-func {half} {zero} {half} {zero} () ()
▷I-func {half} {zero} {half} {forth} () ()
▷I-func {half} {zero} {half} {half} () p₂
▷I-func {half} {zero} {half} {one} () p₂
▷I-func {half} {zero} {one} {zero} () ()
▷I-func {half} {zero} {one} {forth} () ()
▷I-func {half} {zero} {one} {half} () ()
▷I-func {half} {zero} {one} {one} () p₂
▷I-func {half} {forth} {zero} {zero} p₁ p₂ = triv
▷I-func {half} {forth} {zero} {forth} p₁ p₂ = triv
▷I-func {half} {forth} {zero} {half} p₁ p₂ = triv
▷I-func {half} {forth} {zero} {one} p₁ p₂ = triv
▷I-func {half} {forth} {forth} {zero} () ()
▷I-func {half} {forth} {forth} {forth} () p₂
▷I-func {half} {forth} {forth} {half} () p₂
▷I-func {half} {forth} {forth} {one} () p₂
▷I-func {half} {forth} {half} {zero} () ()
▷I-func {half} {forth} {half} {forth} () ()
▷I-func {half} {forth} {half} {half} () p₂
▷I-func {half} {forth} {half} {one} () p₂
▷I-func {half} {forth} {one} {zero} () ()
▷I-func {half} {forth} {one} {forth} () ()
▷I-func {half} {forth} {one} {half} () ()
▷I-func {half} {forth} {one} {one} () p₂
▷I-func {half} {half} {zero} {zero} p₁ p₂ = triv
▷I-func {half} {half} {zero} {forth} p₁ p₂ = triv
▷I-func {half} {half} {zero} {half} p₁ p₂ = triv
▷I-func {half} {half} {zero} {one} p₁ p₂ = triv
▷I-func {half} {half} {forth} {zero} p₁ ()
▷I-func {half} {half} {forth} {forth} p₁ p₂ = triv
▷I-func {half} {half} {forth} {half} p₁ p₂ = triv
▷I-func {half} {half} {forth} {one} p₁ p₂ = triv
▷I-func {half} {half} {half} {zero} p₁ ()
▷I-func {half} {half} {half} {forth} p₁ p₂ = triv
▷I-func {half} {half} {half} {half} p₁ p₂ = triv
▷I-func {half} {half} {half} {one} p₁ p₂ = triv
▷I-func {half} {half} {one} {zero} p₁ ()
▷I-func {half} {half} {one} {forth} p₁ p₂ = triv
▷I-func {half} {half} {one} {half} p₁ p₂ = triv
▷I-func {half} {half} {one} {one} p₁ p₂ = triv
▷I-func {half} {one} {zero} {zero} p₁ p₂ = triv
▷I-func {half} {one} {zero} {forth} p₁ p₂ = triv
▷I-func {half} {one} {zero} {half} p₁ p₂ = triv
▷I-func {half} {one} {zero} {one} p₁ p₂ = triv
▷I-func {half} {one} {forth} {zero} p₁ ()
▷I-func {half} {one} {forth} {forth} p₁ p₂ = triv
▷I-func {half} {one} {forth} {half} p₁ p₂ = triv
▷I-func {half} {one} {forth} {one} p₁ p₂ = triv
▷I-func {half} {one} {half} {zero} p₁ ()
▷I-func {half} {one} {half} {forth} p₁ p₂ = triv
▷I-func {half} {one} {half} {half} p₁ p₂ = triv
▷I-func {half} {one} {half} {one} p₁ p₂ = triv
▷I-func {half} {one} {one} {zero} p₁ ()
▷I-func {half} {one} {one} {forth} p₁ p₂ = triv
▷I-func {half} {one} {one} {half} p₁ p₂ = triv
▷I-func {half} {one} {one} {one} p₁ p₂ = triv
▷I-func {one} {zero} {zero} {zero} p₁ p₂ = triv
▷I-func {one} {zero} {zero} {forth} p₁ p₂ = triv
▷I-func {one} {zero} {zero} {half} p₁ p₂ = triv
▷I-func {one} {zero} {zero} {one} p₁ p₂ = triv
▷I-func {one} {zero} {forth} {zero} p₁ ()
▷I-func {one} {zero} {forth} {forth} () p₂
▷I-func {one} {zero} {forth} {half} () p₂
▷I-func {one} {zero} {forth} {one} () p₂
▷I-func {one} {zero} {half} {zero} () ()
▷I-func {one} {zero} {half} {forth} () ()
▷I-func {one} {zero} {half} {half} () p₂
▷I-func {one} {zero} {half} {one} () p₂
▷I-func {one} {zero} {one} {zero} () ()
▷I-func {one} {zero} {one} {forth} () ()
▷I-func {one} {zero} {one} {half} () ()
▷I-func {one} {zero} {one} {one} () p₂
▷I-func {one} {forth} {zero} {zero} p₁ p₂ = triv
▷I-func {one} {forth} {zero} {forth} p₁ p₂ = triv
▷I-func {one} {forth} {zero} {half} p₁ p₂ = triv
▷I-func {one} {forth} {zero} {one} p₁ p₂ = triv
▷I-func {one} {forth} {forth} {zero} () ()
▷I-func {one} {forth} {forth} {forth} () p₂
▷I-func {one} {forth} {forth} {half} () p₂
▷I-func {one} {forth} {forth} {one} () p₂
▷I-func {one} {forth} {half} {zero} () ()
▷I-func {one} {forth} {half} {forth} () ()
▷I-func {one} {forth} {half} {half} () p₂
▷I-func {one} {forth} {half} {one} () p₂
▷I-func {one} {forth} {one} {zero} () ()
▷I-func {one} {forth} {one} {forth} () ()
▷I-func {one} {forth} {one} {half} () ()
▷I-func {one} {forth} {one} {one} () p₂
▷I-func {one} {half} {zero} {zero} p₁ p₂ = triv
▷I-func {one} {half} {zero} {forth} p₁ p₂ = triv
▷I-func {one} {half} {zero} {half} p₁ p₂ = triv
▷I-func {one} {half} {zero} {one} p₁ p₂ = triv
▷I-func {one} {half} {forth} {zero} () ()
▷I-func {one} {half} {forth} {forth} () p₂
▷I-func {one} {half} {forth} {half} () p₂
▷I-func {one} {half} {forth} {one} () p₂
▷I-func {one} {half} {half} {zero} () ()
▷I-func {one} {half} {half} {forth} p₁ p₂ = triv
▷I-func {one} {half} {half} {half} p₁ p₂ = triv
▷I-func {one} {half} {half} {one} p₁ p₂ = triv
▷I-func {one} {half} {one} {zero} () ()
▷I-func {one} {half} {one} {forth} p₁ p₂ = triv
▷I-func {one} {half} {one} {half} p₁ p₂ = triv
▷I-func {one} {half} {one} {one} p₁ p₂ = triv
▷I-func {one} {one} {zero} {zero} p₁ p₂ = triv
▷I-func {one} {one} {zero} {forth} p₁ p₂ = triv
▷I-func {one} {one} {zero} {half} p₁ p₂ = triv
▷I-func {one} {one} {zero} {one} p₁ p₂ = triv
▷I-func {one} {one} {forth} {zero} p₁ ()
▷I-func {one} {one} {forth} {forth} p₁ p₂ = triv
▷I-func {one} {one} {forth} {half} p₁ p₂ = triv
▷I-func {one} {one} {forth} {one} p₁ p₂ = triv
▷I-func {one} {one} {half} {zero} p₁ ()
▷I-func {one} {one} {half} {forth} p₁ p₂ = triv
▷I-func {one} {one} {half} {half} p₁ p₂ = triv
▷I-func {one} {one} {half} {one} p₁ p₂ = triv
▷I-func {one} {one} {one} {zero} p₁ ()
▷I-func {one} {one} {one} {forth} p₁ p₂ = triv
▷I-func {one} {one} {one} {half} p₁ p₂ = triv
▷I-func {one} {one} {one} {one} p₁ p₂ = triv

▷I-distl : {a b c : Four} → (a ▷I (b ⊔I c)) ≡ ((a ▷I b) ⊔I (a ▷I c))
▷I-distl {zero} {zero} {zero} = refl
▷I-distl {zero} {zero} {forth} = refl
▷I-distl {zero} {zero} {half} = refl
▷I-distl {zero} {zero} {one} = refl
▷I-distl {zero} {forth} {zero} = refl
▷I-distl {zero} {forth} {forth} = refl
▷I-distl {zero} {forth} {half} = refl
▷I-distl {zero} {forth} {one} = refl
▷I-distl {zero} {half} {zero} = refl
▷I-distl {zero} {half} {forth} = refl
▷I-distl {zero} {half} {half} = refl
▷I-distl {zero} {half} {one} = refl
▷I-distl {zero} {one} {zero} = refl
▷I-distl {zero} {one} {forth} = refl
▷I-distl {zero} {one} {half} = refl
▷I-distl {zero} {one} {one} = refl
▷I-distl {forth} {zero} {zero} = refl
▷I-distl {forth} {zero} {forth} = refl
▷I-distl {forth} {zero} {half} = refl
▷I-distl {forth} {zero} {one} = refl
▷I-distl {forth} {forth} {zero} = refl
▷I-distl {forth} {forth} {forth} = refl
▷I-distl {forth} {forth} {half} = refl
▷I-distl {forth} {forth} {one} = refl
▷I-distl {forth} {half} {zero} = refl
▷I-distl {forth} {half} {forth} = refl
▷I-distl {forth} {half} {half} = refl
▷I-distl {forth} {half} {one} = refl
▷I-distl {forth} {one} {zero} = refl
▷I-distl {forth} {one} {forth} = refl
▷I-distl {forth} {one} {half} = refl
▷I-distl {forth} {one} {one} = refl
▷I-distl {half} {zero} {zero} = refl
▷I-distl {half} {zero} {forth} = refl
▷I-distl {half} {zero} {half} = refl
▷I-distl {half} {zero} {one} = refl
▷I-distl {half} {forth} {zero} = refl
▷I-distl {half} {forth} {forth} = refl
▷I-distl {half} {forth} {half} = refl
▷I-distl {half} {forth} {one} = refl
▷I-distl {half} {half} {zero} = refl
▷I-distl {half} {half} {forth} = refl
▷I-distl {half} {half} {half} = refl
▷I-distl {half} {half} {one} = refl
▷I-distl {half} {one} {zero} = refl
▷I-distl {half} {one} {forth} = refl
▷I-distl {half} {one} {half} = refl
▷I-distl {half} {one} {one} = refl
▷I-distl {one} {zero} {zero} = refl
▷I-distl {one} {zero} {forth} = refl
▷I-distl {one} {zero} {half} = refl
▷I-distl {one} {zero} {one} = refl
▷I-distl {one} {forth} {zero} = refl
▷I-distl {one} {forth} {forth} = refl
▷I-distl {one} {forth} {half} = refl
▷I-distl {one} {forth} {one} = refl
▷I-distl {one} {half} {zero} = refl
▷I-distl {one} {half} {forth} = refl
▷I-distl {one} {half} {half} = refl
▷I-distl {one} {half} {one} = refl
▷I-distl {one} {one} {zero} = refl
▷I-distl {one} {one} {forth} = refl
▷I-distl {one} {one} {half} = refl
▷I-distl {one} {one} {one} = refl

▷I-distr : {a b c : Four} → ((a ⊔I b) ▷I c) ≡ ((a ▷I c) ⊔I (b ▷I c))
▷I-distr {zero} {zero} {zero} = refl
▷I-distr {zero} {zero} {forth} = refl
▷I-distr {zero} {zero} {half} = refl
▷I-distr {zero} {zero} {one} = refl
▷I-distr {zero} {forth} {zero} = refl
▷I-distr {zero} {forth} {forth} = refl
▷I-distr {zero} {forth} {half} = refl
▷I-distr {zero} {forth} {one} = refl
▷I-distr {zero} {half} {zero} = refl
▷I-distr {zero} {half} {forth} = refl
▷I-distr {zero} {half} {half} = refl
▷I-distr {zero} {half} {one} = refl
▷I-distr {zero} {one} {zero} = refl
▷I-distr {zero} {one} {forth} = refl
▷I-distr {zero} {one} {half} = refl
▷I-distr {zero} {one} {one} = refl
▷I-distr {forth} {zero} {zero} = refl
▷I-distr {forth} {zero} {forth} = refl
▷I-distr {forth} {zero} {half} = refl
▷I-distr {forth} {zero} {one} = refl
▷I-distr {forth} {forth} {zero} = refl
▷I-distr {forth} {forth} {forth} = refl
▷I-distr {forth} {forth} {half} = refl
▷I-distr {forth} {forth} {one} = refl
▷I-distr {forth} {half} {zero} = refl
▷I-distr {forth} {half} {forth} = refl
▷I-distr {forth} {half} {half} = refl
▷I-distr {forth} {half} {one} = refl
▷I-distr {forth} {one} {zero} = refl
▷I-distr {forth} {one} {forth} = refl
▷I-distr {forth} {one} {half} = refl
▷I-distr {forth} {one} {one} = refl
▷I-distr {half} {zero} {zero} = refl
▷I-distr {half} {zero} {forth} = refl
▷I-distr {half} {zero} {half} = refl
▷I-distr {half} {zero} {one} = refl
▷I-distr {half} {forth} {zero} = refl
▷I-distr {half} {forth} {forth} = refl
▷I-distr {half} {forth} {half} = refl
▷I-distr {half} {forth} {one} = refl
▷I-distr {half} {half} {zero} = refl
▷I-distr {half} {half} {forth} = refl
▷I-distr {half} {half} {half} = refl
▷I-distr {half} {half} {one} = refl
▷I-distr {half} {one} {zero} = refl
▷I-distr {half} {one} {forth} = refl
▷I-distr {half} {one} {half} = refl
▷I-distr {half} {one} {one} = refl
▷I-distr {one} {zero} {zero} = refl
▷I-distr {one} {zero} {forth} = refl
▷I-distr {one} {zero} {half} = refl
▷I-distr {one} {zero} {one} = refl
▷I-distr {one} {forth} {zero} = refl
▷I-distr {one} {forth} {forth} = refl
▷I-distr {one} {forth} {half} = refl
▷I-distr {one} {forth} {one} = refl
▷I-distr {one} {half} {zero} = refl
▷I-distr {one} {half} {forth} = refl
▷I-distr {one} {half} {half} = refl
▷I-distr {one} {half} {one} = refl
▷I-distr {one} {one} {zero} = refl
▷I-distr {one} {one} {forth} = refl
▷I-distr {one} {one} {half} = refl
▷I-distr {one} {one} {one} = refl

⊔I-sym : ∀{a b} → (a ⊔I b) ≡ (b ⊔I a)
⊔I-sym {zero} {zero} = refl
⊔I-sym {zero} {forth} = refl
⊔I-sym {zero} {half} = refl
⊔I-sym {zero} {one} = refl
⊔I-sym {forth} {zero} = refl
⊔I-sym {forth} {forth} = refl
⊔I-sym {forth} {half} = refl
⊔I-sym {forth} {one} = refl
⊔I-sym {half} {zero} = refl
⊔I-sym {half} {forth} = refl
⊔I-sym {half} {half} = refl
⊔I-sym {half} {one} = refl
⊔I-sym {one} {zero} = refl
⊔I-sym {one} {forth} = refl
⊔I-sym {one} {half} = refl
⊔I-sym {one} {one} = refl

⊔I-assoc : ∀{a b c} → (a ⊔I b) ⊔I c ≡ a ⊔I (b ⊔I c)
⊔I-assoc {zero} {zero} {zero} = refl
⊔I-assoc {zero} {zero} {forth} = refl
⊔I-assoc {zero} {zero} {half} = refl
⊔I-assoc {zero} {zero} {one} = refl
⊔I-assoc {zero} {forth} {zero} = refl
⊔I-assoc {zero} {forth} {forth} = refl
⊔I-assoc {zero} {forth} {half} = refl
⊔I-assoc {zero} {forth} {one} = refl
⊔I-assoc {zero} {half} {zero} = refl
⊔I-assoc {zero} {half} {forth} = refl
⊔I-assoc {zero} {half} {half} = refl
⊔I-assoc {zero} {half} {one} = refl
⊔I-assoc {zero} {one} {zero} = refl
⊔I-assoc {zero} {one} {forth} = refl
⊔I-assoc {zero} {one} {half} = refl
⊔I-assoc {zero} {one} {one} = refl
⊔I-assoc {forth} {zero} {zero} = refl
⊔I-assoc {forth} {zero} {forth} = refl
⊔I-assoc {forth} {zero} {half} = refl
⊔I-assoc {forth} {zero} {one} = refl
⊔I-assoc {forth} {forth} {zero} = refl
⊔I-assoc {forth} {forth} {forth} = refl
⊔I-assoc {forth} {forth} {half} = refl
⊔I-assoc {forth} {forth} {one} = refl
⊔I-assoc {forth} {half} {zero} = refl
⊔I-assoc {forth} {half} {forth} = refl
⊔I-assoc {forth} {half} {half} = refl
⊔I-assoc {forth} {half} {one} = refl
⊔I-assoc {forth} {one} {zero} = refl
⊔I-assoc {forth} {one} {forth} = refl
⊔I-assoc {forth} {one} {half} = refl
⊔I-assoc {forth} {one} {one} = refl
⊔I-assoc {half} {zero} {zero} = refl
⊔I-assoc {half} {zero} {forth} = refl
⊔I-assoc {half} {zero} {half} = refl
⊔I-assoc {half} {zero} {one} = refl
⊔I-assoc {half} {forth} {zero} = refl
⊔I-assoc {half} {forth} {forth} = refl
⊔I-assoc {half} {forth} {half} = refl
⊔I-assoc {half} {forth} {one} = refl
⊔I-assoc {half} {half} {zero} = refl
⊔I-assoc {half} {half} {forth} = refl
⊔I-assoc {half} {half} {half} = refl
⊔I-assoc {half} {half} {one} = refl
⊔I-assoc {half} {one} {zero} = refl
⊔I-assoc {half} {one} {forth} = refl
⊔I-assoc {half} {one} {half} = refl
⊔I-assoc {half} {one} {one} = refl
⊔I-assoc {one} {zero} {zero} = refl
⊔I-assoc {one} {zero} {forth} = refl
⊔I-assoc {one} {zero} {half} = refl
⊔I-assoc {one} {zero} {one} = refl
⊔I-assoc {one} {forth} {zero} = refl
⊔I-assoc {one} {forth} {forth} = refl
⊔I-assoc {one} {forth} {half} = refl
⊔I-assoc {one} {forth} {one} = refl
⊔I-assoc {one} {half} {zero} = refl
⊔I-assoc {one} {half} {forth} = refl
⊔I-assoc {one} {half} {half} = refl
⊔I-assoc {one} {half} {one} = refl
⊔I-assoc {one} {one} {zero} = refl
⊔I-assoc {one} {one} {forth} = refl
⊔I-assoc {one} {one} {half} = refl
⊔I-assoc {one} {one} {one} = refl

⊔I-func : ∀{a c b d} → a ≤₄ c → b ≤₄ d → (a ⊔I b) ≤₄ (c ⊔I d)
⊔I-func {zero} {zero} {zero} {zero} triv triv = triv
⊔I-func {zero} {zero} {zero} {forth} triv triv = triv
⊔I-func {zero} {zero} {zero} {half} triv triv = triv
⊔I-func {zero} {zero} {zero} {one} triv triv = triv
⊔I-func {zero} {zero} {forth} {zero} triv ()
⊔I-func {zero} {zero} {forth} {forth} triv triv = triv
⊔I-func {zero} {zero} {forth} {half} triv triv = triv
⊔I-func {zero} {zero} {forth} {one} triv triv = triv
⊔I-func {zero} {zero} {half} {zero} triv ()
⊔I-func {zero} {zero} {half} {forth} triv ()
⊔I-func {zero} {zero} {half} {half} triv triv = triv
⊔I-func {zero} {zero} {half} {one} triv triv = triv
⊔I-func {zero} {zero} {one} {zero} triv ()
⊔I-func {zero} {zero} {one} {forth} triv ()
⊔I-func {zero} {zero} {one} {half} triv ()
⊔I-func {zero} {zero} {one} {one} triv triv = triv
⊔I-func {zero} {forth} {zero} {zero} triv triv = triv
⊔I-func {zero} {forth} {zero} {forth} triv triv = triv
⊔I-func {zero} {forth} {zero} {half} triv triv = triv
⊔I-func {zero} {forth} {zero} {one} triv triv = triv
⊔I-func {zero} {forth} {forth} {zero} triv ()
⊔I-func {zero} {forth} {forth} {forth} triv triv = triv
⊔I-func {zero} {forth} {forth} {half} triv triv = triv
⊔I-func {zero} {forth} {forth} {one} triv triv = triv
⊔I-func {zero} {forth} {half} {zero} triv ()
⊔I-func {zero} {forth} {half} {forth} triv ()
⊔I-func {zero} {forth} {half} {half} triv triv = triv
⊔I-func {zero} {forth} {half} {one} triv triv = triv
⊔I-func {zero} {forth} {one} {zero} triv ()
⊔I-func {zero} {forth} {one} {forth} triv ()
⊔I-func {zero} {forth} {one} {half} triv ()
⊔I-func {zero} {forth} {one} {one} triv triv = triv
⊔I-func {zero} {half} {zero} {zero} triv triv = triv
⊔I-func {zero} {half} {zero} {forth} triv triv = triv
⊔I-func {zero} {half} {zero} {half} triv triv = triv
⊔I-func {zero} {half} {zero} {one} triv triv = triv
⊔I-func {zero} {half} {forth} {zero} triv ()
⊔I-func {zero} {half} {forth} {forth} triv triv = triv
⊔I-func {zero} {half} {forth} {half} triv triv = triv
⊔I-func {zero} {half} {forth} {one} triv triv = triv
⊔I-func {zero} {half} {half} {zero} triv ()
⊔I-func {zero} {half} {half} {forth} triv ()
⊔I-func {zero} {half} {half} {half} triv triv = triv
⊔I-func {zero} {half} {half} {one} triv triv = triv
⊔I-func {zero} {half} {one} {zero} triv ()
⊔I-func {zero} {half} {one} {forth} triv ()
⊔I-func {zero} {half} {one} {half} triv ()
⊔I-func {zero} {half} {one} {one} triv triv = triv
⊔I-func {zero} {one} {zero} {zero} triv triv = triv
⊔I-func {zero} {one} {zero} {forth} triv triv = triv
⊔I-func {zero} {one} {zero} {half} triv triv = triv
⊔I-func {zero} {one} {zero} {one} triv triv = triv
⊔I-func {zero} {one} {forth} {zero} triv ()
⊔I-func {zero} {one} {forth} {forth} triv triv = triv
⊔I-func {zero} {one} {forth} {half} triv triv = triv
⊔I-func {zero} {one} {forth} {one} triv triv = triv
⊔I-func {zero} {one} {half} {zero} triv ()
⊔I-func {zero} {one} {half} {forth} triv ()
⊔I-func {zero} {one} {half} {half} triv triv = triv
⊔I-func {zero} {one} {half} {one} triv triv = triv
⊔I-func {zero} {one} {one} {zero} triv ()
⊔I-func {zero} {one} {one} {forth} triv ()
⊔I-func {zero} {one} {one} {half} triv ()
⊔I-func {zero} {one} {one} {one} triv triv = triv
⊔I-func {forth} {zero} {zero} {zero} () p₂
⊔I-func {forth} {zero} {zero} {forth} () p₂
⊔I-func {forth} {zero} {zero} {half} () p₂
⊔I-func {forth} {zero} {zero} {one} () p₂
⊔I-func {forth} {zero} {forth} {zero} () p₂
⊔I-func {forth} {zero} {forth} {forth} () p₂
⊔I-func {forth} {zero} {forth} {half} () p₂
⊔I-func {forth} {zero} {forth} {one} () p₂
⊔I-func {forth} {zero} {half} {zero} () p₂
⊔I-func {forth} {zero} {half} {forth} () p₂
⊔I-func {forth} {zero} {half} {half} () p₂
⊔I-func {forth} {zero} {half} {one} () p₂
⊔I-func {forth} {zero} {one} {zero} () p₂
⊔I-func {forth} {zero} {one} {forth} () p₂
⊔I-func {forth} {zero} {one} {half} () p₂
⊔I-func {forth} {zero} {one} {one} () p₂
⊔I-func {forth} {forth} {zero} {zero} triv triv = triv
⊔I-func {forth} {forth} {zero} {forth} triv triv = triv
⊔I-func {forth} {forth} {zero} {half} triv triv = triv
⊔I-func {forth} {forth} {zero} {one} triv triv = triv
⊔I-func {forth} {forth} {forth} {zero} triv ()
⊔I-func {forth} {forth} {forth} {forth} triv triv = triv
⊔I-func {forth} {forth} {forth} {half} triv triv = triv
⊔I-func {forth} {forth} {forth} {one} triv triv = triv
⊔I-func {forth} {forth} {half} {zero} triv ()
⊔I-func {forth} {forth} {half} {forth} triv ()
⊔I-func {forth} {forth} {half} {half} triv triv = triv
⊔I-func {forth} {forth} {half} {one} triv triv = triv
⊔I-func {forth} {forth} {one} {zero} triv ()
⊔I-func {forth} {forth} {one} {forth} triv ()
⊔I-func {forth} {forth} {one} {half} triv ()
⊔I-func {forth} {forth} {one} {one} triv triv = triv
⊔I-func {forth} {half} {zero} {zero} triv triv = triv
⊔I-func {forth} {half} {zero} {forth} triv triv = triv
⊔I-func {forth} {half} {zero} {half} triv triv = triv
⊔I-func {forth} {half} {zero} {one} triv triv = triv
⊔I-func {forth} {half} {forth} {zero} triv ()
⊔I-func {forth} {half} {forth} {forth} triv triv = triv
⊔I-func {forth} {half} {forth} {half} triv triv = triv
⊔I-func {forth} {half} {forth} {one} triv triv = triv
⊔I-func {forth} {half} {half} {zero} triv ()
⊔I-func {forth} {half} {half} {forth} triv ()
⊔I-func {forth} {half} {half} {half} triv triv = triv
⊔I-func {forth} {half} {half} {one} triv triv = triv
⊔I-func {forth} {half} {one} {zero} triv ()
⊔I-func {forth} {half} {one} {forth} triv ()
⊔I-func {forth} {half} {one} {half} triv ()
⊔I-func {forth} {half} {one} {one} triv triv = triv
⊔I-func {forth} {one} {zero} {zero} triv triv = triv
⊔I-func {forth} {one} {zero} {forth} triv triv = triv
⊔I-func {forth} {one} {zero} {half} triv triv = triv
⊔I-func {forth} {one} {zero} {one} triv triv = triv
⊔I-func {forth} {one} {forth} {zero} triv ()
⊔I-func {forth} {one} {forth} {forth} triv triv = triv
⊔I-func {forth} {one} {forth} {half} triv triv = triv
⊔I-func {forth} {one} {forth} {one} triv triv = triv
⊔I-func {forth} {one} {half} {zero} triv ()
⊔I-func {forth} {one} {half} {forth} triv ()
⊔I-func {forth} {one} {half} {half} triv triv = triv
⊔I-func {forth} {one} {half} {one} triv triv = triv
⊔I-func {forth} {one} {one} {zero} triv ()
⊔I-func {forth} {one} {one} {forth} triv ()
⊔I-func {forth} {one} {one} {half} triv ()
⊔I-func {forth} {one} {one} {one} triv triv = triv
⊔I-func {half} {zero} {zero} {zero} () p₂
⊔I-func {half} {zero} {zero} {forth} () p₂
⊔I-func {half} {zero} {zero} {half} () p₂
⊔I-func {half} {zero} {zero} {one} () p₂
⊔I-func {half} {zero} {forth} {zero} () p₂
⊔I-func {half} {zero} {forth} {forth} () p₂
⊔I-func {half} {zero} {forth} {half} () p₂
⊔I-func {half} {zero} {forth} {one} () p₂
⊔I-func {half} {zero} {half} {zero} () p₂
⊔I-func {half} {zero} {half} {forth} () p₂
⊔I-func {half} {zero} {half} {half} () p₂
⊔I-func {half} {zero} {half} {one} () p₂
⊔I-func {half} {zero} {one} {zero} () p₂
⊔I-func {half} {zero} {one} {forth} () p₂
⊔I-func {half} {zero} {one} {half} () p₂
⊔I-func {half} {zero} {one} {one} () p₂
⊔I-func {half} {forth} {zero} {zero} () p₂
⊔I-func {half} {forth} {zero} {forth} () p₂
⊔I-func {half} {forth} {zero} {half} () p₂
⊔I-func {half} {forth} {zero} {one} () p₂
⊔I-func {half} {forth} {forth} {zero} () p₂
⊔I-func {half} {forth} {forth} {forth} () p₂
⊔I-func {half} {forth} {forth} {half} () p₂
⊔I-func {half} {forth} {forth} {one} () p₂
⊔I-func {half} {forth} {half} {zero} () p₂
⊔I-func {half} {forth} {half} {forth} () p₂
⊔I-func {half} {forth} {half} {half} () p₂
⊔I-func {half} {forth} {half} {one} () p₂
⊔I-func {half} {forth} {one} {zero} () p₂
⊔I-func {half} {forth} {one} {forth} () p₂
⊔I-func {half} {forth} {one} {half} () p₂
⊔I-func {half} {forth} {one} {one} () p₂
⊔I-func {half} {half} {zero} {zero} triv triv = triv
⊔I-func {half} {half} {zero} {forth} triv triv = triv
⊔I-func {half} {half} {zero} {half} triv triv = triv
⊔I-func {half} {half} {zero} {one} triv triv = triv
⊔I-func {half} {half} {forth} {zero} triv ()
⊔I-func {half} {half} {forth} {forth} triv triv = triv
⊔I-func {half} {half} {forth} {half} triv triv = triv
⊔I-func {half} {half} {forth} {one} triv triv = triv
⊔I-func {half} {half} {half} {zero} triv ()
⊔I-func {half} {half} {half} {forth} triv ()
⊔I-func {half} {half} {half} {half} triv triv = triv
⊔I-func {half} {half} {half} {one} triv triv = triv
⊔I-func {half} {half} {one} {zero} triv ()
⊔I-func {half} {half} {one} {forth} triv ()
⊔I-func {half} {half} {one} {half} triv ()
⊔I-func {half} {half} {one} {one} triv triv = triv
⊔I-func {half} {one} {zero} {zero} triv triv = triv
⊔I-func {half} {one} {zero} {forth} triv triv = triv
⊔I-func {half} {one} {zero} {half} triv triv = triv
⊔I-func {half} {one} {zero} {one} triv triv = triv
⊔I-func {half} {one} {forth} {zero} triv ()
⊔I-func {half} {one} {forth} {forth} triv triv = triv
⊔I-func {half} {one} {forth} {half} triv triv = triv
⊔I-func {half} {one} {forth} {one} triv triv = triv
⊔I-func {half} {one} {half} {zero} triv ()
⊔I-func {half} {one} {half} {forth} triv ()
⊔I-func {half} {one} {half} {half} triv triv = triv
⊔I-func {half} {one} {half} {one} triv triv = triv
⊔I-func {half} {one} {one} {zero} triv ()
⊔I-func {half} {one} {one} {forth} triv ()
⊔I-func {half} {one} {one} {half} triv ()
⊔I-func {half} {one} {one} {one} triv triv = triv
⊔I-func {one} {zero} {zero} {zero} () p₂
⊔I-func {one} {zero} {zero} {forth} () p₂
⊔I-func {one} {zero} {zero} {half} () p₂
⊔I-func {one} {zero} {zero} {one} () p₂
⊔I-func {one} {zero} {forth} {zero} () p₂
⊔I-func {one} {zero} {forth} {forth} () p₂
⊔I-func {one} {zero} {forth} {half} () p₂
⊔I-func {one} {zero} {forth} {one} () p₂
⊔I-func {one} {zero} {half} {zero} () p₂
⊔I-func {one} {zero} {half} {forth} () p₂
⊔I-func {one} {zero} {half} {half} () p₂
⊔I-func {one} {zero} {half} {one} () p₂
⊔I-func {one} {zero} {one} {zero} () p₂
⊔I-func {one} {zero} {one} {forth} () p₂
⊔I-func {one} {zero} {one} {half} () p₂
⊔I-func {one} {zero} {one} {one} () p₂
⊔I-func {one} {forth} {zero} {zero} () p₂
⊔I-func {one} {forth} {zero} {forth} () p₂
⊔I-func {one} {forth} {zero} {half} () p₂
⊔I-func {one} {forth} {zero} {one} () p₂
⊔I-func {one} {forth} {forth} {zero} () p₂
⊔I-func {one} {forth} {forth} {forth} () p₂
⊔I-func {one} {forth} {forth} {half} () p₂
⊔I-func {one} {forth} {forth} {one} () p₂
⊔I-func {one} {forth} {half} {zero} () p₂
⊔I-func {one} {forth} {half} {forth} () p₂
⊔I-func {one} {forth} {half} {half} () p₂
⊔I-func {one} {forth} {half} {one} () p₂
⊔I-func {one} {forth} {one} {zero} () p₂
⊔I-func {one} {forth} {one} {forth} () p₂
⊔I-func {one} {forth} {one} {half} () p₂
⊔I-func {one} {forth} {one} {one} () p₂
⊔I-func {one} {half} {zero} {zero} () p₂
⊔I-func {one} {half} {zero} {forth} () p₂
⊔I-func {one} {half} {zero} {half} () p₂
⊔I-func {one} {half} {zero} {one} () p₂
⊔I-func {one} {half} {forth} {zero} () p₂
⊔I-func {one} {half} {forth} {forth} () p₂
⊔I-func {one} {half} {forth} {half} () p₂
⊔I-func {one} {half} {forth} {one} () p₂
⊔I-func {one} {half} {half} {zero} () p₂
⊔I-func {one} {half} {half} {forth} () p₂
⊔I-func {one} {half} {half} {half} () p₂
⊔I-func {one} {half} {half} {one} () p₂
⊔I-func {one} {half} {one} {zero} () p₂
⊔I-func {one} {half} {one} {forth} () p₂
⊔I-func {one} {half} {one} {half} () p₂
⊔I-func {one} {half} {one} {one} () p₂
⊔I-func {one} {one} {zero} {zero} triv triv = triv
⊔I-func {one} {one} {zero} {forth} triv triv = triv
⊔I-func {one} {one} {zero} {half} triv triv = triv
⊔I-func {one} {one} {zero} {one} triv triv = triv
⊔I-func {one} {one} {forth} {zero} triv ()
⊔I-func {one} {one} {forth} {forth} triv triv = triv
⊔I-func {one} {one} {forth} {half} triv triv = triv
⊔I-func {one} {one} {forth} {one} triv triv = triv
⊔I-func {one} {one} {half} {zero} triv ()
⊔I-func {one} {one} {half} {forth} triv ()
⊔I-func {one} {one} {half} {half} triv triv = triv
⊔I-func {one} {one} {half} {one} triv triv = triv
⊔I-func {one} {one} {one} {zero} triv ()
⊔I-func {one} {one} {one} {forth} triv ()
⊔I-func {one} {one} {one} {half} triv ()
⊔I-func {one} {one} {one} {one} triv triv = triv

⊔I-contract : ∀{a} → (a ⊔I a) ≡ a
⊔I-contract {zero} = refl
⊔I-contract {forth} = refl
⊔I-contract {half} = refl
⊔I-contract {one} = refl

⊔I-inl : ∀{a b} → a ≤₄ (a ⊔I b)
⊔I-inl {zero} {zero} = triv
⊔I-inl {zero} {forth} = triv
⊔I-inl {zero} {half} = triv
⊔I-inl {zero} {one} = triv
⊔I-inl {forth} {zero} = triv
⊔I-inl {forth} {forth} = triv
⊔I-inl {forth} {half} = triv
⊔I-inl {forth} {one} = triv
⊔I-inl {half} {zero} = triv
⊔I-inl {half} {forth} = triv
⊔I-inl {half} {half} = triv
⊔I-inl {half} {one} = triv
⊔I-inl {one} {zero} = triv
⊔I-inl {one} {forth} = triv
⊔I-inl {one} {half} = triv
⊔I-inl {one} {one} = triv

⊔I-inr : ∀{a b} → b ≤₄ (a ⊔I b)
⊔I-inr {zero} {zero} = triv
⊔I-inr {zero} {forth} = triv
⊔I-inr {zero} {half} = triv
⊔I-inr {zero} {one} = triv
⊔I-inr {forth} {zero} = triv
⊔I-inr {forth} {forth} = triv
⊔I-inr {forth} {half} = triv
⊔I-inr {forth} {one} = triv
⊔I-inr {half} {zero} = triv
⊔I-inr {half} {forth} = triv
⊔I-inr {half} {half} = triv
⊔I-inr {half} {one} = triv
⊔I-inr {one} {zero} = triv
⊔I-inr {one} {forth} = triv
⊔I-inr {one} {half} = triv
⊔I-inr {one} {one} = triv

-- Exchange Implications (Fig. 9, top of p. 18):

-- Ideal
ax₁-inv : ∀{a b c d} → (a ⊙I b) ▷I (c ⊙I d) ≤₄ (a ▷I c) ⊙I (b ▷I d)
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

-- Counter example:
-- ax₁ : ∀{a b c d} → (a ▷I c) ⊙I (b ▷I d) ≤₄ (a ⊙I b) ▷I (c ⊙I d)
-- ax₁ {forth} {forth} {forth} {forth} = triv

-- Ideal
ax₂-inv : ∀{a b c} → (a ⊙I b) ▷I c ≤₄ a ⊙I (b ▷I c)
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

-- Counter example:
-- ax₂ : ∀{a b c} → a ⊙I (b ▷I c) ≤₄ (a ⊙I b) ▷I c
-- ax₂ {forth} {forth} {forth} = triv

-- Ideal
ax₃-inv : ∀{a b c} → a ▷I (b ⊙I c) ≤₄ b ⊙I (a ▷I c)
ax₃-inv {zero} {zero} {zero} = triv
ax₃-inv {zero} {zero} {forth} = triv
ax₃-inv {zero} {zero} {half} = triv
ax₃-inv {zero} {zero} {one} = triv
ax₃-inv {zero} {forth} {zero} = triv
ax₃-inv {zero} {forth} {forth} = triv
ax₃-inv {zero} {forth} {half} = triv
ax₃-inv {zero} {forth} {one} = triv
ax₃-inv {zero} {half} {zero} = triv
ax₃-inv {zero} {half} {forth} = triv
ax₃-inv {zero} {half} {half} = triv
ax₃-inv {zero} {half} {one} = triv
ax₃-inv {zero} {one} {zero} = triv
ax₃-inv {zero} {one} {forth} = triv
ax₃-inv {zero} {one} {half} = triv
ax₃-inv {zero} {one} {one} = triv
ax₃-inv {forth} {zero} {zero} = triv
ax₃-inv {forth} {zero} {forth} = triv
ax₃-inv {forth} {zero} {half} = triv
ax₃-inv {forth} {zero} {one} = triv
ax₃-inv {forth} {forth} {zero} = triv
ax₃-inv {forth} {forth} {forth} = triv
ax₃-inv {forth} {forth} {half} = triv
ax₃-inv {forth} {forth} {one} = triv
ax₃-inv {forth} {half} {zero} = triv
ax₃-inv {forth} {half} {forth} = triv
ax₃-inv {forth} {half} {half} = triv
ax₃-inv {forth} {half} {one} = triv
ax₃-inv {forth} {one} {zero} = triv
ax₃-inv {forth} {one} {forth} = triv
ax₃-inv {forth} {one} {half} = triv
ax₃-inv {forth} {one} {one} = triv
ax₃-inv {half} {zero} {zero} = triv
ax₃-inv {half} {zero} {forth} = triv
ax₃-inv {half} {zero} {half} = triv
ax₃-inv {half} {zero} {one} = triv
ax₃-inv {half} {forth} {zero} = triv
ax₃-inv {half} {forth} {forth} = triv
ax₃-inv {half} {forth} {half} = triv
ax₃-inv {half} {forth} {one} = triv
ax₃-inv {half} {half} {zero} = triv
ax₃-inv {half} {half} {forth} = triv
ax₃-inv {half} {half} {half} = triv
ax₃-inv {half} {half} {one} = triv
ax₃-inv {half} {one} {zero} = triv
ax₃-inv {half} {one} {forth} = triv
ax₃-inv {half} {one} {half} = triv
ax₃-inv {half} {one} {one} = triv
ax₃-inv {one} {zero} {zero} = triv
ax₃-inv {one} {zero} {forth} = triv
ax₃-inv {one} {zero} {half} = triv
ax₃-inv {one} {zero} {one} = triv
ax₃-inv {one} {forth} {zero} = triv
ax₃-inv {one} {forth} {forth} = triv
ax₃-inv {one} {forth} {half} = triv
ax₃-inv {one} {forth} {one} = triv
ax₃-inv {one} {half} {zero} = triv
ax₃-inv {one} {half} {forth} = triv
ax₃-inv {one} {half} {half} = triv
ax₃-inv {one} {half} {one} = triv
ax₃-inv {one} {one} {zero} = triv
ax₃-inv {one} {one} {forth} = triv
ax₃-inv {one} {one} {half} = triv
ax₃-inv {one} {one} {one} = triv

-- Counter example:
-- ax₃ : ∀{a b c} → b ⊙I (a ▷I c) ≤₄ a ▷I (b ⊙I c)
-- ax₃ {forth} {forth} {forth} = triv

-- Ideal
ax₄-inv : ∀{a b} → a ▷I b ≤₄ a ⊙I b
ax₄-inv {zero} {zero} = triv
ax₄-inv {zero} {forth} = triv
ax₄-inv {zero} {half} = triv
ax₄-inv {zero} {one} = triv
ax₄-inv {forth} {zero} = triv
ax₄-inv {forth} {forth} = triv
ax₄-inv {forth} {half} = triv
ax₄-inv {forth} {one} = triv
ax₄-inv {half} {zero} = triv
ax₄-inv {half} {forth} = triv
ax₄-inv {half} {half} = triv
ax₄-inv {half} {one} = triv
ax₄-inv {one} {zero} = triv
ax₄-inv {one} {forth} = triv
ax₄-inv {one} {half} = triv
ax₄-inv {one} {one} = triv

ax₄ : Σ[ a ∈ Four ](Σ[ b ∈ Four ](a ⊙I b ≤₄ a ▷I b → ⊥ {lzero}))
ax₄ = forth , (forth , id)
