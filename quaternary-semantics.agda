module quaternary-semantics where

open import level
open import empty
open import unit

data Four : Set where
  zero : Four
  forth : Four
  half : Four
  one : Four

infix 3 _≤₄_

_≤₄_ : Four → Four → Set
forth ≤₄ zero = ⊥
half ≤₄ zero = ⊥
half ≤₄ forth = ⊥
one ≤₄ zero = ⊥
one ≤₄ forth = ⊥
one ≤₄ half = ⊥
_ ≤₄ _ = ⊤

_⊗₄_ : Four → Four → Four
forth ⊗₄ forth = forth
forth ⊗₄ half = half
half ⊗₄ forth = half
half ⊗₄ half = half
forth ⊗₄ one = one
one ⊗₄ forth = one
half ⊗₄ one = one
one ⊗₄ half = one
one ⊗₄ one = one
_ ⊗₄ _ = zero

I₄ : Four
I₄ = forth

_⊸₄_ : Four → Four → Four
forth ⊸₄ zero = zero
half ⊸₄ zero = zero
one ⊸₄ zero = zero
half ⊸₄ forth = zero
one ⊸₄ forth = zero
one ⊸₄ half = zero
half ⊸₄ half = half
forth ⊸₄ forth = forth
forth ⊸₄ half = half
_ ⊸₄ _ = one

