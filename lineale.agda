module lineale where

open import level
open import empty
open import unit
open import eq
open import functions

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

_⊔₄_ : Four → Four → Four
one ⊔₄ _ = one
_ ⊔₄ one = one
half ⊔₄ _ = half
_ ⊔₄ half = half
forth ⊔₄ _ = forth
_ ⊔₄ forth = forth
zero ⊔₄ zero = zero

_⊙₄_ : Four → Four → Four
forth ⊙₄ forth = one
forth ⊙₄ half = one
half ⊙₄ forth = one
half ⊙₄ half = one
forth ⊙₄ one = one
one ⊙₄ forth = one
half ⊙₄ one = one
one ⊙₄ half = one
one ⊙₄ one = one
_ ⊙₄ _ = zero

_▷₄_ : Four → Four → Four
forth ▷₄ half = forth
half ▷₄ forth = half
forth ▷₄ forth = forth
half ▷₄ half = half
one ▷₄ forth = half
forth ▷₄ one = forth
one ▷₄ half = half
half ▷₄ one = half
one ▷₄ one = half
_ ▷₄ _ = zero
