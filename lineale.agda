module lineale where

open import level
open import empty
open import unit
open import eq
open import functions

data Four : Set where
  zero : Four
  half : Four
  one : Four
  two : Four

infix 3 _≤₄_

_≤₄_ : Four → Four → Set
half ≤₄ zero = ⊥
one ≤₄ zero = ⊥
one ≤₄ half = ⊥
two ≤₄ zero = ⊥
two ≤₄ half = ⊥
two ≤₄ one = ⊥
_ ≤₄ _ = ⊤

_⊗₄_ : Four → Four → Four
half ⊗₄ half = half
half ⊗₄ one = one
one ⊗₄ half = one
one ⊗₄ one = one
half ⊗₄ two = two
two ⊗₄ half = two
one ⊗₄ two = two
two ⊗₄ one = two
two ⊗₄ two = two
_ ⊗₄ _ = zero

I₄ : Four
I₄ = half

_⊸₄_ : Four → Four → Four
half ⊸₄ zero = zero
one ⊸₄ zero = zero
two ⊸₄ zero = zero
one ⊸₄ half = zero
two ⊸₄ half = zero
two ⊸₄ one = zero
one ⊸₄ one = one
half ⊸₄ half = half
half ⊸₄ one = one
_ ⊸₄ _ = two

_⊔₄_ : Four → Four → Four
two ⊔₄ _ = two
_ ⊔₄ two = two
one ⊔₄ _ = one
_ ⊔₄ one = one
half ⊔₄ _ = half
_ ⊔₄ half = half
zero ⊔₄ zero = zero

_⊙₄_ : Four → Four → Four
half ⊙₄ half = one
half ⊙₄ one = one
one ⊙₄ half = one
one ⊙₄ one = one
half ⊙₄ two = one
two ⊙₄ half = one
one ⊙₄ two = one
two ⊙₄ one = one
two ⊙₄ two = one
_ ⊙₄ _ = zero

_▷₄_ : Four → Four → Four
half ▷₄ one = half
one ▷₄ half = one
half ▷₄ half = half
one ▷₄ one = one
two ▷₄ half = one
half ▷₄ two = half
two ▷₄ one = one
one ▷₄ two = one
two ▷₄ two = one
_ ▷₄ _ = zero
