module quaternary-semantics where

open import level
open import empty
open import unit
open import eq
open import functions
open import product

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
one   ⊔₄ _     = one
_     ⊔₄ one   = one
half  ⊔₄ _     = half
_     ⊔₄ half  = half
forth ⊔₄ _     = forth
_     ⊔₄ forth = forth
zero  ⊔₄ zero  = zero

_□₄_ : Four → Four → Four
zero  □₄ zero  = zero
zero  □₄ forth = zero
zero  □₄ half  = zero
zero  □₄ one   = zero
forth □₄ zero  = zero
half  □₄ zero  = zero
one   □₄ zero  = zero
forth □₄ forth = half
forth □₄ half  = half
forth □₄ one   = half
half  □₄ forth = half
half  □₄ half  = half
half  □₄ one   = half
one   □₄ forth = half
one   □₄ half  = half
one   □₄ one   = half

_⊙₄_ : Four → Four → Four
zero  ⊙₄ zero  = zero
zero  ⊙₄ forth = zero
zero  ⊙₄ half  = zero
zero  ⊙₄ one   = zero
forth ⊙₄ zero  = zero
half  ⊙₄ zero  = zero
one   ⊙₄ zero  = zero
forth ⊙₄ forth = one
forth ⊙₄ half  = one
forth ⊙₄ one   = one
half  ⊙₄ forth = one
half  ⊙₄ half  = one
half  ⊙₄ one   = one
one   ⊙₄ forth = one
one   ⊙₄ half  = one
one   ⊙₄ one   = one

_▷₄_ : Four → Four → Four
half  ▷₄ forth = one
half  ▷₄ half  = one
half  ▷₄ one   = one
one   ▷₄ forth = one
one   ▷₄ half  = one
one   ▷₄ one   = one
forth ▷₄ half  = forth
forth ▷₄ forth = forth
forth ▷₄ one   = forth
_     ▷₄ _     = zero

_◇₄_ : Four → Four → Four
half  ◇₄ forth = half
half  ◇₄ half  = half
half  ◇₄ one   = half
one   ◇₄ forth = half
one   ◇₄ half  = half
one   ◇₄ one   = half
forth ◇₄ half  = forth
forth ◇₄ forth = forth
forth ◇₄ one   = forth
_     ◇₄ _     = zero

_→₄_ : Four → Four → Four
zero →₄ zero = one
forth →₄ zero = zero
half →₄ zero = zero
one →₄ zero = zero
zero →₄ forth = one
forth →₄ forth = forth
half →₄ forth = forth
one →₄ forth  = forth
zero →₄ half = one
forth →₄ half = forth
half →₄ half = forth
one →₄ half = forth
zero →₄ one = one
forth →₄ one = one
half →₄ one = one
one →₄ one = one

_←₄_ : Four → Four → Four
zero ←₄ zero = one
forth ←₄ zero = one
half ←₄ zero = one
one ←₄ zero = one
zero ←₄ forth = zero
forth ←₄ forth = one
half ←₄ forth = one
one ←₄ forth = one
zero ←₄ half = zero
forth ←₄ half = zero
half ←₄ half = zero
one ←₄ half = one
zero ←₄ one = zero
forth ←₄ one = zero
half ←₄ one = zero
one ←₄ one = one

