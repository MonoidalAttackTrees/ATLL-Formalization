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
half ▷₄ forth = one
forth ▷₄ forth = forth
forth ▷₄ one = forth
half ▷₄ half = one
one ▷₄ forth = one
one ▷₄ half = one
half ▷₄ one = one
one ▷₄ one = one
_ ▷₄ _ = zero

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

←-curry : ∀{a b c} → (a ▷₄ b) ≤₄ c → b ≤₄ (c ←₄ a)
←-curry {zero} {zero} {zero} triv = triv
←-curry {zero} {zero} {forth} triv = triv
←-curry {zero} {zero} {half} triv = triv
←-curry {zero} {zero} {one} triv = triv
←-curry {zero} {forth} {zero} h = triv
←-curry {zero} {forth} {forth} h = triv
←-curry {zero} {forth} {half} h = triv
←-curry {zero} {forth} {one} h = triv
←-curry {zero} {half} {zero} h = triv
←-curry {zero} {half} {forth} h = triv
←-curry {zero} {half} {half} h = triv
←-curry {zero} {half} {one} h = triv
←-curry {zero} {one} {zero} h = triv
←-curry {zero} {one} {forth} h = triv
←-curry {zero} {one} {half} h = triv
←-curry {zero} {one} {one} h = triv
←-curry {forth} {zero} {zero} triv = triv
←-curry {forth} {zero} {forth} triv = triv
←-curry {forth} {zero} {half} triv = triv
←-curry {forth} {zero} {one} triv = triv
←-curry {forth} {forth} {zero} ()
←-curry {forth} {forth} {forth} h = triv
←-curry {forth} {forth} {half} h = triv
←-curry {forth} {forth} {one} h = triv
←-curry {forth} {half} {zero} ()
←-curry {forth} {half} {forth} h = triv
←-curry {forth} {half} {half} h = triv
←-curry {forth} {half} {one} h = triv
←-curry {forth} {one} {zero} ()
←-curry {forth} {one} {forth} h = triv
←-curry {forth} {one} {half} h = triv
←-curry {forth} {one} {one} h = triv
←-curry {half} {zero} {zero} triv = triv
←-curry {half} {zero} {forth} triv = triv
←-curry {half} {zero} {half} triv = triv
←-curry {half} {zero} {one} triv = triv
←-curry {half} {forth} {zero} ()
←-curry {half} {forth} {forth} ()
←-curry {half} {forth} {half} ()
←-curry {half} {forth} {one} h = triv
←-curry {half} {half} {zero} ()
←-curry {half} {half} {forth} ()
←-curry {half} {half} {half} ()
←-curry {half} {half} {one} h = triv
←-curry {half} {one} {zero} ()
←-curry {half} {one} {forth} ()
←-curry {half} {one} {half} ()
←-curry {half} {one} {one} h = triv
←-curry {one} {zero} {zero} triv = triv
←-curry {one} {zero} {forth} triv = triv
←-curry {one} {zero} {half} triv = triv
←-curry {one} {zero} {one} triv = triv
←-curry {one} {forth} {zero} ()
←-curry {one} {forth} {forth} ()
←-curry {one} {forth} {half} ()
←-curry {one} {forth} {one} h = triv
←-curry {one} {half} {zero} ()
←-curry {one} {half} {forth} ()
←-curry {one} {half} {half} ()
←-curry {one} {half} {one} h = triv
←-curry {one} {one} {zero} ()
←-curry {one} {one} {forth} ()
←-curry {one} {one} {half} ()
←-curry {one} {one} {one} h = triv

←-curry-inv : ∀{a b c} → b ≤₄ (c ←₄ a) → (a ▷₄ b) ≤₄ c
←-curry-inv {zero} {zero} {zero} h = triv
←-curry-inv {zero} {zero} {forth} h = triv
←-curry-inv {zero} {zero} {half} h = triv
←-curry-inv {zero} {zero} {one} h = triv
←-curry-inv {zero} {forth} {zero} h = triv
←-curry-inv {zero} {forth} {forth} h = triv
←-curry-inv {zero} {forth} {half} h = triv
←-curry-inv {zero} {forth} {one} h = triv
←-curry-inv {zero} {half} {zero} h = triv
←-curry-inv {zero} {half} {forth} h = triv
←-curry-inv {zero} {half} {half} h = triv
←-curry-inv {zero} {half} {one} h = triv
←-curry-inv {zero} {one} {zero} h = triv
←-curry-inv {zero} {one} {forth} h = triv
←-curry-inv {zero} {one} {half} h = triv
←-curry-inv {zero} {one} {one} h = triv
←-curry-inv {forth} {zero} {zero} h = triv
←-curry-inv {forth} {zero} {forth} h = triv
←-curry-inv {forth} {zero} {half} h = triv
←-curry-inv {forth} {zero} {one} h = triv
←-curry-inv {forth} {forth} {zero} ()
←-curry-inv {forth} {forth} {forth} h = triv
←-curry-inv {forth} {forth} {half} h = triv
←-curry-inv {forth} {forth} {one} h = triv
←-curry-inv {forth} {half} {zero} ()
←-curry-inv {forth} {half} {forth} h = triv
←-curry-inv {forth} {half} {half} h = triv
←-curry-inv {forth} {half} {one} h = triv
←-curry-inv {forth} {one} {zero} ()
←-curry-inv {forth} {one} {forth} h = triv
←-curry-inv {forth} {one} {half} h = triv
←-curry-inv {forth} {one} {one} h = triv
←-curry-inv {half} {zero} {zero} h = triv
←-curry-inv {half} {zero} {forth} h = triv
←-curry-inv {half} {zero} {half} h = triv
←-curry-inv {half} {zero} {one} h = triv
←-curry-inv {half} {forth} {zero} ()
←-curry-inv {half} {forth} {forth} ()
←-curry-inv {half} {forth} {half} ()
←-curry-inv {half} {forth} {one} h = triv
←-curry-inv {half} {half} {zero} ()
←-curry-inv {half} {half} {forth} ()
←-curry-inv {half} {half} {half} ()
←-curry-inv {half} {half} {one} h = triv
←-curry-inv {half} {one} {zero} ()
←-curry-inv {half} {one} {forth} ()
←-curry-inv {half} {one} {half} ()
←-curry-inv {half} {one} {one} h = triv
←-curry-inv {one} {zero} {zero} h = triv
←-curry-inv {one} {zero} {forth} h = triv
←-curry-inv {one} {zero} {half} h = triv
←-curry-inv {one} {zero} {one} h = triv
←-curry-inv {one} {forth} {zero} ()
←-curry-inv {one} {forth} {forth} ()
←-curry-inv {one} {forth} {half} ()
←-curry-inv {one} {forth} {one} h = triv
←-curry-inv {one} {half} {zero} ()
←-curry-inv {one} {half} {forth} ()
←-curry-inv {one} {half} {half} ()
←-curry-inv {one} {half} {one} h = triv
←-curry-inv {one} {one} {zero} ()
←-curry-inv {one} {one} {forth} ()
←-curry-inv {one} {one} {half} ()
←-curry-inv {one} {one} {one} h = triv
