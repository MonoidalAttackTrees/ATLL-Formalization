module filter-semantics where

open import quaternary-semantics

_⊔F_ : Four → Four → Four
one   ⊔F _     = one
_     ⊔F one   = one
half  ⊔F _     = half
_     ⊔F half  = half
forth ⊔F _     = forth
_     ⊔F forth = forth
zero  ⊔F zero  = zero

_⊙F_ : Four → Four → Four
zero  ⊙F zero  = zero
zero  ⊙F forth = zero
zero  ⊙F half  = zero
zero  ⊙F one   = zero
forth ⊙F zero  = zero
half  ⊙F zero  = zero
one   ⊙F zero  = zero
forth ⊙F forth = forth
forth ⊙F half  = forth
forth ⊙F one   = forth
half  ⊙F forth = forth
half  ⊙F half  = forth
half  ⊙F one   = forth
one   ⊙F forth = forth
one   ⊙F half  = forth
one   ⊙F one   = forth

_▷F_ : Four → Four → Four
half  ▷F forth = one
half  ▷F half  = one
half  ▷F one   = one
one   ▷F forth = one
one   ▷F half  = one
one   ▷F one   = one
forth ▷F half  = forth
forth ▷F forth = forth
forth ▷F one   = forth
_     ▷F _     = zero

_→F_ : Four → Four → Four
zero →F zero = one
forth →F zero = zero
half →F zero = zero
one →F zero = zero
zero →F forth = one
forth →F forth = forth
half →F forth = forth
one →F forth  = forth
zero →F half = one
forth →F half = forth
half →F half = forth
one →F half = forth
zero →F one = one
forth →F one = one
half →F one = one
one →F one = one

_←F_ : Four → Four → Four
zero ←F zero = one
forth ←F zero = one
half ←F zero = one
one ←F zero = one
zero ←F forth = zero
forth ←F forth = one
half ←F forth = one
one ←F forth = one
zero ←F half = zero
forth ←F half = zero
half ←F half = zero
one ←F half = one
zero ←F one = zero
forth ←F one = zero
half ←F one = zero
one ←F one = one

