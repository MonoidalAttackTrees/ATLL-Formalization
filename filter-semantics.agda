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
forth ⊙F forth = half
forth ⊙F half  = half
forth ⊙F one   = half
half  ⊙F forth = half
half  ⊙F half  = half
half  ⊙F one   = half
one   ⊙F forth = half
one   ⊙F half  = half
one   ⊙F one   = half
_     ⊙F _     = zero

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
