module ideal-semantics where

open import quaternary-semantics

_⊔I_ : Four → Four → Four
one   ⊔I _     = one
_     ⊔I one   = one
half  ⊔I _     = half
_     ⊔I half  = half
forth ⊔I _     = forth
_     ⊔I forth = forth
zero  ⊔I zero  = zero

_⊙I_ : Four → Four → Four
zero  ⊙I zero  = zero
zero  ⊙I forth = zero
zero  ⊙I half  = zero
zero  ⊙I one   = zero
forth ⊙I zero  = zero
half  ⊙I zero  = zero
one   ⊙I zero  = zero
forth ⊙I forth = one
forth ⊙I half  = one
forth ⊙I one   = one
half  ⊙I forth = one
half  ⊙I half  = one
half  ⊙I one   = one
one   ⊙I forth = one
one   ⊙I half  = one
one   ⊙I one   = one

_▷I_ : Four → Four → Four
half  ▷I forth = half
half  ▷I half  = half
half  ▷I one   = half
one   ▷I forth = half
one   ▷I half  = half
one   ▷I one   = half
forth ▷I half  = forth
forth ▷I forth = forth
forth ▷I one   = forth
_     ▷I _     = zero

