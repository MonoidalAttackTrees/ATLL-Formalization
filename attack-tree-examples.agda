module attack-tree-examples where

open import prelude
open import lineale
open import functions

{-
a = bribe 
b = break in
c = install
d = steal
-}
ex1 : ∀{a b c d} → (a ⊙₄ (b ▷₄ c)) ⊔₄ (b ▷₄ (d ⊙₄ c)) ≤₄ (a ⊔₄ d) ⊙₄ (b ▷₄ c)
ex1 {zero} {zero} {zero} {zero} = triv
ex1 {zero} {zero} {zero} {forth} = triv
ex1 {zero} {zero} {zero} {half} = triv
ex1 {zero} {zero} {zero} {one} = triv
ex1 {zero} {zero} {forth} {zero} = triv
ex1 {zero} {zero} {forth} {forth} = triv
ex1 {zero} {zero} {forth} {half} = triv
ex1 {zero} {zero} {forth} {one} = triv
ex1 {zero} {zero} {half} {zero} = triv
ex1 {zero} {zero} {half} {forth} = triv
ex1 {zero} {zero} {half} {half} = triv
ex1 {zero} {zero} {half} {one} = triv
ex1 {zero} {zero} {one} {zero} = triv
ex1 {zero} {zero} {one} {forth} = triv
ex1 {zero} {zero} {one} {half} = triv
ex1 {zero} {zero} {one} {one} = triv
ex1 {zero} {forth} {zero} {zero} = triv
ex1 {zero} {forth} {zero} {forth} = triv
ex1 {zero} {forth} {zero} {half} = triv
ex1 {zero} {forth} {zero} {one} = triv
ex1 {zero} {forth} {forth} {zero} = triv
ex1 {zero} {forth} {forth} {forth} = triv
ex1 {zero} {forth} {forth} {half} = triv
ex1 {zero} {forth} {forth} {one} = triv
ex1 {zero} {forth} {half} {zero} = triv
ex1 {zero} {forth} {half} {forth} = triv
ex1 {zero} {forth} {half} {half} = triv
ex1 {zero} {forth} {half} {one} = triv
ex1 {zero} {forth} {one} {zero} = triv
ex1 {zero} {forth} {one} {forth} = triv
ex1 {zero} {forth} {one} {half} = triv
ex1 {zero} {forth} {one} {one} = triv
ex1 {zero} {half} {zero} {zero} = triv
ex1 {zero} {half} {zero} {forth} = triv
ex1 {zero} {half} {zero} {half} = triv
ex1 {zero} {half} {zero} {one} = triv
ex1 {zero} {half} {forth} {zero} = triv
ex1 {zero} {half} {forth} {forth} = triv
ex1 {zero} {half} {forth} {half} = triv
ex1 {zero} {half} {forth} {one} = triv
ex1 {zero} {half} {half} {zero} = triv
ex1 {zero} {half} {half} {forth} = triv
ex1 {zero} {half} {half} {half} = triv
ex1 {zero} {half} {half} {one} = triv
ex1 {zero} {half} {one} {zero} = triv
ex1 {zero} {half} {one} {forth} = triv
ex1 {zero} {half} {one} {half} = triv
ex1 {zero} {half} {one} {one} = triv
ex1 {zero} {one} {zero} {zero} = triv
ex1 {zero} {one} {zero} {forth} = triv
ex1 {zero} {one} {zero} {half} = triv
ex1 {zero} {one} {zero} {one} = triv
ex1 {zero} {one} {forth} {zero} = triv
ex1 {zero} {one} {forth} {forth} = triv
ex1 {zero} {one} {forth} {half} = triv
ex1 {zero} {one} {forth} {one} = triv
ex1 {zero} {one} {half} {zero} = triv
ex1 {zero} {one} {half} {forth} = triv
ex1 {zero} {one} {half} {half} = triv
ex1 {zero} {one} {half} {one} = triv
ex1 {zero} {one} {one} {zero} = triv
ex1 {zero} {one} {one} {forth} = triv
ex1 {zero} {one} {one} {half} = triv
ex1 {zero} {one} {one} {one} = triv
ex1 {forth} {zero} {zero} {zero} = triv
ex1 {forth} {zero} {zero} {forth} = triv
ex1 {forth} {zero} {zero} {half} = triv
ex1 {forth} {zero} {zero} {one} = triv
ex1 {forth} {zero} {forth} {zero} = triv
ex1 {forth} {zero} {forth} {forth} = triv
ex1 {forth} {zero} {forth} {half} = triv
ex1 {forth} {zero} {forth} {one} = triv
ex1 {forth} {zero} {half} {zero} = triv
ex1 {forth} {zero} {half} {forth} = triv
ex1 {forth} {zero} {half} {half} = triv
ex1 {forth} {zero} {half} {one} = triv
ex1 {forth} {zero} {one} {zero} = triv
ex1 {forth} {zero} {one} {forth} = triv
ex1 {forth} {zero} {one} {half} = triv
ex1 {forth} {zero} {one} {one} = triv
ex1 {forth} {forth} {zero} {zero} = triv
ex1 {forth} {forth} {zero} {forth} = triv
ex1 {forth} {forth} {zero} {half} = triv
ex1 {forth} {forth} {zero} {one} = triv
ex1 {forth} {forth} {forth} {zero} = triv
ex1 {forth} {forth} {forth} {forth} = triv
ex1 {forth} {forth} {forth} {half} = triv
ex1 {forth} {forth} {forth} {one} = triv
ex1 {forth} {forth} {half} {zero} = triv
ex1 {forth} {forth} {half} {forth} = triv
ex1 {forth} {forth} {half} {half} = triv
ex1 {forth} {forth} {half} {one} = triv
ex1 {forth} {forth} {one} {zero} = triv
ex1 {forth} {forth} {one} {forth} = triv
ex1 {forth} {forth} {one} {half} = triv
ex1 {forth} {forth} {one} {one} = triv
ex1 {forth} {half} {zero} {zero} = triv
ex1 {forth} {half} {zero} {forth} = triv
ex1 {forth} {half} {zero} {half} = triv
ex1 {forth} {half} {zero} {one} = triv
ex1 {forth} {half} {forth} {zero} = triv
ex1 {forth} {half} {forth} {forth} = triv
ex1 {forth} {half} {forth} {half} = triv
ex1 {forth} {half} {forth} {one} = triv
ex1 {forth} {half} {half} {zero} = triv
ex1 {forth} {half} {half} {forth} = triv
ex1 {forth} {half} {half} {half} = triv
ex1 {forth} {half} {half} {one} = triv
ex1 {forth} {half} {one} {zero} = triv
ex1 {forth} {half} {one} {forth} = triv
ex1 {forth} {half} {one} {half} = triv
ex1 {forth} {half} {one} {one} = triv
ex1 {forth} {one} {zero} {zero} = triv
ex1 {forth} {one} {zero} {forth} = triv
ex1 {forth} {one} {zero} {half} = triv
ex1 {forth} {one} {zero} {one} = triv
ex1 {forth} {one} {forth} {zero} = triv
ex1 {forth} {one} {forth} {forth} = triv
ex1 {forth} {one} {forth} {half} = triv
ex1 {forth} {one} {forth} {one} = triv
ex1 {forth} {one} {half} {zero} = triv
ex1 {forth} {one} {half} {forth} = triv
ex1 {forth} {one} {half} {half} = triv
ex1 {forth} {one} {half} {one} = triv
ex1 {forth} {one} {one} {zero} = triv
ex1 {forth} {one} {one} {forth} = triv
ex1 {forth} {one} {one} {half} = triv
ex1 {forth} {one} {one} {one} = triv
ex1 {half} {zero} {zero} {zero} = triv
ex1 {half} {zero} {zero} {forth} = triv
ex1 {half} {zero} {zero} {half} = triv
ex1 {half} {zero} {zero} {one} = triv
ex1 {half} {zero} {forth} {zero} = triv
ex1 {half} {zero} {forth} {forth} = triv
ex1 {half} {zero} {forth} {half} = triv
ex1 {half} {zero} {forth} {one} = triv
ex1 {half} {zero} {half} {zero} = triv
ex1 {half} {zero} {half} {forth} = triv
ex1 {half} {zero} {half} {half} = triv
ex1 {half} {zero} {half} {one} = triv
ex1 {half} {zero} {one} {zero} = triv
ex1 {half} {zero} {one} {forth} = triv
ex1 {half} {zero} {one} {half} = triv
ex1 {half} {zero} {one} {one} = triv
ex1 {half} {forth} {zero} {zero} = triv
ex1 {half} {forth} {zero} {forth} = triv
ex1 {half} {forth} {zero} {half} = triv
ex1 {half} {forth} {zero} {one} = triv
ex1 {half} {forth} {forth} {zero} = triv
ex1 {half} {forth} {forth} {forth} = triv
ex1 {half} {forth} {forth} {half} = triv
ex1 {half} {forth} {forth} {one} = triv
ex1 {half} {forth} {half} {zero} = triv
ex1 {half} {forth} {half} {forth} = triv
ex1 {half} {forth} {half} {half} = triv
ex1 {half} {forth} {half} {one} = triv
ex1 {half} {forth} {one} {zero} = triv
ex1 {half} {forth} {one} {forth} = triv
ex1 {half} {forth} {one} {half} = triv
ex1 {half} {forth} {one} {one} = triv
ex1 {half} {half} {zero} {zero} = triv
ex1 {half} {half} {zero} {forth} = triv
ex1 {half} {half} {zero} {half} = triv
ex1 {half} {half} {zero} {one} = triv
ex1 {half} {half} {forth} {zero} = triv
ex1 {half} {half} {forth} {forth} = triv
ex1 {half} {half} {forth} {half} = triv
ex1 {half} {half} {forth} {one} = triv
ex1 {half} {half} {half} {zero} = triv
ex1 {half} {half} {half} {forth} = triv
ex1 {half} {half} {half} {half} = triv
ex1 {half} {half} {half} {one} = triv
ex1 {half} {half} {one} {zero} = triv
ex1 {half} {half} {one} {forth} = triv
ex1 {half} {half} {one} {half} = triv
ex1 {half} {half} {one} {one} = triv
ex1 {half} {one} {zero} {zero} = triv
ex1 {half} {one} {zero} {forth} = triv
ex1 {half} {one} {zero} {half} = triv
ex1 {half} {one} {zero} {one} = triv
ex1 {half} {one} {forth} {zero} = triv
ex1 {half} {one} {forth} {forth} = triv
ex1 {half} {one} {forth} {half} = triv
ex1 {half} {one} {forth} {one} = triv
ex1 {half} {one} {half} {zero} = triv
ex1 {half} {one} {half} {forth} = triv
ex1 {half} {one} {half} {half} = triv
ex1 {half} {one} {half} {one} = triv
ex1 {half} {one} {one} {zero} = triv
ex1 {half} {one} {one} {forth} = triv
ex1 {half} {one} {one} {half} = triv
ex1 {half} {one} {one} {one} = triv
ex1 {one} {zero} {zero} {zero} = triv
ex1 {one} {zero} {zero} {forth} = triv
ex1 {one} {zero} {zero} {half} = triv
ex1 {one} {zero} {zero} {one} = triv
ex1 {one} {zero} {forth} {zero} = triv
ex1 {one} {zero} {forth} {forth} = triv
ex1 {one} {zero} {forth} {half} = triv
ex1 {one} {zero} {forth} {one} = triv
ex1 {one} {zero} {half} {zero} = triv
ex1 {one} {zero} {half} {forth} = triv
ex1 {one} {zero} {half} {half} = triv
ex1 {one} {zero} {half} {one} = triv
ex1 {one} {zero} {one} {zero} = triv
ex1 {one} {zero} {one} {forth} = triv
ex1 {one} {zero} {one} {half} = triv
ex1 {one} {zero} {one} {one} = triv
ex1 {one} {forth} {zero} {zero} = triv
ex1 {one} {forth} {zero} {forth} = triv
ex1 {one} {forth} {zero} {half} = triv
ex1 {one} {forth} {zero} {one} = triv
ex1 {one} {forth} {forth} {zero} = triv
ex1 {one} {forth} {forth} {forth} = triv
ex1 {one} {forth} {forth} {half} = triv
ex1 {one} {forth} {forth} {one} = triv
ex1 {one} {forth} {half} {zero} = triv
ex1 {one} {forth} {half} {forth} = triv
ex1 {one} {forth} {half} {half} = triv
ex1 {one} {forth} {half} {one} = triv
ex1 {one} {forth} {one} {zero} = triv
ex1 {one} {forth} {one} {forth} = triv
ex1 {one} {forth} {one} {half} = triv
ex1 {one} {forth} {one} {one} = triv
ex1 {one} {half} {zero} {zero} = triv
ex1 {one} {half} {zero} {forth} = triv
ex1 {one} {half} {zero} {half} = triv
ex1 {one} {half} {zero} {one} = triv
ex1 {one} {half} {forth} {zero} = triv
ex1 {one} {half} {forth} {forth} = triv
ex1 {one} {half} {forth} {half} = triv
ex1 {one} {half} {forth} {one} = triv
ex1 {one} {half} {half} {zero} = triv
ex1 {one} {half} {half} {forth} = triv
ex1 {one} {half} {half} {half} = triv
ex1 {one} {half} {half} {one} = triv
ex1 {one} {half} {one} {zero} = triv
ex1 {one} {half} {one} {forth} = triv
ex1 {one} {half} {one} {half} = triv
ex1 {one} {half} {one} {one} = triv
ex1 {one} {one} {zero} {zero} = triv
ex1 {one} {one} {zero} {forth} = triv
ex1 {one} {one} {zero} {half} = triv
ex1 {one} {one} {zero} {one} = triv
ex1 {one} {one} {forth} {zero} = triv
ex1 {one} {one} {forth} {forth} = triv
ex1 {one} {one} {forth} {half} = triv
ex1 {one} {one} {forth} {one} = triv
ex1 {one} {one} {half} {zero} = triv
ex1 {one} {one} {half} {forth} = triv
ex1 {one} {one} {half} {half} = triv
ex1 {one} {one} {half} {one} = triv
ex1 {one} {one} {one} {zero} = triv
ex1 {one} {one} {one} {forth} = triv
ex1 {one} {one} {one} {half} = triv
ex1 {one} {one} {one} {one} = triv

ex1-inv : Σ[ a ∈ Four ](Σ[ b ∈ Four ](Σ[ c ∈ Four ](Σ[ d ∈ Four ]((a ⊔₄ d) ⊙₄ (b ▷₄ c) ≤₄ (a ⊙₄ (b ▷₄ c)) ⊔₄ (b ▷₄ (d ⊙₄ c)) → ⊥ {lzero}))))
ex1-inv = zero , (forth , (forth , (forth , id)))

{-
a = bribe 
b = break in
c = install
d = steal
-}
ex2 : Σ[ a ∈ Four ](Σ[ b ∈ Four ](Σ[ c ∈ Four ](Σ[ d ∈ Four ]((a ⊔₄ d) ⊙₄ (b ▷₄ c) ≤₄ b ▷₄ (d ⊙₄ c) → ⊥ {lzero}))))
ex2 = zero , (forth , (forth , (forth , id)))
