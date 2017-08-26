open import prelude
open import lineale
open import lineale-thms
open import dialectica-cat
open import dialectica-smcc
open import dialectica-at-ops
open import attack-tree

module dialectica-semantics {𝔹 : Set} {pf : dec 𝔹} where

infix 21 ⟦_⟧_

⟦_⟧_ : ATree {𝔹} {pf} → (𝔹 → Obj) → Obj
⟦ NODE b ⟧ α = α b
⟦ AND t₁ t₂ ⟧ α = ⟦ t₁ ⟧ α ⊙ ⟦ t₂ ⟧ α
⟦ OR t₁ t₂ ⟧ α = ⟦ t₁ ⟧ α ⊔ₒ ⟦ t₂ ⟧ α
⟦ SAND t₁ t₂ ⟧ α = ⟦ t₁ ⟧ α ▷ ⟦ t₂ ⟧ α

⟿-interp : ∀{t₁ t₂ : ATree {𝔹} {pf}}{α : 𝔹 → Obj}
  → t₁ ⟿ t₂
  → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
⟿-interp {.(OR _ _)} {.(OR _ _)} ⟿-OR-sym = ⊔-β
⟿-interp {.(AND _ _)} {.(AND _ _)} ⟿-AND-sym = ⊙-β
⟿-interp {.(OR _ (OR _ _))} {.(OR (OR _ _) _)} ⟿-OR-assoc = ⊔-α-inv
⟿-interp {.(AND _ (AND _ _))} {.(AND (AND _ _) _)} ⟿-AND-assoc = ⊙-α-inv
⟿-interp {.(SAND _ (SAND _ _))} {.(SAND (SAND _ _) _)} ⟿-SAND-assoc = ▷-α-inv
⟿-interp {.(AND _ (OR _ _))} {.(OR (AND _ _) (AND _ _))} ⟿-AND-distl = ⊔-⊙-distl
⟿-interp {.(SAND _ (OR _ _))} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-distl = ⊔-▷-distl
⟿-interp {.(AND (OR _ _) _)} {.(OR (AND _ _) (AND _ _))} ⟿-AND-distr = ⊔-⊙-distr
⟿-interp {.(SAND (OR _ _) _)} {.(OR (SAND _ _) (SAND _ _))} ⟿-SAND-distr = ⊔-▷-distr
⟿-interp {.(AND _ _)} {.(AND _ _)} (⟿-AND₁ p) = (⟿-interp p) ⊙ₐ id
⟿-interp {.(AND _ _)} {.(AND _ _)} (⟿-AND₂ p) = id ⊙ₐ (⟿-interp p)
⟿-interp {.(OR _ _)} {.(OR _ _)} (⟿-OR₁ p) = (⟿-interp p) ⊔ₐ id
⟿-interp {.(OR _ _)} {.(OR _ _)} (⟿-OR₂ p) = id ⊔ₐ (⟿-interp p)
⟿-interp {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₁ p) = (⟿-interp p) ▷ₐ id
⟿-interp {.(SAND _ _)} {.(SAND _ _)} (⟿-SAND₂ p) = id ▷ₐ (⟿-interp p)
⟿-interp {.(OR t₂ t₂)} {t₂} ⟿-contract = ⊔-contract

⟿*-interp : ∀{t₁ t₂ : ATree {𝔹} {pf}}{α : 𝔹 → Obj}
  → t₁ ⟿* t₂
  → Hom (⟦ t₁ ⟧ α) (⟦ t₂ ⟧ α)
⟿*-interp {t₁} {t₂} (⟿-step p) = ⟿-interp p
⟿*-interp {t₁} {.t₁} ⟿-refl = id
⟿*-interp {t₁} {t₃} (⟿-trans {_}{t₂}{_} p₁ p₂) = ⟿*-interp p₁ ○ ⟿*-interp p₂

⟱-interp : ∀{t₁ t₂ : ATree {𝔹} {pf}}{α : 𝔹 → Obj}
  → t₁ ⟱ t₂
  → Σ[ S ∈ Obj ]( (Hom (⟦ t₁ ⟧ α) S) × Hom (⟦ t₂ ⟧ α) S )
⟱-interp {t₁} {t₂}{α} (s , p₁ , p₂) = ⟦ s ⟧ α , (⟿*-interp p₁) , (⟿*-interp p₂)
