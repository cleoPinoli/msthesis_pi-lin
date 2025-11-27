open import Data.Sum
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_; contradiction)
open import Data.List.Base using ([]; _∷_; [_])

open import Type
open import Context
open import Process
open import Congruence
open import Reduction
open import DeadlockFreedom

data ReductionContext {n} (Δ : Context n) : Context n → Set where
  hole   : ReductionContext Δ Δ
  cut-l  : ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
           ReductionContext Δ (A ∷ Γ₁) → Process (B ∷ Γ₂) →
           ReductionContext Δ Γ
  cut-r  : ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
           Process (A ∷ Γ₁) → ReductionContext Δ (B ∷ Γ₂) →
           ReductionContext Δ Γ

_⟦_⟧ : ∀{n} {Γ Δ : Context n} → ReductionContext Δ Γ → Process Δ → Process Γ
hole ⟦ P ⟧           = P
cut-l d p 𝒞 Q ⟦ P ⟧  = cut d p (𝒞 ⟦ P ⟧) Q
cut-r d p Q 𝒞 ⟦ P ⟧  = cut d p Q (𝒞 ⟦ P ⟧)

WellFormed        : ∀{n} {Γ : Context n} → Process Γ → Set
WellFormed {n} {Γ} P = ∀{Δ : Context n} {𝒞 : ReductionContext Δ Γ} {Q : Process Δ} →
                    P ⊒ (𝒞 ⟦ Q ⟧) → Alive Q

type-safety : ∀{n} {Γ : Context n} (P : Process Γ) → WellFormed P
type-safety P {_} {_} {Q} _ = deadlock-freedom Q
