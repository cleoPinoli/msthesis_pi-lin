module Termination where

open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat
import Data.Nat.Properties as NatProp
open import Data.Product using (_×_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Bool using (true; false)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process
open import Reduction
open import Congruence
-- open import DeadlockFreedom


size : ∀{Γ} -> Process Γ -> ℕ
size (close) = zero
size (link _ _) = zero
size (fail _ ) = zero
size (wait _ P) = suc (size P)
size (select _ _ P) = suc (size P)
size (case _ P Q) = suc (size P ⊔ size Q) 
size (cut _ _ P Q) = suc (size P + size Q)
-- size (fork _ _ P Q) = suc (size P + size Q)
-- size (join _ P) = suc (size P)

#size : ∀{Γ Δ} (P : Process Γ) (π : Γ # Δ) -> size (#process π P) ≡ size P
#size (close) π with #one π --Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl = refl
#size (link d p) π with #one+ π p
... | Δ' , _ , π' with #one π'
... | refl = refl
#size (fail p) π = refl
#size (wait p P) π with #one+ π p
... | Δ' , q , π' = cong suc (#size P π')
#size (select x p P) π with #one+ π p
... | Δ' , q , π' = cong suc (#size P (#next π'))
#size (case p P Q) π with #one+ π p
... | Δ' , q , π'
  rewrite #size P (#next π') | #size Q (#next π') = refl
#size (cut d p P Q) π with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂
  rewrite #size P (#next π₁) | #size Q (#next π₂) = refl


-- precongruence preserves process size
size-⊒ : ∀{Γ} {P Q : Process Γ} -> P ⊒ Q -> size Q ≡ size P
size-⊒ {_} {cut _ _ P Q} (s-comm d d' p p') rewrite NatProp.+-comm (size P) (size Q)  = refl
size-⊒ {_} {cut _ _ P (cut _ _ Q R)} (s-assoc-r d e p q p' q')
  rewrite #size Q #here = begin
  suc ((suc (size P) + size Q) + size R)
  ≡⟨ cong suc (cong suc (NatProp.+-assoc (size P) (size Q) (size R))) ⟩
  suc (suc (size P) + (size Q + size R))
  ≡⟨ cong suc (Eq.sym (NatProp.+-suc (size P) (size Q + size R)) ) ⟩
  suc (size P + suc (size Q + size R)) ∎
  where open Eq.≡-Reasoning
size-⊒ {_} (s-link d p) = refl
size-⊒ {_} (s-wait d p q) = refl
size-⊒ {_} {cut _ _ (case _ P Q) R} (s-case d p q)
 rewrite #size P #here |
         #size Q #here |
         NatProp.+-distribʳ-⊔ (size R) (size P) (size Q) = refl
size-⊒ s-refl = refl
size-⊒ {_} (s-tran pc₁ pc₂) = Eq.trans (size-⊒ pc₂) (size-⊒ pc₁)
size-⊒ {_} {cut _ _ P R} (s-cong-l d p pc) = cong (_+ size R) (cong suc (size-⊒ pc))
size-⊒ {_} {cut _ _ (select _ _ P) Q} (s-select-l d p q)
  rewrite #size P #here = refl
size-⊒ {_} {cut _ _ (select _ _ P) Q} (s-select-r d p q)
  rewrite #size P #here = refl


-- redux always decreases process size
size-r : ∀{Γ} {P Q : Process Γ} -> P ~> Q -> size Q < size P
size-r {_} {cut _ _ (link _ _) P} (r-link d e p) rewrite #size P (#cons p) = s≤s NatProp.≤-refl
size-r {_} {cut _ _ (close) (wait _ Q)} (r-close p q) = s≤s (NatProp.n≤1+n (size Q))  
size-r {_} (r-fail p) = s≤s z≤n
size-r {_} {cut _ _ (select true _ P) (case _ Q R)} (r-left d e p q r) = begin
  suc (suc (size P + size Q)) ≡⟨ cong suc (Eq.sym (NatProp.+-suc (size P) (size Q))) ⟩
  suc (size P + suc (size Q)) <⟨ s≤s (s≤s (NatProp.+-monoʳ-≤ (size P) (s≤s (NatProp.m≤m⊔n (size Q) (size R))))) ⟩
  suc (suc (size P + suc (size Q ⊔ size R))) ∎
  where open NatProp.≤-Reasoning
size-r {_} {cut _ _ (select false _ P) (case _ Q R)} (r-right d e p q r) = begin
  suc (suc (size P + size R)) ≡⟨ cong suc (Eq.sym (NatProp.+-suc (size P) (size R))) ⟩
  suc (size P + suc (size R)) <⟨ s≤s (s≤s (NatProp.+-monoʳ-≤ (size P) (s≤s (NatProp.n≤m⊔n ((size Q)) (size R))))) ⟩
  suc (suc (size P + suc (size Q ⊔ size R))) ∎
  where open NatProp.≤-Reasoning
size-r {_} {cut _ _ P R} (r-cut d q red) = s≤s (NatProp.+-monoˡ-≤ (size R) (size-r red)) 
size-r (r-cong p red) rewrite Eq.sym (size-⊒ p) = size-r red

-- => is what is sometimes called ∼>*
--termination : ∀{Γ} (P : Process Γ) -> ∃[ Q ] ((P => Q) × (Observable Q))
-- termination P = {!!} -- import DeadlockFreedom, adapt languages *somehow*, check close-related stuff (*again, somehow*) and fork-join bizness
