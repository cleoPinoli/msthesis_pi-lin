module Reduction where

open import Data.Bool using (Bool)
open Bool using (true; false)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Type
open import Context
open import Process
open import Congruence

data _~>_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  r-link :
    ∀{Γ Δ A B}
    {P : Process (B :: Δ)}
    (d : Dual A B) (e : Dual A B)
    (p : Γ ≃ [ B ] + Δ) ->
    cut d p (link e (split-l (split-r split-e))) P ~> #process (#cons p)  P

  r-close :
    ∀{Γ}
    {P : Process Γ} (p : Γ ≃ [] + Γ) (q : Γ ≃ [] + Γ) ->
    cut dual-one-bot p (close) (wait (split-l q) P) ~> P

  r-fail :
    ∀{Γ Γ₁ Γ₂ Δ A B}
    {P : Process (B :: Γ₂)}
    {d : Dual A B}
    {p : Γ ≃ Γ₁ + Γ₂}
    (q : Γ₁ ≃ [ Top ] + Δ)
    ->
    let _ , p' , q' = +-assoc-l p q in    
    cut d p (fail (split-r q)) P ~> fail q' 

  r-left :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₁ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : Dual A₁ B₁) (d₂ : Dual A₂ B₂)
    (p : Γ ≃ Γ₁ + Γ₂) (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂)
    ->
    cut (dual-plus-with d₁ d₂) p (select true (split-l q₁) P) (case (split-l q₂) Q R) ~> cut d₁ p P Q

  r-right :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₂ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : Dual A₁ B₁) (d₂ : Dual A₂ B₂)
    (p : Γ ≃ Γ₁ + Γ₂) (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂)
    ->
    cut (dual-plus-with d₁ d₂) p (select false (split-l q₁) P) (case (split-l q₂) Q R) ~> cut d₂ p P R

  r-cut :
    ∀{Γ Γ₁ Γ₂ A B}
    {P Q : Process (A :: Γ₁)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (q : Γ ≃ Γ₁ + Γ₂)
    (r : P ~> Q) ->
    cut d q P R ~> cut d q Q R

-- provided that P ⊒ R and R ~> Q then P ~> Q
  r-cong :
    ∀{Γ}
    {P R Q : Process Γ}
    (p : P ⊒ R) (q : R ~> Q) -> P ~> Q


-- P is Reducible if P ~> Q for some Q.
Reducible : ∀{Γ} -> Process Γ -> Set
Reducible P = ∃[ Q ] (P ~> Q)

data _=>_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  refl : ∀{Γ} {P : Process Γ} -> P => P
  tran : ∀{Γ} {P Q R : Process Γ} -> P ~> R -> R => Q -> P => Q


