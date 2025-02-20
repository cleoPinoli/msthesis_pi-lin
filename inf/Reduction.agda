{-# OPTIONS --guardedness #-}

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
    cut d p (box (link e (split-l (split-r split-e)))) (box P) ~> #process (#cons p) P .∞Process.unbox

  r-close :
    ∀{Γ}
    {P : Process Γ} (p : Γ ≃ [] + Γ) (q : Γ ≃ [] + Γ) ->
    cut dual-one-bot p (box close) ( box (wait (split-l q) (box P))) ~> P

  r-fail :
    ∀{Γ Γ₁ Γ₂ Δ A B}
    {P : Process (B :: Γ₂)}
    {d : Dual A B}
    {p : Γ ≃ Γ₁ + Γ₂}
    (q : Γ₁ ≃ [ Top ] + Δ)
    ->
    let _ , p' , q' = +-assoc-l p q in    
    cut d p (box (fail (split-r q))) (box P) ~> fail q' 

  r-left :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₁ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : ∞Dual A₁ B₁) (d₂ : ∞Dual A₂ B₂) --queste nel frammento finito erano Dual, ho provato a giocare con un box per mantenere Dual qui ma è un po' rognoso
    (p : Γ ≃ Γ₁ + Γ₂) (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂)
    ->
    cut (dual-plus-with d₁ d₂) p (box (select true (split-l q₁) (box P))) (box (case (split-l q₂) (box Q) (box R))) ~> cut (d₁ .∞Dual.unbox) p (box P) (box Q)


  r-right :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₂ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : ∞Dual A₁ B₁) (d₂ : ∞Dual A₂ B₂)
    (p : Γ ≃ Γ₁ + Γ₂) (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂)
    ->
    cut (dual-plus-with d₁ d₂) p (box (select false (split-l q₁) (box P))) (box (case (split-l q₂) (box Q) (box R))) ~> cut (d₂ .∞Dual.unbox) p (box P) (box R)

  r-cut :
    ∀{Γ Γ₁ Γ₂ A B}
    {P Q : Process (A :: Γ₁)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (q : Γ ≃ Γ₁ + Γ₂)
    (r : P ~> Q) ->
    cut d q (box P) (box R) ~> cut d q (box Q) (box R)

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


