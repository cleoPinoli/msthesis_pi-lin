open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as NatProp
open import Data.Product using (_×_)
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Nullary using (¬_)

open import List
open import Type
open import Context

data Process (Γ : Context) : Set where
   Close : Γ ≃ [ One ] + [] -> Process Γ
   Link  : ∀{A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ])
           -> Process Γ
   Fail  : ∀{Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   Wait  : ∀{Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   Select : ∀{Δ A B}
            (x : Bool)
            (p : Γ ≃ [ A ⊕ B ] + Δ)
            -> Process ((if x then A else B) :: Δ)
            -> Process Γ
   Case  : ∀{Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   -- Fork  : ∀{Δ Γ₁ Γ₂ A B}
   --         (p : Γ ≃ [ A ⊗ B ] + Δ)
   --         (q : Δ ≃ Γ₁ + Γ₂)
   --         -> Process (A :: Γ₁)
   --         -> Process (B :: Γ₂)
   --         -> Process Γ
   -- Join  : ∀{Δ A B}
   --         (p : Γ ≃ [ A ⅋ B ] + Δ)
   --         -> Process (B :: A :: Δ)
   --         -> Process Γ
   Cut   : ∀{Γ₁ Γ₂ A B}
           (d : Dual A B)
           (p : Γ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (Link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = Link d q
#process π (Close p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = Close q
#process π (Fail p) with #one+ π p
... | Δ' , q , π' = Fail q
#process π (Wait p P) with #one+ π p
... | Δ' , q , π' = Wait q (#process π' P)
#process π (Select x p P) = {!!}
#process π (Case p P Q) = {!!}

#process π (Cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = Cut d q (#process (#next π₁) P) (#process (#next π₂) Q)

data _⊒_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  s-comm : ∀{Γ Γ₁ Γ₂ A B P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
           -> Cut d p P Q ⊒ Cut (dual-symm d) (+-comm p) Q P

  s-assoc-r : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
              {P : Process (A :: Γ₁)}
              {Q : Process (B :: A' :: Δ₁)}
              {R : Process (B' :: Δ₂)}
              (d : Dual A A') (e : Dual B B')
              (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
              (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
              Cut d p P (Cut e (split-l q) Q R) ⊒ Cut e q' (Cut d (split-r p') P (#process #here Q)) R

  s-link : ∀{Γ A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ]) ->
           Link d p ⊒ Link (dual-symm d) (+-comm p)

  s-fail : ∀{Γ Γ₁ Γ₂ Δ A B P} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Top ] + Δ) ->
           let _ , _ , q' = +-assoc-l p q in
           Cut d p (Fail (split-r q)) P ⊒ Fail q'

  s-wait : ∀{Γ Γ₁ Γ₂ Δ A B}
           {P : Process (A :: Δ)}
           {Q : Process (B :: Γ₂)}
           (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Bot ] + Δ) ->
           let _ , p' , q' = +-assoc-l p q in
           Cut d p (Wait (split-r q) P) Q ⊒ Wait q' (Cut d p' P Q)

  -- (x)(case y(z){P|Q} | R) ⊒ case y(z){(x)(P|R), (x)(Q|R)} , x ≠ y,z
  s-case : ∀{Γ A B A₁ A₂ Γ₁ Γ₂ Δ}
         {P : Process (A₁ :: A :: Δ)}
         {Q : Process (A₂ :: A :: Δ)}
         {R : Process (B :: Γ₂)}
         (d : Dual A B)
         (p : Γ ≃ Γ₁ + Γ₂)
         (q : Γ₁ ≃ [ A₁ & A₂ ] + Δ) ->
         let _ , p' , q' = +-assoc-l p q in
         Cut d p (Case (split-r q) P Q) R ⊒
         Case q' (Cut d (split-l p') (#process #here P) R)
                 (Cut d (split-l p') (#process #here Q) R)

  s-refl : ∀{Γ} {P : Process Γ} -> P ⊒ P
  s-tran : ∀{Γ} {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong : ∀{Γ Γ₁ Γ₂ A A'}
           {P Q : Process (A :: Γ₁)}
           {R : Process (A' :: Γ₂)}
           (d : Dual A A')
           (p : Γ ≃ Γ₁ + Γ₂) ->
           P ⊒ Q -> Cut d p P R ⊒ Cut d p Q R

  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B A₁ A₂}
    {P : Process (A₁ :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂)
    (q : Γ₁ ≃ [ A₁ ⊕ A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Select true (split-r q) P) Q ⊒
    Select true q' (Cut d (split-l p') (#process #here P) Q)

  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B A₁ A₂}
    {P : Process (A₂ :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂)
    (q : Γ₁ ≃ [ A₁ ⊕ A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    Cut d p (Select false (split-r q) P) Q ⊒
    Select false q' (Cut d (split-l p') (#process #here P) Q)

s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            Cut d p (Cut e (split-r q) P Q) R ⊒ Cut (dual-symm (dual-symm e)) (+-comm (+-comm q')) P (Cut (dual-symm (dual-symm d)) (split-l (+-comm (+-comm p'))) (#process #here Q) R)
s-assoc-l d e p q p' q' =
  s-tran (s-cong d p (s-comm e (split-r q)))  (s-tran (s-comm d p)
  (s-tran (s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q) (+-comm p') (+-comm q'))
  (s-tran (s-cong (dual-symm e) (+-comm q') (s-comm (dual-symm d) (split-r (+-comm p'))))
  (s-comm (dual-symm e) (+-comm q')))))

data _~>_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  r-link :
    ∀{Γ Δ A B}
    {P : Process (B :: Δ)}
    (d : Dual A B)
    (p : Γ ≃ [ B ] + Δ) ->
    Cut d p (Link d (split-l (split-r split-e))) P ~> #process (#cons p) P

  r-close :
    ∀{Γ}
    {P : Process Γ} ->
    Cut dual-one-bot +-unit-l (Close (split-l split-e)) (Wait (split-l +-unit-l) P) ~> P

  r-left :
    ∀{Γ Γ₁ Γ₂ A₁ A₂ B₁ B₂}
    {P : Process (A₁ :: Γ₁)}
    {Q : Process (B₁ :: Γ₂)}
    {R : Process (B₂ :: Γ₂)}
    (d₁ : Dual A₁ B₁) (d₂ : Dual A₂ B₂) -- è il caso che A ≡ A₁ altrimenti non sarebbe possibile l'opzione r-right, ma non so quanto ci interessi
    (q₁ : Γ₁ ≃ [] + Γ₁) (q₂ : Γ₂ ≃ [] + Γ₂) -- dati [B₁ & B₂], entrambi devono essere duali di A, dove A=inl(A,A₁). Ergo B₁ = B₂ = B
    (p : Γ ≃ Γ₁ + Γ₂)
    ->
    Cut (dual-plus-with d₁ d₂) p (Select true (split-l q₁) P) (Case (split-l q₂) Q R) ~> Cut d₁ p P Q

  -- r-right :


  r-cut :
    ∀{Γ Γ₁ Γ₂ A B}
    {P Q : Process (A :: Γ₁)}
    {R : Process (B :: Γ₂)}
    (d : Dual A B)
    (q : Γ ≃ Γ₁ + Γ₂)
    (r : P ~> Q) ->
    Cut d q P R ~> Cut d q Q R


-- provided that P ⊒ R and R ~> Q then P ~> Q
  r-cong :
    ∀{Γ}
    {P R Q : Process Γ}
    (p : P ⊒ R) (q : R ~> Q) -> P ~> Q
