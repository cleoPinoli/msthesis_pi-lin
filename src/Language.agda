
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Nullary using (¬_)

data Type : Set where
  Zero One Bot Top : Type
  _&_ _⊕_ : Type -> Type -> Type

data Dual : Type -> Type -> Set where
  dual-zero-top : Dual Zero Top
  dual-top-zero : Dual Top Zero
  dual-one-bot  : Dual One Bot
  dual-bot-one  : Dual Bot One
  dual-with-plus : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t & s) (t' ⊕ s')
  dual-plus-with : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t ⊕ s) (t' & s')

BoolST : Type
BoolST = One ⊕ One

Channel : Set
Channel = ℕ

data Maybe (A : Set) : Set where
  none : Maybe A
  some : A -> Maybe A

data Context : Set where
  [] : Context
  _::_ : (A : Type) (Γ : Context) -> Context

[_] : Type -> Context
[_] = _:: []

_++_ : Context -> Context -> Context
[] ++ Δ = Δ
(mt :: Γ) ++ Δ = mt :: (Γ ++ Δ)

infixr 5 _::_ _++_
infix 4 _≃_+_

data Empty : Context -> Set where
  empty-[] : Empty []

data _≃_+_ : Context -> Context -> Context -> Set where
  split-e : [] ≃ [] + []
  split-l : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ A :: Γ₁ + Γ₂
  split-r : ∀{Γ Γ₁ Γ₂ A} -> Γ ≃ Γ₁ + Γ₂ -> A :: Γ ≃ Γ₁ + A :: Γ₂

split-comm : ∀{Γ Γ₁ Γ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ ≃ Γ₂ + Γ₁
split-comm split-e = split-e
split-comm (split-l p) = split-r (split-comm p)
split-comm (split-r p) = split-l (split-comm p)

data Process : Context -> Set where
   close : Process [ One ]
   fail  : ∀{Γ Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   wait  : ∀{Γ Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   left  : ∀{Γ Δ A B}
           (p : Γ ≃ [ A ⊕ B ] + Δ)
           -> Process (A :: Δ)
           -> Process Γ
   right : ∀{Γ Δ A B}
           (p : Γ ≃ [ A ⊕ B ] + Δ)
           -> Process (B :: Δ)
           -> Process Γ
   case_ : ∀{Γ Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   cut    : ∀{Γ Γ₁ Γ₂ A B}
            (d : Dual A B)
            (p : Γ ≃ Γ₁ + Γ₂)
            -> Process (A :: Γ₁)
            -> Process (B :: Γ₂)
            -> Process Γ

dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm dual-zero-top = dual-top-zero
dual-symm dual-top-zero = dual-zero-top
dual-symm dual-one-bot = dual-bot-one
dual-symm dual-bot-one = dual-one-bot
dual-symm (dual-with-plus p q) = dual-plus-with (dual-symm p) (dual-symm q)
dual-symm (dual-plus-with p q) = dual-with-plus (dual-symm p) (dual-symm q)

split-assoc : ∀{Γ Γ₁ Γ₂ Δ₁ Δ₂} -> Γ ≃ Γ₁ + Γ₂ -> Γ₂ ≃ Δ₁ + Δ₂ ->
              ∃[ Δ ] (Δ ≃ Γ₁ + Δ₁) × (Γ ≃ Δ + Δ₂)
split-assoc split-e split-e = [] , split-e , split-e
split-assoc (split-l p) q = {!!}
split-assoc (split-r p) q = {!!}

split-unit-l : ∀{Γ} -> Γ ≃ [] + Γ
split-unit-l {[]} = split-e
split-unit-l {A :: Γ} = split-r split-unit-l

split-sing-l : ∀{A B Γ} -> [ A ] ≃ [ B ] + Γ -> A ≡ B × Γ ≡ []
split-sing-l (split-l split-e) = refl , refl

split-sing : ∀{A B Γ Δ Δ'} -> Γ ≃ [ A ] + Δ -> Γ ≃ [ B ] + Δ' -> (A ≡ B × Δ ≡ Δ') ∨ 

top : ∀{Γ Δ A} -> Γ ≃ [ A ] + Δ -> Process Γ -> Process (A :: Δ)
top p close with split-sing-l p
... | refl , refl = close
top p (fail q) = {!!}
top p (wait p₁ P) = {!!}
top p (left p₁ P) = {!!}
top p (right p₁ P) = {!!}
top p ((case p₁) P P₁) = {!!}
top p (cut d p₁ P P₁) = {!!}

data _⊒_ {Γ} : Process Γ -> Process Γ -> Set where
  s-comm : ∀{Γ₁ Γ₂ A B P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
           -> cut d p P Q ⊒ cut (dual-symm d) (split-comm p) Q P

  s-assoc : ∀{Γ₁ Γ₂ Δ₁ Δ₂ A A' B B'}
            {P : Process (A :: Γ₁)}
            {Q : Process (B :: A' :: Δ₁)}
            {R : Process (B' :: Δ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂) ->
            let Δ , p' , q' = split-assoc p q in
            cut d p P (cut e (split-l q) Q R) ⊒ cut e q' (cut d (split-r p') P (top (split-r (split-l split-unit-l)) Q)) R

--   s-fail : ∀{Γ₁ Γ₂ Γ₃ A B P} (d : Dual A B) (p : Γ ≃ Γ₁ ++ some Top :: Γ₂ + Γ₃)
--            -> let Δ₁ , Δ₂ , eq = split-not-empty p in
--               cut d p (fail {some A :: Γ₁} {Γ₂}) P ⊒ subst Process eq (fail {Δ₁} {Δ₂})
