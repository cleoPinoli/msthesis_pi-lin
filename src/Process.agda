module Process where

open import Data.Sum
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl) 
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)

open import List
open import Type
open import Context

data Process (Γ : Context) : Set where
   close : Γ ≃ [ One ] + [] -> Process Γ -- @diff
   link  : ∀{A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ])
           -> Process Γ
   fail  : ∀{Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   wait  : ∀{Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   select : ∀{Δ A B}
            (x : Bool)
            (p : Γ ≃ [ A ⊕ B ] + Δ)
            -> Process ((if x then A else B) :: Δ)
            -> Process Γ
   case  : ∀{Δ A B}
           (p : Γ ≃ [ A & B ] + Δ)
           -> Process (A :: Δ)
           -> Process (B :: Δ)
           -> Process Γ
   -- fork  : ∀{Δ Γ₁ Γ₂ A B}
   --         (p : Γ ≃ [ A ⊗ B ] + Δ)
   --         (q : Δ ≃ Γ₁ + Γ₂)
   --         -> Process (A :: Γ₁)
   --         -> Process (B :: Γ₂)
   --         -> Process Γ
   -- join  : ∀{Δ A B}
   --         (p : Γ ≃ [ A ⅋ B ] + Δ)
   --         -> Process (B :: A :: Δ)
   --         -> Process Γ
   cut   : ∀{Γ₁ Γ₂ A B}
           (d : Dual A B)
           (p : Γ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = link d q
#process π (close p) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ with #one π₁ | #nil π₂
... | refl | refl = close q
#process π (fail p) with #one+ π p
... | Δ' , q , π' = fail q
#process π (wait p P) with #one+ π p
... | Δ' , q , π' = wait q (#process π' P)
#process π (select x p P) with #one+ π p
... | Δ' , q , π' = select x q (#process (#next π') P)
#process π (case p P Q) with #one+ π p
... | Δ' , q , π' = case q (#process (#next π') P) (#process (#next π') Q)
#process π (cut d p P Q) with #split π p
... | Δ₁ , Δ₂ , q , π₁ , π₂ = cut d q (#process (#next π₁) P) (#process (#next π₂) Q)

data _⊒_ : ∀{Γ} -> Process Γ -> Process Γ -> Set where
  s-comm : ∀{Γ Γ₁ Γ₂ A B P Q} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
           -> cut d p P Q ⊒ cut (dual-symm d) (+-comm p) Q P

  s-assoc-r : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
              {P : Process (A :: Γ₁)}
              {Q : Process (B :: A' :: Δ₁)}
              {R : Process (B' :: Δ₂)}
              (d : Dual A A') (e : Dual B B')
              (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₂ ≃ Δ₁ + Δ₂)
              (p' : Δ ≃ Γ₁ + Δ₁) (q' : Γ ≃ Δ + Δ₂) ->
              cut d p P (cut e (split-l q) Q R) ⊒ cut e q' (cut d (split-r p') P (#process #here Q)) R

  s-link : ∀{Γ A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ]) ->
           link d p ⊒ link (dual-symm d) (+-comm p)

  s-wait : ∀{Γ Γ₁ Γ₂ Δ A B}
           {P : Process (A :: Δ)}
           {Q : Process (B :: Γ₂)}
           (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ [ Bot ] + Δ) ->
           let _ , p' , q' = +-assoc-l p q in
           cut d p (wait (split-r q) P) Q ⊒ wait q' (cut d p' P Q)

  -- (x)(case y(z){P|Q} | R) ⊒ case y(z){(x)(P|R), (x)(Q|R)} , x ≠ y,z
  s-case : ∀{Γ A B A₁ A₂ Γ₁ Γ₂ Δ}
         {P : Process (A₁ :: A :: Δ)}
         {Q : Process (A₂ :: A :: Δ)}
         {R : Process (B :: Γ₂)}
         (d : Dual A B)
         (p : Γ ≃ Γ₁ + Γ₂)
         (q : Γ₁ ≃ [ A₁ & A₂ ] + Δ) ->
         let _ , p' , q' = +-assoc-l p q in
         cut d p (case (split-r q) P Q) R ⊒
         case q' (cut d (split-l p') (#process #here P) R)
                 (cut d (split-l p') (#process #here Q) R)

  s-refl : ∀{Γ} {P : Process Γ} -> P ⊒ P
  s-tran : ∀{Γ} {P Q R : Process Γ} -> P ⊒ Q -> Q ⊒ R -> P ⊒ R
  s-cong : ∀{Γ Γ₁ Γ₂ A A'}
           {P Q : Process (A :: Γ₁)}
           {R : Process (A' :: Γ₂)}
           (d : Dual A A')
           (p : Γ ≃ Γ₁ + Γ₂) ->
           P ⊒ Q -> cut d p P R ⊒ cut d p Q R

  s-select-l :
    ∀{Γ Γ₁ Γ₂ Δ A B A₁ A₂}
    {P : Process (A₁ :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂)
    (q : Γ₁ ≃ [ A₁ ⊕ A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (select true (split-r q) P) Q ⊒
    select true q' (cut d (split-l p') (#process #here P) Q)

  s-select-r :
    ∀{Γ Γ₁ Γ₂ Δ A B A₁ A₂}
    {P : Process (A₂ :: A :: Δ)}
    {Q : Process (B :: Γ₂)}
    (d : Dual A B)
    (p : Γ ≃ Γ₁ + Γ₂)
    (q : Γ₁ ≃ [ A₁ ⊕ A₂ ] + Δ) ->
    let _ , p' , q' = +-assoc-l p q in
    cut d p (select false (split-r q) P) Q ⊒
    select false q' (cut d (split-l p') (#process #here P) Q)

s-assoc-l : ∀{Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ A A' B B'}
            {P : Process (B :: Δ₁)}
            {Q : Process (B' :: A :: Δ₂)}
            {R : Process (A' :: Γ₂)}
            (d : Dual A A') (e : Dual B B')
            (p : Γ ≃ Γ₁ + Γ₂) (q : Γ₁ ≃ Δ₁ + Δ₂)
            (p' : Δ ≃ Δ₂ + Γ₂) (q' : Γ ≃ Δ₁ + Δ) ->
            cut d p (cut e (split-r q) P Q) R ⊒ cut (dual-symm (dual-symm e)) (+-comm (+-comm q')) P (cut (dual-symm (dual-symm d)) (split-l (+-comm (+-comm p'))) (#process #here Q) R)
s-assoc-l d e p q p' q' =
  s-tran (s-cong d p (s-comm e (split-r q)))  (s-tran (s-comm d p)
  (s-tran (s-assoc-r (dual-symm d) (dual-symm e) (+-comm p) (+-comm q) (+-comm p') (+-comm q'))
  (s-tran (s-cong (dual-symm e) (+-comm q') (s-comm (dual-symm d) (split-r (+-comm p'))))
  (s-comm (dual-symm e) (+-comm q')))))



-- Input and Output processes that perform an action on the most recent channel.
data Input : ∀{Γ} -> Process Γ -> Set where
  fail :
    ∀{Γ Δ}
    (p : Γ ≃ [] + Δ) -> Input (fail (split-l p))
  wait :
    ∀{Γ Δ} (p : Γ ≃ [] + Δ) {P : Process Δ} -> Input (wait (split-l p) P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (A :: Δ)} {Q : Process (B :: Δ)} ->
    Input (case (split-l p) P Q)
--  join :
--    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (B :: A :: Δ)} ->
--    Input (join (split-l p) P)

data Output : ∀{Γ} -> Process Γ -> Set where
  close : ∀{Γ} (p : Γ ≃ [ One ] + []) -> Output (close p)
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [] + Δ) {P : Process ((if x then A else B) :: Δ)} ->
    Output (select x (split-l p) P)
--  fork :
--    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
--    {P : Process (A :: Δ₁)} {Q : Process (B :: Δ₂)} ->
--    Output (fork (split-l p) q P Q)


-- an Action process is either an Input or an Output process.
Action : ∀{Γ} -> Process Γ -> Set
Action P = Input P ⊎ Output P

-- two processes whose youngest channels have types related by duality
-- cannot be both Input or both Output processes.

input-input :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Input P × Input Q)
input-input dual-top-zero (fail p , ())
input-input dual-bot-one (wait p , ())
input-input (dual-with-plus d d₁) (case p , ())
-- input-input (d-⅋-⊗ d d₁) (join p , ())

-- @todo fix close!!
-- output-output :
--  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
--  Dual A B -> ¬ (Output P × Output Q)
-- output-output dual-one-bot (close p , ())
-- output-output (dual-plus-with d d₁) (select x p , ())
-- output-output (d-⊗-⅋ d d₁) (fork p q , ())
