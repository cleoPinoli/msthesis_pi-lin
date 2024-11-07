module Process where

open import Data.Sum
open import Data.Bool using (Bool; if_then_else_)
open Bool using (true; false)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl) 
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)


open import Type
open import Context

data Process :  Context -> Set where
   link  : ∀{Γ A B}
           (d : Dual A B)
           (p : Γ ≃ [ A ] + [ B ])
           -> Process Γ
   fail  : ∀{Γ Δ}
           (p : Γ ≃ [ Top ] + Δ)
           -> Process Γ
   close : Process (One :: [])
   wait  : ∀{Γ Δ}
           (p : Γ ≃ [ Bot ] + Δ)
           -> Process Δ
           -> Process Γ
   select : ∀{Γ Δ A B}
            (x : Bool)
            (p : Γ ≃ [ A ⊕ B ] + Δ)
            -> Process ((if x then A else B) :: Δ)
            -> Process Γ
   case  : ∀{Γ Δ A B}
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
   cut   : ∀{Γ Γ₁ Γ₂ A B}
           (d : Dual A B)
           (p : Γ ≃ Γ₁ + Γ₂)
           -> Process (A :: Γ₁)
           -> Process (B :: Γ₂)
           -> Process Γ

#process : ∀{Γ Δ} -> Γ # Δ -> Process Γ -> Process Δ
#process π (link d p) with #one+ π p
... | Δ' , q , π' with #one π'
... | refl = link d q
#process π close  with #one π
... | refl = close
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
  close : Output close
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

output-output :
  ∀{Γ Δ A B} {P : Process (A :: Γ)} {Q : Process (B :: Δ)} ->
  Dual A B -> ¬ (Output P × Output Q)
output-output dual-one-bot (close , ())
output-output (dual-plus-with d d₁) (select x p , ())
-- output-output (d-⊗-⅋ d d₁) (fork p q , ())
