import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl) 
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
-- so far so good

{-# BUILTIN NATURAL ℕ #-}
-- I will build castles upon this stone number 0. Just you wait.
