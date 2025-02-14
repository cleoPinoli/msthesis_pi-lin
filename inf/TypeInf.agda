{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}
--per usare il modulo nonostante il buco in una prova (imprudente e sconsiderato da parte mia)

module TypeInf where

open import Data.Nat

data Type : Set

record ∞Type : Set where
  coinductive
  field
    force : Type
open ∞Type

data Type where
  Zero One Top Bot : Type
  _⊕_ _&_ : ∞Type -> ∞Type -> Type

data Dual : Type -> Type -> Set

record ∞Dual (t s : Type) : Set where
  coinductive
  field
    force : Dual t s
open ∞Dual

data Dual where
  dual-one-bot : Dual One Bot
  dual-bot-one : Dual Bot One
  dual-plus-with : ∀{t s t' s'} -> ∞Dual (t .force) (t' .force) -> ∞Dual (s .force) (s' .force) -> Dual (t ⊕ s) (t' & s')
  dual-with-plus : ∀{t s t' s'} -> ∞Dual (t .force) (t' .force) -> ∞Dual (s .force) (s' .force) -> Dual (t & s) (t' ⊕ s')


dual-symm : ∀{t s} -> Dual t s -> ∞Dual s t
dual-symm dual-one-bot .force = dual-bot-one
dual-symm dual-bot-one .force = dual-one-bot
dual-symm (dual-plus-with p q) .force = dual-with-plus (dual-symm (p .force)) (dual-symm (q .force))
dual-symm (dual-with-plus p q) .force = dual-plus-with (dual-symm (p .force)) (dual-symm (q .force))
