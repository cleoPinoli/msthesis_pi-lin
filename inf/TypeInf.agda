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

record ∞Dual (t s : ∞Type) : Set where
  coinductive
  field
    force : Dual (t .force) (s .force)
open ∞Dual

data Dual where
  dual-one-bot : Dual One Bot
  dual-bot-one : Dual Bot One
  dual-plus-with : ∀{t s t' s'} -> ∞Dual t t' -> ∞Dual s s' -> Dual (t ⊕ s) (t' & s')
  dual-with-plus : ∀{t s t' s'} -> ∞Dual t t' -> ∞Dual s s' -> Dual (t & s) (t' ⊕ s')


dual-symm : ∀{t s} -> Dual (t .force) (s .force) -> ∞Dual s t
dual-symm {t}{s} p .force = {!!} 
