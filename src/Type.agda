module Type where

data Type : Set where
  Zero One Bot Top : Type
  _&_ _⊕_ _⊗_ _⅋_ : Type -> Type -> Type

data Dual : Type -> Type -> Set where
  dual-zero-top : Dual Zero Top
  dual-top-zero : Dual Top Zero
  dual-one-bot  : Dual One Bot
  dual-bot-one  : Dual Bot One
  dual-with-plus : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t & s) (t' ⊕ s')
  dual-plus-with : ∀{t s t' s'} -> Dual t t' -> Dual s s' -> Dual (t ⊕ s) (t' & s')

dual-symm : ∀{A B} -> Dual A B -> Dual B A
dual-symm dual-zero-top = dual-top-zero
dual-symm dual-top-zero = dual-zero-top
dual-symm dual-one-bot = dual-bot-one
dual-symm dual-bot-one = dual-one-bot
dual-symm (dual-with-plus p q) = dual-plus-with (dual-symm p) (dual-symm q)
dual-symm (dual-plus-with p q) = dual-with-plus (dual-symm p) (dual-symm q)

