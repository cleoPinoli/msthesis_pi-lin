open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Data.List.Base using (List; []; _∷_; [_]; _++_)

open import Type
open import Context
open import Process

ex0 : Process {zero} [ $∀ (var zero ⅋ ort zero) ]
ex0 = all (split-l split-e)
          λ { (s-⅋ (s-v d) (s-o e)) →
              join (split-l split-e)
              (link e (split-r (split-l split-e))) }

ex1 : Process {zero} [ $∀ ($∀ (var (suc zero) ⅋ (var zero ⅋ (ort zero ⊗ ort (suc zero))))) ]
ex1 = all (split-l split-e) λ {
          (s-∀ (s-⅋ (s-v x) (s-⅋ (s-v x₁) (s-⊗ (s-o x₂) (s-o x₃))))) →
          all (split-l split-e) λ {
            (s-⅋ s (s-⅋ (s-v x) (s-⊗ (s-o x₁) s₃))) → {!!}
          }
      }

