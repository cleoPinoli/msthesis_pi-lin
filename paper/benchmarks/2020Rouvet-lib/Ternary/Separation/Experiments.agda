

  infixl 9 _◇_
  data _◇_ {p} (P : SPred p) (Φᵢ : Carrier) : SPred (p ⊔ a) where
    ⟪_,_⟫ : ∀ {Φₚ Φ} → P Φₚ → Φᵢ ⊎ Φₚ ≣ Φ → (P ◇ Φᵢ) Φ


  module _ {p q} (P : SPred p) (Q : SPred q) where
    infixr 8 _◇─_
    _◇─_ : SPred (p ⊔ q ⊔ a)
    _◇─_ Φᵢ = ∀[ P ◇ Φᵢ ⇒ Q ]

  module _ {p q} {P : SPred p} {Q : SPred q} where
    pair : ε[ P ◇─ (Q ◇─ P ✴ Q) ]
    pair ⟪ px , σ₁ ⟫ ⟪ qx , σ₂ ⟫ rewrite ⊎-id⁻ˡ σ₁ = px ×⟨ σ₂ ⟩ qx

  module _ {p} {P : SPred p} where
    ◇-ε : ∀[ P ◇ ε ⇒ P ]
    ◇-ε ⟪ px , σ ⟫ rewrite ⊎-id⁻ˡ σ = px
