
module Families.Preorder where

open import Prelude
open import Structures.Preorder public


module Displayed where

    record DispPreord {i}(Γ : Preord i) j : Type (i ⊔ lsuc j) where
        field
            ∣_∣T_   : ∣ Γ ∣C → Type j
            _T_⊢_≤_ : ∀{γ γ'}(p : Γ C γ ≤ γ') → ∣_∣T_ γ → ∣_∣T_ γ' → Prop j
            refT    : ∀{γ} x → _T_⊢_≤_ (refC Γ γ) x x
            transT  : ∀{γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}
                    {x : ∣_∣T_ γ}{x' : ∣_∣T_ γ'}{x'' : ∣_∣T_ γ''}
                    → _T_⊢_≤_ p x x' → _T_⊢_≤_ q x' x'' → _T_⊢_≤_ (transC Γ p q) x x''
        infix 4 ∣_∣T_
        infix 5 _T_⊢_≤_
    open DispPreord public

module DispPreordReasoning {i}{Γ : Preord i}{j}(α : Displayed.DispPreord Γ j) where
    open Displayed

    infixr 30 _≤T⟨_⟩_
    infixl 40 _≤T∎

    _≤T∎ : ∀{γ} x → _T_⊢_≤_ α (refC Γ γ) x x
    _≤T∎ = refT α

    _≤T⟨_⟩_ : ∀{γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}(x : ∣ α ∣T γ){x' : ∣ α ∣T γ'} →
        α T p ⊢ x ≤ x' → {x'' : ∣ α ∣T γ''} → α T q ⊢ x' ≤ x'' → α T transC Γ p q ⊢ x ≤ x''
    x ≤T⟨ φ ⟩ ψ = transT α φ ψ


module Pseudo where

    open Preord
    open Displayed
    open Displayed.DispPreord

    record psPreordFibrancy⁺ {i}(Γ : Preord i) j (α : DispPreord Γ j) : Type (i ⊔ lsuc j) where
        field
            coeT⁺    : {γ γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → ∣ α ∣T γ → ∣ α ∣T γ'
            cohT⁺    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ')(x : ∣ α ∣T γ) → α T p ⊢ x ≤ (coeT⁺ p x)
            cartT⁺   : ∀{γ γ' γ''}(x : ∣ α ∣T γ){p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}(x'' : ∣ α ∣T γ'')
                    (φ : α T transC Γ p q ⊢ x ≤ x'') → α T q ⊢ coeT⁺ p x ≤ x''
    open psPreordFibrancy⁺

    psPreordFam⁺ : ∀ {i} (Γ : Preord i) j → Type (i ⊔ lsuc j)
    psPreordFam⁺ Γ j = Σ (DispPreord Γ j) (psPreordFibrancy⁺ Γ j)

    record psPreordFibrancy⁻ {i}(Γ : Preord i) j (α : DispPreord Γ j) : Type (i ⊔ lsuc j) where
        field
            coeT⁻    : {γ γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → ∣ α ∣T γ' → ∣ α ∣T γ
            cohT⁻    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ')(x' : ∣ α ∣T γ') → α T p ⊢ (coeT⁻ p x') ≤ x'
            cartT⁻   : ∀{γ γ' γ''}(x : ∣ α ∣T γ){p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}(x'' : ∣ α ∣T γ'')
                    (ψ : α T transC Γ p q ⊢ x ≤ x'') → α T p ⊢ x ≤ coeT⁻ q x''
    open psPreordFibrancy⁻

    psPreordFam⁻ : ∀ {i} (Γ : Preord i) j → Type (i ⊔ lsuc j)
    psPreordFam⁻ Γ j = Σ (DispPreord Γ j) (psPreordFibrancy⁻ Γ j)

module Split where

    open Displayed
    open Pseudo
    open Displayed.DispPreord
    open Pseudo.psPreordFibrancy⁺
    open Pseudo.psPreordFibrancy⁻

    record splitPreordFibrancy⁺ {i}(Γ : Preord i) j (α : psPreordFam⁺ Γ j) : Type (i ⊔ lsuc j) where
        field
            coeT⁺-ref : ∀ {γ : ∣ Γ ∣C}(x :  ∣ fst α ∣T γ ) → coeT⁺ (snd α) (refC Γ γ) x ≡ x
            coeT⁺-trans : ∀ {γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}(x : ∣ fst α ∣T γ) → 
                        (coeT⁺ (snd α) (transC Γ p q) x) ≡ coeT⁺ (snd α) q (coeT⁺ (snd α) p x)
    
    splitPreordFam⁺ : ∀ {i} (Γ : Preord i) j → Type (i ⊔ lsuc j)
    splitPreordFam⁺ Γ j = Σ (psPreordFam⁺ Γ j) (splitPreordFibrancy⁺ Γ j)

    record splitPreordFibrancy⁻ {i}(Γ : Preord i) j (α : psPreordFam⁻ Γ j) : Type (i ⊔ lsuc j) where
        field
            coeT⁻-ref : ∀ {γ : ∣ Γ ∣C}(x :  ∣ fst α ∣T γ ) → coeT⁻ (snd α) (refC Γ γ) x ≡ x
            coeT⁻-trans : ∀ {γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}(x'' : ∣ fst α ∣T γ'') → 
                        (coeT⁻ (snd α) (transC Γ p q) x'') ≡ coeT⁻ (snd α) p (coeT⁻ (snd α) q x'')
    
    splitPreordFam⁻ : ∀ {i} (Γ : Preord i) j → Type (i ⊔ lsuc j)
    splitPreordFam⁻ Γ j = Σ (psPreordFam⁻ Γ j) (splitPreordFibrancy⁻ Γ j)