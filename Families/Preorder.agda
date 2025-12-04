
module Families.Preorder where

open import Prelude
open import Structures.Preorder public


module Displayed where

    record DispPreord {i}(Γ : Preord i) j : Type (i ⊔ lsuc j) where
        field
            ∣_∣T_   : ∣ Γ ∣C → Type j
            ≤D : ∀ (γ γ' : ∣ Γ ∣C)(p : Γ C γ ≤ γ') → ∣_∣T_ γ → ∣_∣T_ γ' → Prop j
            refT    : ∀{γ} x → ≤D γ γ (refC Γ γ) x x
            transT  : ∀{γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}
                    {x : ∣_∣T_ γ}{x' : ∣_∣T_ γ'}{x'' : ∣_∣T_ γ''}
                    → ≤D γ γ' p x x' → ≤D γ' γ'' q x' x'' → ≤D γ γ'' (transC Γ p q) x x''
        infix 4 ∣_∣T_
    open DispPreord public

    infix 5 _T_⊢_≤_
    _T_⊢_≤_ : ∀ {i}{Γ : Preord i}{j}(α : DispPreord Γ j){γ γ'}(p : Γ C γ ≤ γ') → ∣ α ∣T γ → ∣ α ∣T γ' → Prop j
    _T_⊢_≤_ α {γ} {γ'} = ≤D α γ γ'

    DispPreord-≡-intro : ∀ {i}{Γ : Preord i}{j} (α β : DispPreord Γ j) →
        (e1 : (λ γ → ∣ α ∣T γ) ≡ (λ γ → ∣ β ∣T γ)) →
        (≤D α) ≡ (λ γ γ' p x x' → ≤D β γ γ' p (trₜ (congr e1 γ) x) (trₜ (congr e1 γ') x')) → 
        α ≡ β
    DispPreord-≡-intro α record { ∣_∣T_ = .(∣_∣T_ α) ; ≤D = .(≤D α) ; refT = _ ; transT = _ } refl refl = refl

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