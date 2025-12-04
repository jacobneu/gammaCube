
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

    tzt : ∀ {i} {Γ : Preord i} {j} (α : psPreordFam⁺ Γ j) {γ γ' γ''}(x : ∣ fst α ∣T γ)(p : Γ C γ ≤ γ')(q : Γ C γ' ≤ γ'') →
        fst α T (refC Γ γ'') ⊢ coeT⁺ (snd α) q (coeT⁺ (snd α) p x) ≤ coeT⁺ (snd α) (transC Γ p q) x
    tzt {i}{Γ}{j} α x p q = 
        cartT⁺ (snd α) (coeT⁺ (snd α) p x) (coeT⁺ (snd α) (transC Γ p q) x) 
            (cartT⁺ (snd α) x _ (cohT⁺ (snd α) (transC Γ p q) _))
    
    tztop : ∀ {i} {Γ : Preord i} {j} (α : psPreordFam⁺ Γ j) {γ γ' γ''}(x : ∣ fst α ∣T γ)(p : Γ C γ ≤ γ')(q : Γ C γ' ≤ γ'') →
        fst α T (refC Γ γ'') ⊢ coeT⁺ (snd α) (transC Γ p q) x ≤ coeT⁺ (snd α) q (coeT⁺ (snd α) p x)
    tztop {i}{Γ}{j} α x p q = cartT⁺ (snd α) x _ (transT (fst α) (cohT⁺ (snd α) p _) (cohT⁺ (snd α) q _))

    psFunctorial : ∀ {i} {Γ : Preord i} {j} (α : psPreordFam⁺ Γ j) {γ γ'}(x y : ∣ fst α ∣T γ)(p : Γ C γ ≤ γ') →
        fst α T (refC Γ γ) ⊢ x ≤ y → fst α T (refC Γ γ') ⊢ coeT⁺ (snd α) p x ≤ coeT⁺ (snd α) p y
    psFunctorial {i}{Γ}{j} α {γ}{γ'} x y p φ = cartT⁺ (snd α) x (coeT⁺ (snd α) p y) (transT (fst α) φ (cohT⁺ (snd α) p y))

    _⁻ᵀ : ∀ {i} {Γ : Preord i} {j} → psPreordFam⁺ Γ j → psPreordFam⁺ Γ j
    _⁻ᵀ {i}{Γ}{j} α = 
        let open DispPreordReasoning (fst α) in record 
        { ∣_∣T_ = ∣ fst α ∣T_
        ; ≤D = λ γ γ' p x x' → ≤D (fst α) γ' γ' (refC Γ γ') x' (coeT⁺ (snd α) p x)
        ; refT = λ {γ} x → cohT⁺ (snd α) (refC Γ γ) x
        ; transT = λ {γ}{γ'}{γ''}{p}{q}{x}{x'}{x''} φ ψ →
            x'' 
                ≤T⟨ ψ ⟩ 
            coeT⁺ (snd α) q x' 
                ≤T⟨ psFunctorial α _ _ q φ ⟩ 
            coeT⁺ (snd α) q (coeT⁺ (snd α) p x) 
                ≤T⟨ tzt α x p q ⟩
            (coeT⁺ (snd α) (transC Γ p q) x  ≤T∎) 
        }
        , record 
        { coeT⁺ = coeT⁺ (snd α)
        ; cohT⁺ = λ p x → refT (fst α) (coeT⁺ (snd α) p x)
        ; cartT⁺ = λ x {p}{q} x'' φ → transT (fst α) φ (tztop α x p q)
        }

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