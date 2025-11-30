
module Families.Setoid where

open import Prelude
open import Structures.Setoid public


module Displayed where

    record DispSetoid {i}(Γ : Setoid i) j : Type (i ⊔ lsuc j) where
        field
            ∣_∣T_   : ∣ Γ ∣C → Type j
            _T_⊢_~_ : ∀{γ γ'}(p : Γ C γ ~ γ') → ∣_∣T_ γ → ∣_∣T_ γ' → Prop j
            refT    : ∀{γ} α → _T_⊢_~_ (refC Γ γ) α α
            symT    : ∀{γ γ'}{p : Γ C γ ~ γ'}{α : ∣_∣T_ γ}{α' : ∣_∣T_ γ'}
                    → _T_⊢_~_ p α α' → _T_⊢_~_ (symC Γ p) α' α
            transT  : ∀{γ γ' γ''}{p : Γ C γ ~ γ'}{q : Γ C γ' ~ γ''}
                    {α : ∣_∣T_ γ}{α' : ∣_∣T_ γ'}{α'' : ∣_∣T_ γ''}
                    → _T_⊢_~_ p α α' → _T_⊢_~_ q α' α'' → _T_⊢_~_ (transC Γ p q) α α''
        infix 4 ∣_∣T_
        infix 5 _T_⊢_~_
    open DispSetoid public

    -- DispSetoid-≡-intro : ∀ {i}{Γ : Setoid i}{j}(α α' : DispSetoid Γ j) → 
    --     (base : ∣ α ∣T_ ≡ ∣ α' ∣T_) →
    --     (_≡_ {X = {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → ∣ α ∣T γ → ∣ α ∣T γ' → Prop j} (λ {γ γ'}(p : Γ C γ ~ γ')(x : ∣ α ∣T γ)(x' : ∣ α ∣T γ') → _T_⊢_~_ α {γ} {γ'} p x x') λ {γ γ'}(p : Γ C γ ~ γ')(x : ∣ α ∣T γ)(x' : ∣ α ∣T γ') → _T_⊢_~_ α' {γ} {γ'} p (tr (λ φ → φ γ) base x) (tr (λ φ → φ γ') base x')) →  
    --     α ≡ α'
    -- DispSetoid-≡-intro α record { ∣_∣T_ = .(∣_∣T_ α) ; _T_⊢_~_ = _T_⊢_~₁_ ; refT = refT₁ ; symT = symT₁ ; transT = transT₁ } refl c = {! c !}

module Disp~Reasoning {i}{Γ : Setoid i}{j}(α : Displayed.DispSetoid Γ j) where
    open Displayed

    infixr 30 _~D⟨_⟩_
    infixl 40 _~D∎

    _~D∎ : ∀{γ} x → _T_⊢_~_ α (refC Γ γ) x x
    _~D∎ = refT α

    _~D⟨_⟩_ : ∀{γ γ' γ''}{p : Γ C γ ~ γ'}{q : Γ C γ' ~ γ''}(x : ∣ α ∣T γ){x' : ∣ α ∣T γ'} →
        α T p ⊢ x ~ x' → {x'' : ∣ α ∣T γ''} → α T q ⊢ x' ~ x'' → α T transC Γ p q ⊢ x ~ x''
    x ~D⟨ φ ⟩ ψ = transT α φ ψ

    reverseT : ∀{γ γ'}{p : Γ C γ ~ γ'}{x : ∣ α ∣T γ}{x' : ∣ α ∣T γ'}
                    → α T p ⊢ x ~ x' → α T symC Γ p ⊢ x' ~ x
    reverseT = symT α

module Pseudo where

    open Setoid
    open Displayed
    open Displayed.DispSetoid

    record psSetoidFibrancy {i}(Γ : Setoid i) j (α : DispSetoid Γ j) : Type (i ⊔ lsuc j) where
        field
            coeT    : {γ γ' : ∣ Γ ∣C} → (p : Γ C γ ~ γ') → ∣ α ∣T γ → ∣ α ∣T γ'
            cohT    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ')(x : ∣ α ∣T γ) → α T p ⊢ x ~ (coeT p x)
    open psSetoidFibrancy

    psSetoidFam : ∀ {i} (Γ : Setoid i) j → Type (i ⊔ lsuc j)
    psSetoidFam Γ j = Σ (DispSetoid Γ j) (psSetoidFibrancy Γ j)

    psSetoidFam-is-DispSetoid : ∀ {i} (Γ : Setoid i) j → psSetoidFam Γ j → DispSetoid Γ j
    psSetoidFam-is-DispSetoid Γ j = fst

    -- psSetoidFam-≡-intro : 

    record PseudoFunctor {i}(Γ : Setoid i) j : Type (i ⊔ lsuc j) where
        field
            obj : ∣ Γ ∣C → Setoid j
            mor : ∀ {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' →  SetoidMor (obj γ) (obj γ')
            zz : ∀ {γ : ∣ Γ ∣C}(x : ∣ obj γ ∣C) → (obj γ) C (∣ mor (refC Γ γ) ∣s x) ~ x
            tzt : ∀ {γ γ' γ'' : ∣ Γ ∣C}(p : Γ C γ ~ γ')(q : Γ C γ' ~ γ'')(x : ∣ obj γ ∣C) → 
                (obj γ'') C ∣ mor (transC Γ p q) ∣s x ~ ∣ mor q ∣s (∣ mor p ∣s x)
    open PseudoFunctor

    psFam-functorial : ∀ {i}{Γ : Setoid i}{j}(α : psSetoidFam Γ j){γ γ' : ∣ Γ ∣C}
        (p : Γ C γ ~ γ')
        {x y : ∣ fst α ∣T γ} → 
        (fst α) T refC Γ γ ⊢ x ~ y →
        (fst α) T refC Γ γ' ⊢ coeT (snd α) p x ~ coeT (snd α) p y
    psFam-functorial α p {x}{y} φ = transT (fst α) (symT (fst α) (cohT (snd α) p x)) (transT (fst α) φ (cohT (snd α) p y))  

    psFam-to-psFunct : ∀ {i} (Γ : Setoid i) j → psSetoidFam Γ j → PseudoFunctor Γ j
    psFam-to-psFunct Γ j α = 
        let open Disp~Reasoning (fst α) in
        record  
        { obj = λ γ → record 
            { ∣_∣C = ∣ fst α ∣T γ 
            ; _C_~_ =  _T_⊢_~_ (fst α) (refC Γ γ)
            ; refC = refT (fst α) 
            ; symC = symT (fst α) 
            ; transC = transT (fst α) } 
        ; mor = λ {γ} {γ'} p → record 
            { ∣_∣s = coeT (snd α) p 
            ; ~s = λ {x} {y} w → 
                coeT (snd α) p x 
                    ~D⟨ symT (fst α) (cohT (snd α) p x) ⟩
                x 
                    ~D⟨ w ⟩ 
                y 
                    ~D⟨ cohT (snd α) p y ⟩ 
                coeT (snd α) p y       
                    ~D∎
            } 
        ; zz = λ {γ} x → symT (fst α) (cohT (snd α) (refC Γ γ) x) 
        ; tzt = λ p q x → 
            coeT (snd α) (transC Γ p q) x 
                ~D⟨ symT (fst α) (cohT (snd α) (transC Γ p q) x) ⟩
            x 
                ~D⟨ cohT (snd α) p x ⟩
            coeT (snd α) p x 
                ~D⟨ cohT (snd α) q (coeT (snd α) p x) ⟩
            coeT (snd α) q (coeT (snd α) p x)
                ~D∎
        }

    psFunct-to-psFam : ∀ {i} (Γ : Setoid i) j → PseudoFunctor Γ j → psSetoidFam Γ j
    psFunct-to-psFam Γ j A =
       record
       { ∣_∣T_ = λ γ → ∣ obj A γ ∣C 
       ; _T_⊢_~_ = λ {γ} {γ'} p x x' → (obj A γ') C ∣ mor A p ∣s x ~ x' 
       ; refT = λ x → zz A x 
       ; symT = λ {γ} {γ'} {p} {x} {y} w' → 
            let open ~Reasoning (obj A γ) in
                ∣ mor A (symC Γ p) ∣s y
                    ~⟨ ~s (mor A (symC Γ p)) w' ⁻¹ ⟩
                ∣ mor A (symC Γ p) ∣s (∣ mor A p ∣s x)
                    ~⟨ tzt A p (symC Γ p) x ⁻¹ ⟩
                ∣ mor A (refC Γ γ) ∣s x
                    ~⟨ zz A x ⟩
                x
                    ~∎
       ; transT = λ {γ} {γ'} {γ''} {p} {q} {x} {x'} {x''} φ ψ →
            let open ~Reasoning (obj A γ'') in
                ∣ mor A (transC Γ p q) ∣s x 
                    ~⟨ tzt A p q x ⟩ 
                ∣ mor A q ∣s (∣ mor A p ∣s x) 
                    ~⟨ ~s (mor A q) φ ⟩
                ∣ mor A q ∣s x'
                    ~⟨ ψ ⟩
                x'' 
                    ~∎
       },
       record 
       { coeT = λ p → ∣ mor A p ∣s 
       ; cohT = λ {γ} {γ'} p x → refC (obj A γ') (∣ mor A p ∣s x) 
       }

module Split where

    open Displayed
    open Pseudo
    open Displayed.DispSetoid
    open Pseudo.psSetoidFibrancy

    record splitSetoidFibrancy {i}(Γ : Setoid i) j (α : psSetoidFam Γ j) : Type (i ⊔ lsuc j) where
        field
            coeT-ref : ∀ {γ : ∣ Γ ∣C}( x :  ∣ fst α ∣T γ ) → coeT (snd α) (refC Γ γ) x ≡ x
            coeT-trans : ∀ {γ γ' γ''}{p : Γ C γ ~ γ'}{q : Γ C γ' ~ γ''}(x : ∣ fst α ∣T γ) → 
                        (coeT (snd α) (transC Γ p q) x) ≡ coeT (snd α) q (coeT (snd α) p x)
    
    splitSetoidFam : ∀ {i} (Γ : Setoid i) j → Type (i ⊔ lsuc j)
    splitSetoidFam Γ j = Σ (psSetoidFam Γ j) (splitSetoidFibrancy Γ j)

    splitSetoidFam-is-DispSetoid : ∀ {i} (Γ : Setoid i) j → splitSetoidFam Γ j → DispSetoid Γ j
    splitSetoidFam-is-DispSetoid Γ j α = fst (fst α)

