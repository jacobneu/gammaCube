
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

    record SetoidSec {i}(Γ : Setoid i){j}(A : DispSetoid Γ j) : Type (i ⊔ j) where
        field
            ∣_∣t : (γ : ∣ Γ ∣C) → ∣ A ∣T γ
            ~t   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ') → A T p ⊢ (∣_∣t γ) ~ (∣_∣t γ')
        infix 4 ∣_∣t
    open SetoidSec public


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



    psFam-to-psFunct : ∀ {i} (Γ : Setoid i) j → psSetoidFam Γ j → PseudoFunctor Γ j
    psFam-to-psFunct Γ j α = record  
        { obj = λ γ → record 
            { ∣_∣C = ∣ fst α ∣T γ 
            ; _C_~_ =  _T_⊢_~_ (fst α) (refC Γ γ)
            ; refC = refT (fst α) 
            ; symC = symT (fst α) 
            ; transC = transT (fst α) } 
        ; mor = λ {γ} {γ'} p → record 
            { ∣_∣s = coeT (snd α) p 
            ; ~s = λ {x} {y} w → transT (fst α) (transT (fst α) (symT (fst α) (cohT (snd α) p x)) w) (cohT (snd α) p y) 
            } 
        ; zz = λ {γ} x → symT (fst α) (cohT (snd α) (refC Γ γ) x) 
        ; tzt = λ p q x → transT (fst α) (symT (fst α) (cohT (snd α) (transC Γ p q) x)) (transT (fst α) (cohT (snd α) p x) (cohT (snd α) q (coeT (snd α) p x)))
        }

    psFunct-to-psFam : ∀ {i} (Γ : Setoid i) j → PseudoFunctor Γ j → psSetoidFam Γ j
    psFunct-to-psFam Γ j A = (record
       { ∣_∣T_ = λ γ → ∣ obj A γ ∣C 
       ; _T_⊢_~_ = λ {γ} {γ'} p x x' → (obj A γ') C ∣ mor A p ∣s x ~ x' 
       ; refT = λ x → zz A x 
       ; symT = λ {γ} {γ'} {p} {x} {y} w' → symC (obj A γ) (transC (obj A γ) (transC (obj A γ) ( symC (obj A γ) (zz A x)) (tzt A p (symC Γ p) x)) (~s (mor A (symC Γ p)) w'))
       ; transT = λ {γ} {γ'} {γ''} {p} {q} {x} x' x'' → transC (obj A γ'') (transC (obj A γ'') (tzt A p q x) (~s (mor A q) x')) x'' }), (record 
       { coeT = λ p → ∣ mor A p ∣s 
       ; cohT = λ {γ} {γ'} p x → refC (obj A γ') (∣ mor A p ∣s x) 
       })

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

