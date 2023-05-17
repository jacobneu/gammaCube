
{-
Modified from the Agda formalization of the Setoid universe,
by Thorsten Altenkrich, Simon Boulier, Ambrus Kaposi, Christian Sattler, and Filippo Sestini.
https://bitbucket.org/taltenkirch/Setoid-univ
-}

module Structures.Preorder where

open import Prelude 


record Preord i : Type (lsuc i) where
  field
    ∣_∣C : Type i
    _C_≤_ : ∣_∣C → ∣_∣C → Prop i
    refC : ∀ γ → _C_≤_ γ γ
    transC : ∀{γ γ' γ''} → _C_≤_ γ γ' → _C_≤_ γ' γ'' → _C_≤_ γ γ''
  infix 4 ∣_∣C
  infix 5 _C_≤_
open Preord public

record PreordMor {i j}(Γ : Preord i)(Δ : Preord j) : Type (i ⊔ j) where
  field
    ∣_∣s : ∣ Γ ∣C → ∣ Δ ∣C
    ≤s   : {γ γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → Δ C (∣_∣s γ) ≤ (∣_∣s γ')
  infix 4 ∣_∣s
open PreordMor public

record PreordFam⁺ {i}(Γ : Preord i) j : Type (i ⊔ lsuc j) where
  constructor mkTy⁺
  field
    ∣_∣T⁺_   : ∣ Γ ∣C → Type j
    _T⁺_⊢_≤_ : ∀{γ γ'}(p : Γ C γ ≤ γ') → ∣_∣T⁺_ γ → ∣_∣T⁺_ γ' → Prop j
    refT⁺    : ∀{γ} α → _T⁺_⊢_≤_ (refC Γ γ) α α
    transT⁺  : ∀{γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}
              {α : ∣_∣T⁺_ γ}{α' : ∣_∣T⁺_ γ'}{α'' : ∣_∣T⁺_ γ''}
            → _T⁺_⊢_≤_ p α α' → _T⁺_⊢_≤_ q α' α'' → _T⁺_⊢_≤_ (transC Γ p q) α α''
    coeT⁺    : {γ γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → ∣_∣T⁺_ γ → ∣_∣T⁺_ γ'
    cohT⁺    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ')(α : ∣_∣T⁺_ γ) → _T⁺_⊢_≤_ p α (coeT⁺ p α)
  infix 4 ∣_∣T⁺_
  infix 5 _T⁺_⊢_≤_
open PreordFam⁺ public

record PreordFam⁻ {i}(Γ : Preord i) j : Type (i ⊔ lsuc j) where
  constructor mkTy⁻
  field
    ∣_∣T⁻_   : ∣ Γ ∣C → Type j
    _T⁻_⊢_≤_ : ∀{γ γ'}(p : Γ C γ ≤ γ') → ∣_∣T⁻_ γ → ∣_∣T⁻_ γ' → Prop j
    refT⁻    : ∀{γ} α → _T⁻_⊢_≤_ (refC Γ γ) α α
    transT⁻  : ∀{γ γ' γ''}{p : Γ C γ ≤ γ'}{q : Γ C γ' ≤ γ''}
              {α : ∣_∣T⁻_ γ}{α' : ∣_∣T⁻_ γ'}{α'' : ∣_∣T⁻_ γ''}
            → _T⁻_⊢_≤_ p α α' → _T⁻_⊢_≤_ q α' α'' → _T⁻_⊢_≤_ (transC Γ p q) α α''
    coeT⁻    : {γ γ' : ∣ Γ ∣C} → Γ C γ ≤ γ' → ∣_∣T⁻_ γ' → ∣_∣T⁻_ γ
    cohT⁻    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ')(α' : ∣_∣T⁻_ γ') → _T⁻_⊢_≤_ p (coeT⁻ p α') α'
  infix 4 ∣_∣T⁻_
  infix 5 _T⁻_⊢_≤_
open PreordFam⁻ public

record PreordSec⁺ {i}(Γ : Preord i){j}(A : PreordFam⁺ Γ j) : Type (i ⊔ j) where
  field
    ∣_∣t⁺ : (γ : ∣ Γ ∣C) → ∣ A ∣T⁺ γ
    ≤t⁺   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ') → A T⁺ p ⊢ (∣_∣t⁺ γ) ≤ (∣_∣t⁺ γ')
  infix 4 ∣_∣t⁺
open PreordSec⁺ public
record PreordSec⁻ {i}(Γ : Preord i){j}(A : PreordFam⁻ Γ j) : Type (i ⊔ j) where
  field
    ∣_∣t⁻ : (γ : ∣ Γ ∣C) → ∣ A ∣T⁻ γ
    ≤t⁻   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ≤ γ') → A T⁻ p ⊢ (∣_∣t⁻ γ) ≤ (∣_∣t⁻ γ')
  infix 4 ∣_∣t⁻
open PreordSec⁻ public


-- Concrete Polarization

_⁻C : ∀{i} → Preord i → Preord i
Δ ⁻C = record 
     { ∣_∣C = ∣ Δ ∣C 
     ; _C_≤_ = λ δ₀ δ₁ → Δ C δ₁ ≤ δ₀ 
     ; refC = refC Δ 
     ; transC = swapp (transC Δ) 
     }
_⁻S : ∀{i j}{Γ : Preord i}{Δ : Preord j} → PreordMor Γ Δ → PreordMor (Γ ⁻C) (Δ ⁻C)
σ ⁻S = record { ∣_∣s = ∣ σ ∣s ; ≤s = ≤s σ }

_⁻CT : ∀ {i j}{Γ : Preord i} → PreordFam⁺ Γ j → PreordFam⁻ (Γ ⁻C) j
A ⁻CT = mkTy⁻ (∣ A ∣T⁺_) (λ p a a' → A T⁺ p ⊢ a' ≤ a) (refT⁺ A) (swapp (transT⁺ A)) (coeT⁺ A) (cohT⁺ A)

-- _⁻T : ∀ {i j}{Γ : Preord i} → PreordFam⁺ Γ j → PreordFam⁺ Γ j
-- A ⁻T = mkTy⁺ (∣ A ∣T⁺_) (λ p a a' → {!   !}) {!   !} {!   !} {!   !} {!   !}
