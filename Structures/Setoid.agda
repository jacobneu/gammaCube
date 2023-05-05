{-
Taken (with minor modification) from Agda formalization of the setoid universe,
by Thorsten Altenkrich, Simon Boulier, Ambrus Kaposi, Christian Sattler, and Filippo Sestini.
https://bitbucket.org/taltenkirch/setoid-univ
-}

module Structures.Setoid where

open import Prelude 


record Setoid i : Type (lsuc i) where
  field
    ∣_∣C : Type i
    _C_~_ : ∣_∣C → ∣_∣C → Prop i
    refC : ∀ γ → _C_~_ γ γ
    symC : ∀{γ γ'} → _C_~_ γ γ' → _C_~_ γ' γ
    transC : ∀{γ γ' γ''} → _C_~_ γ γ' → _C_~_ γ' γ'' → _C_~_ γ γ''
  infix 4 ∣_∣C
  infix 5 _C_~_
open Setoid public

record SetoidMor {i j}(Γ : Setoid i)(Δ : Setoid j) : Type (i ⊔ j) where
  field
    ∣_∣s : ∣ Γ ∣C → ∣ Δ ∣C
    ~s   : {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → Δ C (∣_∣s γ) ~ (∣_∣s γ')
  infix 4 ∣_∣s
open SetoidMor public

record SetoidFam {i}(Γ : Setoid i) j : Type (i ⊔ lsuc j) where
  constructor mkTy
  field
    ∣_∣T_   : ∣ Γ ∣C → Set j
    _T_⊢_~_ : ∀{γ γ'}(p : Γ C γ ~ γ') → ∣_∣T_ γ → ∣_∣T_ γ' → Prop j
    refT    : ∀{γ} α → _T_⊢_~_ (refC Γ γ) α α
    symT    : ∀{γ γ'}{p : Γ C γ ~ γ'}{α : ∣_∣T_ γ}{α' : ∣_∣T_ γ'}
            → _T_⊢_~_ p α α' → _T_⊢_~_ (symC Γ p) α' α
    transT  : ∀{γ γ' γ''}{p : Γ C γ ~ γ'}{q : Γ C γ' ~ γ''}
              {α : ∣_∣T_ γ}{α' : ∣_∣T_ γ'}{α'' : ∣_∣T_ γ''}
            → _T_⊢_~_ p α α' → _T_⊢_~_ q α' α'' → _T_⊢_~_ (transC Γ p q) α α''
    coeT    : {γ γ' : ∣ Γ ∣C} → Γ C γ ~ γ' → ∣_∣T_ γ → ∣_∣T_ γ'
    cohT    : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ')(α : ∣_∣T_ γ) → _T_⊢_~_ p α (coeT p α)
  infix 4 ∣_∣T_
  infix 5 _T_⊢_~_
open SetoidFam public


record SetoidSec {i}(Γ : Setoid i){j}(A : SetoidFam Γ j) : Type (i ⊔ j) where
  field
    ∣_∣t : (γ : ∣ Γ ∣C) → ∣ A ∣T γ
    ~t   : {γ γ' : ∣ Γ ∣C}(p : Γ C γ ~ γ') → A T p ⊢ (∣_∣t γ) ~ (∣_∣t γ')
  infix 4 ∣_∣t
open SetoidSec public