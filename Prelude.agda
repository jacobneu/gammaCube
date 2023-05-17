

module Prelude where 

open import Agda.Primitive public
  renaming ( Set   to Type
           ; Setω  to Typeω )

-- Unit

record ⊤  : Type  where constructor tt

-- Sigma

open import Agda.Builtin.Sigma public

infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀{ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Σ[ x ∈ A ] B
infixl 4 _×_

record Σp {ℓ ℓ'} (A : Prop ℓ) (B : A → Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  constructor _,p_
  field
    fstp : A
    sndp : B fstp
infixl 5 _,p_
open Σp public
_×p_ : ∀{ℓ ℓ'} → Prop ℓ → Prop ℓ' → Prop (ℓ ⊔ ℓ')
A ×p B = Σp A λ _ → B
infixl 4 _×p_

record Σps {ℓ ℓ'} (A : Prop ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,ps_
  field
    fstps : A
    sndps : B fstps
infixl 5 _,ps_
open Σps public
_×ps_ : ∀{ℓ ℓ'} → Prop ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A ×ps B = Σps A λ _ → B
infixl 4 _×ps_

record Σsp {ℓ ℓ'} (A : Type ℓ) (B : A → Prop ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,sp_
  field
    fstsp : A
    sndsp : B fstsp
infixl 5 _,sp_
open Σsp public
_×sp_ : ∀{ℓ ℓ'} → Type ℓ → Prop ℓ' → Type (ℓ ⊔ ℓ')
A ×sp B = Σsp A λ _ → B
infixl 4 _×sp_

record ↑ps {ℓ}(A : Prop ℓ) : Type ℓ where
  constructor mk↑ps
  field
    un↑ps : A
open ↑ps public

-- Empty

data ⊥ : Type where

⊥elim : ∀{ℓ}{A : Type ℓ} → ⊥ → A
⊥elim ()

⊥elimp : ∀{ℓ}{A : Prop ℓ} → ⊥ → A
⊥elimp ()

-- Props

record ↑pl {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor mk↑pl
  field
    un↑pl : A
open ↑pl public

data Tr {i}(A : Type i) : Prop i where
  tr : A → Tr A

untr : ∀{i j}{A : Type i}{B : Tr A → Prop j} → ((x : A) → B (tr x)) → (x : Tr A) → B x
untr f (tr x) = f x

data ⊥p : Prop where

⊤p : Prop
⊤p = Tr ⊤

ttp : ⊤p
ttp = tr tt

⊥pelim : ∀{ℓ}{A : Type ℓ} → ⊥p → A
⊥pelim ()
⊥pelimp : ∀{ℓ}{A : Prop ℓ} → ⊥p → A
⊥pelimp ()
⊤p' : ∀{ℓ} → Prop ℓ
⊤p' = ↑pl ⊤p

ttp' : ∀{ℓ} → ⊤p' {ℓ}
ttp' = mk↑pl ttp

⊥p' : ∀{ℓ} → Prop ℓ
⊥p' = ↑pl ⊥p

⊥pelim' : ∀{ℓ ℓ'}{A : Type ℓ} → ⊥p' {ℓ'} → A
⊥pelim' ()

-- Bool

data 𝟚 : Type where
  tt ff : 𝟚

if_then_else_ : ∀{ℓ}{C : 𝟚 → Type ℓ}(b : 𝟚)(c : C tt)(d : C ff) → C b
if tt then c else d = c
if ff then c else d = d

pif_then_else_ : ∀{ℓ}{C : 𝟚 → Prop ℓ}(b : 𝟚)(c : C tt)(d : C ff) → C b
pif tt then c else d = c
pif ff then c else d = d

_≟𝟚_ : 𝟚 → 𝟚 → Prop
x₀ ≟𝟚 x₁ = if x₀ then (if x₁ then ⊤p else ⊥p) else (if x₁ then ⊥p else ⊤p)

ref𝟚 : ∀ b → b ≟𝟚 b
ref𝟚 tt = ttp
ref𝟚 ff = ttp

sym𝟚 : ∀ {b₀ b₁} → b₀ ≟𝟚 b₁ → b₁ ≟𝟚 b₀
sym𝟚 {tt} {tt} _ = ttp
sym𝟚 {ff} {ff} _ = ttp

trans𝟚 : ∀ {b₀ b₁ b₂} → b₀ ≟𝟚 b₁ → b₁ ≟𝟚 b₂ → b₀ ≟𝟚 b₂
trans𝟚 {tt} {tt} {tt} _ _ = ttp
trans𝟚 {ff} {ff} {ff} _ _ = ttp

-- Identity Types

data _≡_ {ℓ} {X : Type ℓ} : X → X → Type ℓ where
  refl : {x : X} → x ≡ x 
infix 4 _≡_

infixr 30 _≡⟨_⟩_
infixl 40 _∎

_≡⟨_⟩_ : ∀ {ℓ} {X : Type ℓ} (x : X) {y : X} (p : x ≡ y) {z : X} (q : y ≡ z) → x ≡ z
x ≡⟨ refl ⟩ refl = refl

_∎ : ∀ {ℓ} {X : Type ℓ} (x : X) → x ≡ x
x ∎ = refl 

-- Function stuff (replace with import?)

swapp : ∀ {i} {X Y Z : Prop i} → (X → Y → Z) → Y → X → Z
swapp f y x = f x y

record _≅_ {i} (X Y : Type i) : Type i where 
  field
    ltr : X → Y
    rtl : Y → X
    ≡idl : (x : X) → rtl(ltr x) ≡ x
    ≡idr : (y : Y) → ltr(rtl y) ≡ y
open _≅_ public 