\begin{code}
module extra.LambdaReduction where
\end{code}

## Imports

\begin{code}
open import plfa.Untyped using (_⊢_; ★; _·_; ƛ_; _,_; _[_])
\end{code}

## Full beta reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′
\end{code}

\begin{code}
infix  2 _—↠_
infix  1 start_
infixr 2 _—→⟨_⟩_
infix  3 _[]

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _[] : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

start_ : ∀ {Γ} {A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
start M—↠N = M—↠N
\end{code}

\begin{code}
—↠-trans : ∀{Γ}{A}{L M N : Γ ⊢ A}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M []) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)
\end{code}

## Reduction is a congruence

\begin{code}
—→-app-cong : ∀{Γ}{L L' M : Γ ⊢ ★}
            → L —→ L'
            → L · M —→ L' · M
—→-app-cong (ξ₁ ll') = ξ₁ (—→-app-cong ll')
—→-app-cong (ξ₂ ll') = ξ₁ (ξ₂ ll')
—→-app-cong β = ξ₁ β
—→-app-cong (ζ ll') = ξ₁ (ζ ll')
\end{code}



## Multi-step reduction is a congruence

\begin{code}
abs-cong : ∀ {Γ} {N N' : Γ , ★ ⊢ ★}
         → N —↠ N'
           ----------
         → ƛ N —↠ ƛ N'
abs-cong (M []) = ƛ M []
abs-cong (L —→⟨ r ⟩ rs) = ƛ L —→⟨ ζ r ⟩ abs-cong rs
\end{code}

\begin{code}
appL-cong : ∀ {Γ} {L L' M : Γ ⊢ ★}
         → L —↠ L'
           ---------------
         → L · M —↠ L' · M
appL-cong {Γ}{L}{L'}{M} (L []) = L · M []
appL-cong {Γ}{L}{L'}{M} (L —→⟨ r ⟩ rs) = L · M —→⟨ ξ₁ r ⟩ appL-cong rs
\end{code}

\begin{code}
appR-cong : ∀ {Γ} {L M M' : Γ ⊢ ★}
         → M —↠ M'
           ---------------
         → L · M —↠ L · M'
appR-cong {Γ}{L}{M}{M'} (M []) = L · M []
appR-cong {Γ}{L}{M}{M'} (M —→⟨ r ⟩ rs) = L · M —→⟨ ξ₂ r ⟩ appR-cong rs
\end{code}

