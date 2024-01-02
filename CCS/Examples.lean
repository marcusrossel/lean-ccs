import CCS.Basic

-- Examples from http://www.cse.unsw.edu.au/~cs3151/22T2/Week%2008/Wednesday%20Slides.pdf

inductive N
  | in20 | in50 | outCoke | outMars
  deriving DecidableEq

instance : Fintype N where
  elems := {.in20, .in50, .outCoke, .outMars}
  complete n := by cases n <;> decide

inductive C
  | repeat₁ | repeat₂
  deriving DecidableEq

open N C

def VM₁ : CCS N C := in20 ° outCoke ° in50 ° outMars ° repeat₁
def VM₂ : CCS N C := (in50 ° outMars ° repeat₂) + (in20 ° outCoke ° repeat₂)
def VM₃ : CCS N := in50 ° (outCoke ° 0 + outMars ° 0)
def VM₄ : CCS N := (in50 ° outCoke ° 0) + (in50 ° outMars ° 0)

instance : CCS.Interpretable C N where
  transition
    | .repeat₁, τ, p => p = VM₁
    | .repeat₂, τ, p => p = VM₂
    | _, _, _ => False

instance : Decidable <| CCS.Interpretable.transition (c : C) (act : Action N) p :=
  match c with
  | .repeat₁ =>
    if ha : act = τ then if hp : p = VM₁
    then .isTrue  <| ha ▸ hp
    else .isFalse <| ha ▸ hp
    else .isFalse <| by simp [CCS.Interpretable.transition, ha]
  | .repeat₂ =>
    if ha : act = τ then if hp : p = VM₂
    then .isTrue  <| ha ▸ hp
    else .isFalse <| ha ▸ hp
    else .isFalse <| by simp [CCS.Interpretable.transition, ha]

example : VM₁ -[in20]→ (outCoke ° in50 ° outMars ° repeat₁) := by decide
example : ¬ VM₁ -[in50]→ (outCoke ° in50 ° outMars ° repeat₁) := by decide

example : VM₂ -[in50]→ (outMars ° repeat₂) := by decide
example : VM₂ -[in20]→ (outCoke ° repeat₂) := by decide
example : ¬ VM₂ -[in50]→ (outCoke ° repeat₂) := by decide
example : repeat₂ -[τ]→ VM₂ := by decide
