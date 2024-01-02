import CCS.Lean
import CCS.Action

inductive CCS (Name : Type) (Const : Type := Empty)
  | null     : CCS Name Const
  | «prefix» : Action Name → CCS Name Const → CCS Name Const
  | choice   : CCS Name Const → CCS Name Const → CCS Name Const
  | parallel : CCS Name Const → CCS Name Const → CCS Name Const
  | restrict : Name → CCS Name Const → CCS Name Const
  | const    : Const → CCS Name Const
  deriving DecidableEq, Hashable, BEq

namespace CCS

instance : OfNat (CCS Name Const) 0 where
  ofNat := .null

instance : Add (CCS Name Const) where
  add := .choice

instance : Coe Const (CCS Name Const) where
  coe := .const

infixr:80 " ° " => CCS.prefix

infixr:50 " ‖ " => CCS.parallel

notation "(ν " a ") " p => CCS.restrict a p

-- `Const` is an interpretable type over `Name` if it has an associated transition relation.
class Interpretable (Const Name : Type) where
  transition : Const → Action Name → CCS Name Const → Prop

instance : Interpretable Empty Name where
  transition e _ _ := nomatch e

section Unhygienic

set_option hygiene false

local notation p " -[" α "]→ " p' => CCS.Transition p α p'

inductive Transition [Interpretable Const Name] :
    (CCS Name Const) → (Action Name) → (CCS Name Const) → Prop
  | «prefix»      : (α ° p) -[α]→ p
  | choiceLeft    : (p -[α]→ p') → (p + q) -[α]→ p'
  | choiceRight   : (q -[α]→ q') → (p + q) -[α]→ q'
  | parallelLeft  : (p -[α]→ p') → (p ‖ q) -[α]→ (p' ‖ q)
  | parallelRight : (q -[α]→ q') → (p ‖ q) -[α]→ (p ‖ q')
  | communication : (p -[α]→ p') → (q -[~α]→ q') → (p ‖ q) -[τ]→ (p' ‖ q')
  | restriction   : (p -[α]→ p') → (a ∉ α) → ((ν a) p) -[α]→ ((ν a) p')
  | const         : (Interpretable.transition (c : Const) α p) → c -[α]→ p

end Unhygienic

notation p " -[" α "]→ " p' => CCS.Transition p α p'

section Decidable

variable [DecidableEq Name] [DecidableEq Const] [Fintype Name] [CCS.Interpretable Const Name]
variable [∀ (c : Const) (act : Action Name) p, Decidable <| CCS.Interpretable.transition c act p]

def transition : (CCS Name Const) → (Action Name) → (CCS Name Const) → Bool
  | α ° p, α', p' => (α = α') ∧ (p = p')
  | p + q, α, pq' => (transition p α pq') ∨ (transition q α pq')
  | p ‖ q, α, p' ‖ q' =>
    (transition p α p') ∧ (q = q') ∨
    (transition q α q') ∧ (p = p') ∨
    (α = τ) ∧ ∃ α', (transition p α' p') ∧ (transition q (~α') q')
  | (ν a) p, α, (ν a') p' => (transition p α p') ∧ (a ∉ α) ∧ (a = a')
  | (c : Const), α, p => Interpretable.transition c α p
  | _, _, _ => false

variable {p p' : CCS Name Const}

theorem Transition.iff_transition : (p -[act]→ p') ↔ (CCS.transition p act p') where
  mp t := by
    induction t <;> simp_all [transition]
    case communication => apply Or.inr; apply Or.inr; exists ‹_›
  mpr h := by
    induction p generalizing p' act <;> try simp_all [transition]
    case «prefix» => constructor
    case choice hi₁ hi₂ =>
      cases h
      case inl h => exact .choiceLeft <| hi₁ h
      case inr h => exact .choiceRight <| hi₂ h
    case parallel hi₁ hi₂ =>
      cases p' <;> simp_all [transition]
      case parallel =>
        cases h <;> try cases ‹_ ∨ _ ›
        case inl h =>
          cases h.right
          exact .parallelLeft <| hi₁ h.left
        case inr.inl h =>
          cases h.right
          exact .parallelRight <| hi₂ h.left
        case inr.inr h =>
          have ⟨hτ, ⟨_, ha₁, ha₂⟩⟩ := h
          subst hτ
          exact .communication (hi₁ ha₁) (hi₂ ha₂)
    case restrict hi =>
      cases p' <;> simp_all [transition]
      case restrict => exact .restriction (hi h.left) (h.right.right ▸ h.right.left)
    case const =>
      exact .const h

instance : Decidable (p -[act]→ p') :=
  decidable_of_iff' _ CCS.Transition.iff_transition
