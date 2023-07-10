import Lean
import Std.Data.List.Lemmas
-- import Mathlib.Data.FinEnum

class Finite (α : Type) where
  elems : List α
  complete : ∀ a, a ∈ elems 

inductive List.Any (p : α → Prop) : List α → Prop
  | head : (p hd) → Any p (hd :: tl)
  | tail : (Any p tl) → Any p (hd :: tl)

theorem List.Any.iff_exists_satisfying_mem {l : List α} : l.Any p ↔ ∃ a, (a ∈ l) ∧ (p a) where
  mp ha := by
    induction ha 
    case head h => exact ⟨_, ⟨.head _, h⟩⟩  
    case tail hi => exact hi.elim fun _ ⟨hm, hp⟩ => ⟨_, ⟨.tail _ hm, hp⟩⟩  
  mpr h := by
    have ⟨_, hm, hp⟩ := h; clear h
    induction hm
    case head => exact .head ‹_› 
    case tail => exact .tail ‹_› 

def List.any' (p : α → Prop) [DecidablePred p] : List α → Bool
  | [] => false
  | hd :: tl => if p hd then true else tl.any' p

theorem List.Any.iff_any' {l : List α} [DecidablePred p] : l.Any p ↔ l.any' p where
  mp ha := by induction ha <;> simp_all [any']
  mpr h := by
    induction l <;> simp_all [any']
    case cons hi =>
      split at h
      case inl => exact .head ‹_›
      case inr => exact .tail $ hi h

instance [DecidablePred p] : DecidablePred (List.Any p) :=
  fun l => 
    if h : l.any' p
    then .isTrue (List.Any.iff_any'.mpr h) 
    else .isFalse (mt List.Any.iff_any'.mp $ h) 

instance [f : Finite α] [DecidablePred p] : Decidable (∃ a : α, p a) :=
  if h : f.elems.Any (p ·) 
  then .isTrue $ List.Any.iff_exists_satisfying_mem.mp h |>.elim fun a ⟨_, h⟩ => ⟨a, h⟩
  else .isFalse fun ⟨a, ha⟩ => (mt List.Any.iff_exists_satisfying_mem.mpr $ h) ⟨a, f.complete _, ha⟩  










inductive Action (Name : Type)
  | tau
  | bar (n : Name)
  | plain (n : Name)
  deriving DecidableEq

notation "τ" => Action.tau

instance : Coe α (Action α) where
  coe := .plain

open List in 
instance [fin : Finite Name] : Finite (Action Name) where
  elems := τ :: (fin.elems.map .bar ++ fin.elems.map .plain)
  complete
    | τ          => .head _
    | .bar _     => .tail _ $ mem_append_of_mem_left _ $ mem_map_of_mem _ $ fin.complete _ 
    | (_ : Name) => .tail _ $ mem_append_of_mem_right _ $ mem_map_of_mem _ $ fin.complete _ 

def Action.barred : Action Name → Action Name
  | τ          => τ
  | bar n      => n
  | (n : Name) => bar n

prefix:50 "~" => Action.barred

inductive Action.References : Action Name → Name → Prop
  | bar : References (bar n) n
  | plain : References (n : Name) n

instance : Membership Name (Action Name) where
  mem n a := a.References n

section Decidable

variable [DecidableEq Name] {act : Action Name}

def Action.references : Action Name → Name → Bool
  | tau, _ => false
  | bar n, n' | plain n, n' => n = n'

theorem Action.References.iff_references : act.References n ↔ act.references n := by
  cases act <;> simp [references]
  case tau => intro; contradiction
  all_goals constructor <;> (intro h; cases h; constructor)

instance : Decidable (n ∈ act) :=
  if h : act.references n 
  then .isTrue (Action.References.iff_references.mpr h) 
  else .isFalse (mt Action.References.iff_references.mp $ h) 

end Decidable

inductive CCS (Name : Type) (Const : Type := Empty)
  | null     : CCS Name Const
  | «prefix» : Action Name → CCS Name Const → CCS Name Const
  | choice   : CCS Name Const → CCS Name Const → CCS Name Const
  | parallel : CCS Name Const → CCS Name Const → CCS Name Const
  | restrict : Name → CCS Name Const → CCS Name Const
  | const    : Const → CCS Name Const
  deriving DecidableEq

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
class CCS.Interpretable (Const Name : Type) where
  transition : Const → Action Name → CCS Name Const → Prop

instance : CCS.Interpretable Empty Name where
  transition e _ _ := nomatch e

section Unhygienic

set_option hygiene false

local notation p " -[" α "]→ " p' => CCS.Transition p α p' 

inductive CCS.Transition [Interpretable Const Name] : 
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

variable [DecidableEq Name] [DecidableEq Const] [Finite Name] [CCS.Interpretable Const Name]
variable [∀ (c : Const) (act : Action Name) p, Decidable $ CCS.Interpretable.transition c act p]

def CCS.transition : (CCS Name Const) → (Action Name) → (CCS Name Const) → Bool 
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

theorem CCS.Transition.iff_transition : (p -[act]→ p') ↔ (CCS.transition p act p') where
  mp t := by
    induction t <;> simp_all [transition]
    case communication => apply Or.inr; apply Or.inr; exists ‹_›
  mpr h := by
    induction p generalizing p' act <;> simp_all [transition]
    case «prefix» => constructor
    case choice hi₁ hi₂ => 
      cases h 
      case inl h => exact .choiceLeft $ hi₁ h
      case inr h => exact .choiceRight $ hi₂ h
    case parallel hi₁ hi₂ =>
      cases p' <;> simp_all [transition]
      case parallel => 
        cases h <;> try cases ‹_ ∨ _ ›
        case inl h => 
          cases h.right
          exact .parallelLeft $ hi₁ h.left
        case inr.inl h => 
          cases h.right
          exact .parallelRight $ hi₂ h.left
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
  if h : CCS.transition p act p' 
  then .isTrue (CCS.Transition.iff_transition.mpr h) 
  else .isFalse (mt CCS.Transition.iff_transition.mp $ h) 

end Decidable

section Computable

variable (State Action : Type) [Hashable State] [Hashable Action] [BEq State] [BEq Action]

structure LTS.Edge :=
  src : State
  act : Action
  dst : State
  deriving Hashable, BEq

structure LTS where
  edges : Lean.HashSet $ LTS.Edge State Action

def CCS.lts [Interpretable Const Name] : LTS State Action := sorry

end Computable







-- Examples from http://www.cse.unsw.edu.au/~cs3151/22T2/Week%2008/Wednesday%20Slides.pdf

inductive N  
  | in20 | in50 | outCoke | outMars
  deriving DecidableEq

instance : Finite N where
  elems := [.in20, .in50, .outCoke, .outMars] 
  complete n := by cases n <;> decide

inductive C
  | repeat₁ | repeat₂
  deriving DecidableEq

open N C

def VM₁ : CCS N C := in20 ° outCoke ° in50 ° outMars ° repeat₁
def VM₂ : CCS N C := (in50 ° outMars ° repeat₂) + (in20 ° outCoke ° repeat₂)
def VM₃ : CCS N C := in50 ° (outCoke ° 0 + outMars ° 0)
def VM₄ : CCS N C := (in50 ° outCoke ° 0) + (in50 ° outMars ° 0)

instance : CCS.Interpretable C N where
  transition 
    | .repeat₁, τ, p => p = VM₁
    | .repeat₂, τ, p => p = VM₂
    | _, _, _ => False

instance : Decidable $ CCS.Interpretable.transition (c : C) (act : Action N) p :=
  match c with
  | .repeat₁ => 
    if ha : act = τ then if hp : p = VM₁ 
    then .isTrue  $ ha ▸ hp 
    else .isFalse $ ha ▸ hp 
    else .isFalse $ by simp [CCS.Interpretable.transition, ha]
  | .repeat₂ =>
    if ha : act = τ then if hp : p = VM₂ 
    then .isTrue  $ ha ▸ hp 
    else .isFalse $ ha ▸ hp 
    else .isFalse $ by simp [CCS.Interpretable.transition, ha]

example : VM₁ -[in20]→ (outCoke ° in50 ° outMars ° repeat₁) := by decide
example : ¬ VM₁ -[in50]→ (outCoke ° in50 ° outMars ° repeat₁) := by decide

example : VM₂ -[in50]→ (outMars ° repeat₂) := by decide
example : VM₂ -[in20]→ (outCoke ° repeat₂) := by decide
example : ¬ VM₂ -[in50]→ (outCoke ° repeat₂) := by decide
example : repeat₂ -[τ]→ VM₂ := by decide

