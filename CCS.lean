import Lean
import Std.Data.List.Lemmas
import Mathlib.Data.Fintype.Basic

open Lean (HashSet)
open Std (HashMap)

instance [Hashable α] [BEq α] : Membership α (HashSet α) where
  mem a s := s.contains a

inductive Action (Name : Type)
  | tau
  | bar (n : Name)
  | plain (n : Name)
  deriving DecidableEq, Hashable, BEq

notation "τ" => Action.tau

instance : Coe α (Action α) where
  coe := .plain

open Finset in 
instance [fin : Fintype Name] [DecidableEq Name] : Fintype (Action Name) where
  elems := insert τ (fin.elems.image .bar ∪ fin.elems.image .plain)
  complete
    | τ          => mem_insert_self ..
    | .bar _     => mem_insert_of_mem $ mem_union_left  _ $ mem_image_of_mem _ $ fin.complete _ 
    | (_ : Name) => mem_insert_of_mem $ mem_union_right _ $ mem_image_of_mem _ $ fin.complete _

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
  deriving DecidableEq, Hashable, BEq

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

variable [DecidableEq Name] [DecidableEq Const] [Fintype Name] [CCS.Interpretable Const Name]
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

namespace LTS

-- TODO: Most of the following functions should use `HashMap.modify`.

variable (State Label : Type) [Hashable State] [Hashable Label] [BEq State] [BEq Label]

abbrev Successors := HashMap Label $ HashSet State

abbrev Transitions := HashMap State $ Successors State Label

structure Transition (State Label : Type) where
  src   : State
  label : Label
  dst   : State

variable {State Label}

inductive Transition.Mem : State → Transition State Label → Prop
  | src : Mem s ⟨s, _, _⟩
  | dst : Mem s ⟨_, _, s⟩

instance : Membership State (Transition State Label) where
  mem := Transition.Mem

inductive Transitions.Mem : (Transition State Label) → (Transitions State Label) → Prop 
  | intro : (ts.find? t.src = some ts') → (ts'.find? t.label = some succs) → (succs.contains t.dst) → Mem t ts 

instance : Membership (Transition State Label) (Transitions State Label) where
  mem := Transitions.Mem

def Successors.merge (succ₁ succ₂ : Successors State Label) : Successors State Label :=
  HashMap.mergeWith (fun _ s₁ s₂ => s₁.merge s₂) succ₁ succ₂

namespace Transitions

def merge (ts₁ ts₂ : Transitions State Label) : Transitions State Label :=
  HashMap.mergeWith (fun _ s₁ s₂ => s₁.merge s₂) ts₁ ts₂

def mergeInto (ts : Transitions State Label) (src : State) (succs : Successors State Label) : 
    Transitions State Label :=
  let srcSuccs := ts.findD src ∅
  let srcSuccs' := srcSuccs.merge succs
  HashMap.insert ts src srcSuccs'

def insert (ts : Transitions State Label) (src : State) (l : Label) (dst : State) : 
    Transitions State Label :=
  let srcSuccs  := ts.findD src ∅
  let lSuccs    := srcSuccs.findD l ∅
  let lSuccs'   := lSuccs.insert dst
  let srcSuccs' := srcSuccs.insert l lSuccs'
  HashMap.insert ts src srcSuccs'

end Transitions

variable (State Label) in
structure _root_.LTS where
  states      : HashSet State 
  transitions : Transitions State Label

def empty : LTS State Label where
  states := ∅
  transitions := ∅

def successors (lts : LTS State Label) (src : State) : Successors State Label :=
  lts.transitions.findD src ∅

instance : EmptyCollection (LTS State Label) where
  emptyCollection := .empty

end LTS

namespace CCS

variable [CCS.Interpretable Const Name] [Hashable Name] [Hashable Const] [BEq Name] [BEq Const]

def lts : (CCS Name Const) → LTS (CCS Name Const) (Action Name) 
  | 0 => ∅
  | s@(α ° p) => { 
      states := p.lts.states.insert s, 
      transitions := p.lts.transitions.insert s α p
    }
  | s@(p + q) => { 
      states := p.lts.states.merge q.lts.states |>.insert s, -- Note, states p and q might be redundant from here on.
      transitions := p.lts.transitions |>.merge q.lts.transitions |>.mergeInto s (p.lts.successors p |>.merge $ q.lts.successors q)
    }
  | p ‖ q => sorry
  | (ν a) p => sorry
  | (c : Const) => sorry

variable {s : CCS Name Const}

theorem CCS.lts_state_mem_iff : x ∈ s.lts.states ↔ ∃ t, t ∈ s.lts.transitions ∧ x ∈ t :=
  sorry

theorem CCS.lts_transition_mem_iff : ⟨p, α, p'⟩ ∈ s.lts.transitions ↔ p -[α]→ p' :=
  sorry

end CCS

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
