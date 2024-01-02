import Lean
import Std.Lean.HashSet
import Std.Data.HashMap

open Lean (HashSet)
open Std (HashMap)

namespace LTS

-- TODO: Most of the following functions should use `HashMap.modify`.

variable (State Label : Type) [Hashable State] [Hashable Label] [BEq State] [BEq Label]

abbrev Successors := HashMap Label (HashSet State)

abbrev Transitions := HashMap State (Successors State Label)

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

-- For each `(αᵢ, dstᵢ) ∈ succs` add the transition `(src, αᵢ, dstᵢ)` to `ts`.
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

-- TODO: Why do we have separate sets of states and transitions? Doesn't the set of transitions also
--       tell us all of the states?
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
