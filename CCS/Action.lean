import Mathlib.Data.Fintype.Basic

inductive Action (Name : Type)
  | tau
  | bar (n : Name)
  | plain (n : Name)
  deriving DecidableEq, Hashable, BEq

namespace Action

notation "τ" => Action.tau

instance : Coe α (Action α) where
  coe := .plain

open Finset in
instance [fin : Fintype Name] [DecidableEq Name] : Fintype (Action Name) where
  elems := insert τ (fin.elems.image .bar ∪ fin.elems.image .plain)
  complete
    | τ          => mem_insert_self ..
    | bar _      => mem_insert_of_mem <| mem_union_left  _ <| mem_image_of_mem _ <| fin.complete _
    | (_ : Name) => mem_insert_of_mem <| mem_union_right _ <| mem_image_of_mem _ <| fin.complete _

def barred : Action Name → Action Name
  | τ          => τ
  | bar n      => n
  | (n : Name) => bar n

prefix:50 "~" => Action.barred

inductive References : Action Name → Name → Prop
  | bar   : References (bar n) n
  | plain : References (n : Name) n

instance : Membership Name (Action Name) where
  mem n a := a.References n

section Decidable

variable [DecidableEq Name] {act : Action Name}

def references : Action Name → Name → Bool
  | tau, _ => false
  | bar n, n' | plain n, n' => n = n'

theorem References.iff_references : n ∈ act ↔ act.references n := by
  cases act <;> simp [references]
  case tau => intro; contradiction
  all_goals constructor <;> (intro h; cases h; constructor)

instance : Decidable (n ∈ act) :=
  decidable_of_iff' _ References.iff_references
