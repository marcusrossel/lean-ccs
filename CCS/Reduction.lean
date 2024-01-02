import CCS.Basic
import CCS.LTS

open Lean (HashSet)

instance [Hashable α] [BEq α] : Membership α (Lean.HashSet α) where
  mem a s := s.contains a

namespace CCS

def restrictN : List Name → CCS Name Const → CCS Name Const
  | [],       p => p
  | hd :: tl, p => (ν hd) restrictN tl p

local notation "(ν* " νs ") " p => restrictN νs p

variable [CCS.Interpretable Const Name] [Hashable Name] [Hashable Const] [BEq Name] [BEq Const]
variable [DecidableEq Name]

def lts : (CCS Name Const) → LTS (CCS Name Const) (Action Name) :=
  go []
where
  go («νs» : List Name) : (CCS Name Const) → LTS (CCS Name Const) (Action Name)
  | 0 => ∅
  | (ν a) p => go («νs».concat a) p
  | s@(α ° p) =>
    let s' := (ν* νs) s
    -- If `α` is a restricted name, we don't get any transitions from `s`.
    if νs.any (· ∈ α) then
      { states := {s'}, transitions := ∅ }
    else
      let ltsP := go νs p
      let p' := (ν* νs) p
      { states := ltsP.states.insert s', transitions := ltsP.transitions.insert s' α p' }
  | s@(p + q) =>
    let ltsP := go νs p
    let ltsQ := go νs q
    let p' := (ν* νs) p
    let q' := (ν* νs) q
    let s' := (ν* νs) s
    -- We don't transition to process `p` or `q` directly, but rather to whatever states *they* can
    -- transition to. This set `succs` are the transitions to those successor states (excluding
    -- those involving restricted transitions).
    let succs :=
      ltsP.successors p'   |>.merge
      (ltsQ.successors q') |>.filter
      fun a _ => νs.all (· ∉ a)
    {
      states := ltsP.states.merge ltsQ.states |>.insert s',
      transitions := ltsP.transitions |>.merge ltsQ.transitions |>.mergeInto s' succs
    }
  | p ‖ q => {
    states := sorry
    transitions := sorry
  }
  | (c : Const) => {
    states := sorry
    transitions := sorry
  }

variable {s : CCS Name Const}

theorem CCS.lts_state_mem_iff : x ∈ s.lts.states ↔ ∃ t, t ∈ s.lts.transitions ∧ x ∈ t :=
  sorry

theorem CCS.lts_transition_mem_iff : ⟨p, α, p'⟩ ∈ s.lts.transitions ↔ p -[α]→ p' :=
  sorry
