import CCS.Basic
import CCS.LTS

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
      transitions := p.lts.transitions |>.merge q.lts.transitions |>.mergeInto s (p.lts.successors p |>.merge <| q.lts.successors q)
    }
  | p ‖ q => sorry
  | (ν a) p => sorry
  | (c : Const) => sorry

variable {s : CCS Name Const}

theorem CCS.lts_state_mem_iff : x ∈ s.lts.states ↔ ∃ t, t ∈ s.lts.transitions ∧ x ∈ t :=
  sorry

theorem CCS.lts_transition_mem_iff : ⟨p, α, p'⟩ ∈ s.lts.transitions ↔ p -[α]→ p' :=
  sorry
