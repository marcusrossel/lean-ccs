import Lean

instance [Hashable α] [BEq α] : Membership α (Lean.HashSet α) where
  mem a s := s.contains a
