/-- A reflexive relation -/
class Reflexive (op : α → α → Prop) : Prop where
  refl : {a : α} → op a a

/-- A reflexive relation -/
class Transitive (op : α → α → Prop) : Prop where
  trans : {a b c : α} → op a b -> op b c -> op a c
