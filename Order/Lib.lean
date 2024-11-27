/-- A reflexive relation -/
class Reflexive (op : α → α → Prop) : Prop where
  refl : {a : α} → op a a

/-- A reflexive relation -/
class Transitive (op : α → α → Prop) : Prop where
  trans : {a b c : α} → op a b -> op b c -> op a c

/-- An associatve 3-place operato -/
class Associative (op : α → α -> α → Prop) : Prop where
  assoc : {x y z xy xyz : α} → op x y xy -> op xy z xyz -> ∃ yz, op y z yz ∧ op x yz xyz

/-- A commutative 3-place operator -/
class Commutative (op : α → α -> α → Prop) : Prop where
  comm : {a b c : α} → op a b c -> op b a c
