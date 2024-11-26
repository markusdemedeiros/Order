import Order.Logic

open L

/--
Shallow embedding of Hilbert-style IP proof system

Used to derive generic rules
-/
class IP (R : L B -> Prop) where
  mp    : R φ -> R (imp φ ψ) -> R ψ
  imp1  : R <| imp φ <| imp ψ φ
  imp2  : R <| imp (imp φ (imp ψ χ)) <| imp (imp φ ψ) <| imp φ χ
  andI  : R <| imp φ <| imp ψ (and φ ψ)
  andE1 : R <| imp (and φ ψ) φ
  andE2 : R <| imp (and φ ψ) ψ
  orI1  : R <| imp φ (or φ ψ)
  orI2  : R <| imp ψ (or φ ψ)
  orE   : R <| imp (imp φ χ) <| imp (imp ψ χ) <| imp (or φ ψ) χ
  botE  : R <| imp bot φ


/-
Shallow embedding of optional axioms
-/

class WEM (R : L B -> Prop) extends IP R where
  wem : R <| or (neg φ) (neg (neg φ))

class GD (R : L B -> Prop) extends IP R where
  gd : R <| or (imp φ ψ) (imp ψ φ)

class EM (R : L B -> Prop) extends IP R where
  em : R <| or φ (neg φ)

/--
Shallow embedding of SL axioms
-/
class SL (R : L B -> Prop) extends IP R where
  scomm  : R <| imp (sep φ ψ) (sep ψ φ)
  sA1    : (R <| imp (sep φ ψ) χ) -> (R <| imp φ (wand ψ χ))
  sA2    : (R <| imp φ (wand ψ χ)) -> (R <| imp (sep φ ψ) χ)
  semp   : R <| iff (sep φ emp) φ
  sassoc : R <| imp (sep (sep φ ψ) χ) <| (sep φ (sep ψ χ))
  smono  : R (imp φ1 ψ1) -> R (imp φ2 ψ2) -> R (imp (sep φ1 φ2) (sep ψ1 ψ2))

/-
Shallow embedding of optional SL actioms
-/

class GC (R : L B -> Prop) extends SL R where
  starE : R <| imp (sep φ ψ) φ

class EE (R : L B -> Prop) extends SL R where
  eE : R <| imp (and emp (sep φ ψ)) φ

class EDup (R : L B -> Prop) extends SL R where
  eDup : R <| imp (and emp φ) <| (sep φ φ)

class MallocFree (R : L B -> Prop) extends EE R, EDup R

/-
Derived laws
-/
/-
def wandE1 [IP R] [SL R] : R <| imp (sep (wand ϕ ψ) ϕ) ψ := by sorry

def or_sep_iff [IP R] [SL R] : R <| iff (sep (or ϕ ψ) χ) (or (sep ϕ ψ) (sep ϕ χ)) := sorry

def and_sep_iff [IP R] [SL R] : R <| iff (sep (and ϕ ψ) χ) (and (sep ϕ ψ) (sep ϕ χ)) := sorry
-/
