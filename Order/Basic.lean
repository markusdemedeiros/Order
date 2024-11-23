/-
# Separation Logic
-/

/-
Syntax of a generic separation logic
-/
inductive L (B : Type)
| base (b  : B) : L B
| bot : L B
| and  (l : L B) (r : L B) : L B
| or   (l : L B) (r : L B) : L B
| imp  (l : L B) (r : L B) : L B
| emp : L B
| sep  (l : L B) (r : L B) : L B
| wand (l : L B) (r : L B) : L B

def L.iff (l : L B) (r : L B) := L.and (L.imp l r) (L.imp r l)

def L.neg (p : L B) : L B := L.imp p L.bot

def L.top : L B := L.neg L.bot

def L.is_logical (l : L B) : Prop :=
  match l with
  | base _   => True
  | bot      => True
  | and _ _  => True
  | or _ _   => True
  | imp  _ _ => True
  | emp      => False
  | sep  _ _ => False
  | wand _ _ => False

open L

/--
Shallow embedding of Hilbert-style IP proof system
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

/-
Separation Algebras
-/
class SepC (M : Type) where
  sepC : M -> M -> M

infixl:65 " ∗ " => SepC.sepC

class SA (M : Type) extends SepC M where
  sepC_assoc : Std.Associative sepC
  sepC_comm : Std.Commutative sepC


/-
Semantics
-/
class Kripke.AtomicInterp (M B : Type) where
  ainterp : M -> B -> Prop

class Kripke.Ord (M : Type) where
  kle : M -> M -> Prop
infixl:65 " << " => Kripke.Ord.kle

def is_increasing [Kripke.Ord M] [SepC M] (e : M) : Prop :=
  ∀ m n : M, e ∗ m = n -> m << n

class Kripke.Structure (M : Type) extends Kripke.Ord M where
  kle_refl : ∀ m, kle m m
  kle_trans : ∀ m1 m2 m3, kle m1 m2 -> kle m2 m3 -> kle m1 m3

class Kripke.Model (M B : Type) [Kripke.Structure M] extends Kripke.AtomicInterp M B where
  kle_ainterp_mono : ∀ m n σ, m << n -> ainterp m σ -> ainterp n σ

@[simp]
def Kripke.interp_weak [Kripke.Structure M] [Kripke.Model M B] [SepC M] (m : M) (e : L B) :  Prop :=
  match e with
  | L.base b   => Kripke.AtomicInterp.ainterp m b
  | L.bot      => False
  | L.and l r  => interp_weak m l ∧ interp_weak m r
  | L.or l r   => interp_weak m l ∨ interp_weak m r
  | L.imp l r  => ∀ m0, m << m0 -> interp_weak m0 l -> interp_weak m0 r
  | L.emp      => is_increasing m
  | L.sep l r  => ∃ m1 m2 : M, m1 ∗ m2 = m ∧ interp_weak m1 l ∧ interp_weak m2 r
  | L.wand l r => ∀ m1 m2 : M, m ∗ m1 = m2 -> interp_weak m1 l -> interp_weak m2 r

@[simp]
def Kripke.interp_strong [Kripke.Structure M] [Kripke.Model M B] [SepC M] (m : M) (e : L B) : Prop :=
  match e with
  | L.base b   => Kripke.AtomicInterp.ainterp m b
  | L.bot      => False
  | L.and l r  => interp_strong m l ∧ interp_strong m r
  | L.or l r   => interp_strong m l ∨ interp_strong m r
  | L.imp l r  => ∀ m0, m << m0 -> interp_strong m0 l -> interp_strong m0 r
  | L.emp      => is_increasing m
  | L.sep l r  => ∃ m0 m1 m2 : M, m0 << m ∧ m1 ∗ m2 = m0 ∧ interp_strong m1 l ∧ interp_strong m2 r
  | L.wand l r => ∀ m0 m1 m2 : M, m << m0 -> m0 ∗ m1 = m2 -> interp_strong m1 l -> interp_strong m2 r


-- General interface for Kripke Semantics (not sure if interp_* are necessary)
class Kripke.Semantics (M B : Type) [Kripke.Ord M] extends Kripke.AtomicInterp M B where
  interp : M -> L B -> Prop
  interp_base : interp m (L.base b) = Kripke.AtomicInterp.ainterp m b
  interp_bot  : interp m L.bot = False
  interp_and  : interp m (L.and l r) = (interp m l ∧ interp m r)
  interp_or   : interp m (L.or l r) = (interp m l ∨ interp m r)
  interp_imp  : interp m (L.imp l r) = ∀ m0, m << m0 -> interp m0 l -> interp m0 r

instance weak_semantics [Kripke.Structure M] [Kripke.Model M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_weak
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance strong_semantics [Kripke.Structure M] [Kripke.Model M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_strong
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

/--
Monotonic denotations
-/
def Kripke.monotonic_denotation [Kripke.Ord M] [Kripke.Semantics M B] (e : L B) : Prop :=
  ∀ m n : M, n << m -> Kripke.Semantics.interp n e -> Kripke.Semantics.interp m e

def UCSA (M : Type) [Kripke.Ord M] [SepC M] : Prop :=
  ∀ m1 m2 m n, m1 ∗ m2 = m -> m << n -> ∃ (n1 n2 : M), n1 ∗ n2 = n ∧ m1 << n1 ∧ m2 << n2

def DCSA (M : Type) [Kripke.Ord M] [SepC M] : Prop :=
  ∀ m1 m2 m n1 n2, m1 ∗ m2 = m -> n1 << m1 -> n2 << m2 -> ∃(n : M), n1 ∗ n2 = n ∧ n << m

-- FIXME: Typeclasses for the next 4 lemmas
theorem weak_sep_mononicity [SepC M] [Kripke.Structure M] [Kripke.Model M B](e1 e2 : L B) :
    UCSA M ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@weak_semantics M _ _ _ _) e1 ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@weak_semantics M _ _ _ _) e2 ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@weak_semantics M _ _ _ _) (L.sep e1 e2) := by
  intro U
  unfold Kripke.monotonic_denotation
  simp [Kripke.Semantics.interp]
  intro M1 M2 m n Hnm m1 m2 Hm1m2 He1 He2
  rcases (U _ _ _ _ Hm1m2 Hnm) with ⟨ n1, n2, H1, H2, H3 ⟩
  exists n1
  exists n2
  apply And.intro
  · exact H1
  apply And.intro
  · exact M1 n1 m1 H2 He1
  · exact M2 n2 m2 H3 He2


theorem weak_wand_mononicity [SepC M] [Kripke.Structure M] [Kripke.Model M B] (e1 e2 : L B):
    DCSA M ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@weak_semantics M _ _ _ _) e1 ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@weak_semantics M _ _ _ _) e2 ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@weak_semantics M _ _ _ _) (L.wand e1 e2) := by
  intro D
  unfold Kripke.monotonic_denotation
  simp [Kripke.Semantics.interp]
  intro H1 H2
  intro m n Hmn
  intro H
  intro m1 He1
  unfold DCSA at D
  rcases (D m m1 (m ∗ m1) n m1 (by rfl) Hmn (Kripke.Structure.kle_refl m1)) with ⟨ n', Hn', Hn'mm1 ⟩
  apply (H2 (m ∗ m1) n' Hn'mm1)
  rw [<- Hn']
  apply H
  apply He1

--- These two theorems are sort of weird, why do we not require e1 and e2 to have monotone denotation?
--- The paper says they need it

theorem strong_sep_mononicity [SepC M] [Kripke.Structure M] [Kripke.Model M B](e1 e2 : L B) :
    -- @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@strong_semantics M _ _ _ _) e1 ->
    -- @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@strong_semantics M _ _ _ _) e2 ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@strong_semantics M _ _ _ _) (L.sep e1 e2) := by
  intro m n Hmn
  simp [Kripke.Semantics.interp]
  intro x Hx x1 x2 Hx1x2 Hi1 Hi2
  exists x
  apply And.intro
  · exact Kripke.Structure.kle_trans x n m Hx Hmn
  exists x1
  exists x2

theorem strong_wand_mononicity [SepC M] [Kripke.Structure M] [Kripke.Model M B](e1 e2 : L B) :
    -- @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@strong_semantics M _ _ _ _) e1 ->
    -- @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@strong_semantics M _ _ _ _) e2 ->
    @Kripke.monotonic_denotation _ _ Kripke.Structure.toOrd (@strong_semantics M _ _ _ _) (L.sep e1 e2) := by
  intro m n Hmn
  simp [Kripke.Semantics.interp]
  intro x Hx x1 x2 Hx1x2 Hi1 Hi2
  exists x
  apply And.intro
  · exact Kripke.Structure.kle_trans x n m Hx Hmn
  exists x1
  exists x2
