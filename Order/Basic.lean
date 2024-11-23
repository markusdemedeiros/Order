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

-- General interface for Kripke Semantics
class Kripke.Semantics (M B : Type) [Kripke.Ord M] extends Kripke.AtomicInterp M B where
  interp : M -> L B -> Prop
  interp_base : interp m (L.base b) = Kripke.AtomicInterp.ainterp m b
  interp_bot  : interp m L.bot = False
  interp_and  : interp m (L.and l r) = (interp m l ∧ interp m r)
  interp_or   : interp m (L.or l r) = (interp m l ∨ interp m r)
  interp_imp  : interp m (L.imp l r) = ∀ m0, m << m0 -> interp m0 l -> interp m0 r

-- Interface for Kripke semantics with strong wand
class Kripke.StrongWandSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) where
  interp_wand : S.interp m (L.wand l r) = ∀ m0 m1 m2 : M, m << m0 -> m0 ∗ m1 = m2 -> S.interp m1 l -> S.interp m2 r

-- Interface for Kripke semantics with strong sep
class Kripke.StrongSepSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) where
  interp_sep : S.interp m (L.sep l r) = ∃ m0 m1 m2 : M, m0 << m ∧ m1 ∗ m2 = m0 ∧ S.interp m1 l ∧ S.interp m2 r

-- Interface for Kripke semantics with weak wand
class Kripke.WeakWandSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) where
  interp_wand : S.interp m (L.wand l r) = ∀ m1 m2 : M, m ∗ m1 = m2 -> S.interp m1 l -> S.interp m2 r

-- Interface for Kripke semantics with weak sep
class Kripke.WeakSepSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) where
  interp_sep : S.interp m (L.sep l r) = ∃ m1 m2 : M, m1 ∗ m2 = m ∧ S.interp m1 l ∧ S.interp m2 r


/-
Instances of Kripke semantics
-/

/--
Flat semantics: both sep and wand are weak
-/
@[simp]
def Kripke.interp_flat [Kripke.Structure M] [Kripke.Model M B] [SepC M] (m : M) (e : L B) :  Prop :=
  match e with
  | L.base b   => Kripke.AtomicInterp.ainterp m b
  | L.bot      => False
  | L.and l r  => interp_flat m l ∧ interp_flat m r
  | L.or l r   => interp_flat m l ∨ interp_flat m r
  | L.imp l r  => ∀ m0, m << m0 -> interp_flat m0 l -> interp_flat m0 r
  | L.emp      => is_increasing m
  | L.sep l r  => ∃ m1 m2 : M, m1 ∗ m2 = m ∧ interp_flat m1 l ∧ interp_flat m2 r
  | L.wand l r => ∀ m1 m2 : M, m ∗ m1 = m2 -> interp_flat m1 l -> interp_flat m2 r

/--
Upwards semantics: both sep is weak and wand is strong
-/
@[simp]
def Kripke.interp_upwards [Kripke.Structure M] [Kripke.Model M B] [SepC M] (m : M) (e : L B) : Prop :=
  match e with
  | L.base b   => Kripke.AtomicInterp.ainterp m b
  | L.bot      => False
  | L.and l r  => interp_upwards m l ∧ interp_upwards m r
  | L.or l r   => interp_upwards m l ∨ interp_upwards m r
  | L.imp l r  => ∀ m0, m << m0 -> interp_upwards m0 l -> interp_upwards m0 r
  | L.emp      => is_increasing m
  | L.sep l r  => ∃ m1 m2 : M, m1 ∗ m2 = m ∧ interp_upwards m1 l ∧ interp_upwards m2 r
  | L.wand l r => ∀ m0 m1 m2 : M, m << m0 -> m0 ∗ m1 = m2 -> interp_upwards m1 l -> interp_upwards m2 r

/--
Downwards semantics: sep is strong and wand is weak
-/
@[simp]
def Kripke.interp_downwards [Kripke.Structure M] [Kripke.Model M B] [SepC M] (m : M) (e : L B) :  Prop :=
  match e with
  | L.base b   => Kripke.AtomicInterp.ainterp m b
  | L.bot      => False
  | L.and l r  => interp_downwards m l ∧ interp_downwards m r
  | L.or l r   => interp_downwards m l ∨ interp_downwards m r
  | L.imp l r  => ∀ m0, m << m0 -> interp_downwards m0 l -> interp_downwards m0 r
  | L.emp      => is_increasing m
  | L.sep l r  =>  ∃ m0 m1 m2 : M, m0 << m ∧ m1 ∗ m2 = m0 ∧ interp_downwards m1 l ∧ interp_downwards m2 r
  | L.wand l r => ∀ m1 m2 : M, m ∗ m1 = m2 -> interp_downwards m1 l -> interp_downwards m2 r


/-
Instances of the general interfaces for flat, upwards, and downwards semantics
-/

instance flat_semantics [Kripke.Structure M] [Kripke.Model M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_flat
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance flat_weak_wand [Kripke.Structure M] [Kripke.Model M B] [SepC M]  : Kripke.WeakWandSemantics M B flat_semantics where
  interp_wand := by simp [Kripke.Semantics.interp]

instance flat_weak_sep [Kripke.Structure M] [Kripke.Model M B] [SepC M]  : Kripke.WeakSepSemantics M B flat_semantics where
  interp_sep := by simp [Kripke.Semantics.interp]

instance upwards_semantics [Kripke.Structure M] [Kripke.Model M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_upwards
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance upwards_strong_wand [Kripke.Structure M] [Kripke.Model M B] [SepC M]  : Kripke.StrongWandSemantics M B upwards_semantics where
  interp_wand := by simp [Kripke.Semantics.interp]

instance upwards_weak_sep [Kripke.Structure M] [Kripke.Model M B] [SepC M]  : Kripke.WeakSepSemantics M B upwards_semantics where
  interp_sep := by simp [Kripke.Semantics.interp]

instance downwards_semantics [Kripke.Structure M] [Kripke.Model M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_downwards
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance downwards_weak_wand [Kripke.Structure M] [Kripke.Model M B] [SepC M]  : Kripke.WeakWandSemantics M B downwards_semantics where
  interp_wand := by simp [Kripke.Semantics.interp]

instance downwards_strong_sep [Kripke.Structure M] [Kripke.Model M B] [SepC M]  : Kripke.StrongSepSemantics M B downwards_semantics where
  interp_sep := by simp [Kripke.Semantics.interp]

/--
Monotonic denotations
-/
def Kripke.monotonic_denotation [Kripke.Ord M] (S : Kripke.Semantics M B) (e : L B) : Prop :=
  ∀ m n : M, n << m -> S.interp n e -> S.interp m e

class UCSA (M : Type) [Kripke.Ord M] [SepC M] where
  ucsa : ∀ m1 m2 m n, m1 ∗ m2 = m -> m << n -> ∃ (n1 n2 : M), n1 ∗ n2 = n ∧ m1 << n1 ∧ m2 << n2

class DCSA (M : Type) [Kripke.Ord M] [SepC M] where
  dcsa : ∀ m1 m2 m n1 n2, m1 ∗ m2 = m -> n1 << m1 -> n2 << m2 -> ∃(n : M), n1 ∗ n2 = n ∧ n << m

theorem weak_sep_monotonicity [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.WeakSepSemantics M B S] [UCSA M] :
    Kripke.monotonic_denotation S e1 ->
    Kripke.monotonic_denotation S e2 ->
    Kripke.monotonic_denotation S (L.sep e1 e2) := by
  unfold Kripke.monotonic_denotation
  simp [W.interp_sep]
  intro M1 M2 m n Hnm m1 m2 Hm1m2 He1 He2
  rcases (@UCSA.ucsa _ _ _ _ m1 m2 n m Hm1m2 Hnm) with ⟨ n1, n2, H1, H2, H3 ⟩
  exists n1
  exists n2
  apply And.intro
  · exact H1
  apply And.intro
  · exact M1 n1 m1 H2 He1
  · exact M2 n2 m2 H3 He2

theorem weak_wand_monotonicity [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.WeakWandSemantics M B S] [DCSA M] :
    -- Kripke.monotonic_denotation S e1 ->
    Kripke.monotonic_denotation S e2 ->
    Kripke.monotonic_denotation S (L.wand e1 e2) := by
  unfold Kripke.monotonic_denotation
  simp [W.interp_wand]
  intro H2 m n Hmn H m1 He1
  have Hm1 : m1 << m1 := by apply Kripke.Structure.kle_refl
  rcases (@DCSA.dcsa _ _ _ _ m m1 (m ∗ m1) n m1 (by rfl) Hmn Hm1) with ⟨ n', Hn', Hn'mm1 ⟩
  apply (H2 (m ∗ m1) n' Hn'mm1)
  rw [<- Hn']
  apply H
  apply He1

theorem strong_sep_monotonicity [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.StrongSepSemantics M B S] :
    -- Kripke.monotonic_denotation S e1 ->
    -- Kripke.monotonic_denotation S e2 ->
    Kripke.monotonic_denotation S (L.sep e1 e2) := by
  intro m n Hmn
  simp [W.interp_sep]
  intro x Hx x1 x2 Hx1x2 Hi1 Hi2
  exists x
  apply And.intro
  · exact Kripke.Structure.kle_trans x n m Hx Hmn
  exists x1
  exists x2

theorem strong_wand_monotonicity [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.StrongWandSemantics M B S] :
    -- Kripke.monotonic_denotation S e1 ->
    -- Kripke.monotonic_denotation S e2 ->
    Kripke.monotonic_denotation S (L.wand e1 e2) := by
  intro m n Hmn
  simp [W.interp_wand]
  intro H m0 m1 Hm0m1 Hi1
  apply H
  · exact Kripke.Structure.kle_trans n m m0 Hmn Hm0m1
  apply Hi1
