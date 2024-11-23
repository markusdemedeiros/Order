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

class SA (M : Type) [SepC M] where
  sepC_assoc : ∀ m0 m1 m2 : M, (m0 ∗ m1) ∗ m2 = m0 ∗ (m1 ∗ m2)
  sepC_comm : ∀ m0 m1 : M, m0 ∗ m1 = m1 ∗ m0


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

class Kripke.Model (M B : Type) [Kripke.Structure M] [I : Kripke.AtomicInterp M B] where
  kle_ainterp_mono : ∀ m n σ, m << n -> I.ainterp m σ -> I.ainterp n σ

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

-- Interface for Kripke semantics with emp
class Kripke.EmpSemantics  (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) where
  interp_emp  : S.interp m L.emp = is_increasing m

/-
Instances of Kripke semantics
-/

/--
Flat semantics: both sep and wand are weak
-/
@[simp]
def Kripke.interp_flat [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] (m : M) (e : L B) :  Prop :=
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
def Kripke.interp_upwards [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] (m : M) (e : L B) : Prop :=
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
def Kripke.interp_downwards [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] (m : M) (e : L B) :  Prop :=
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

instance flat_semantics [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_flat
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance flat_weak_wand [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M]  : Kripke.WeakWandSemantics M B flat_semantics where
  interp_wand := by simp [Kripke.Semantics.interp]

instance flat_weak_sep [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M]  : Kripke.WeakSepSemantics M B flat_semantics where
  interp_sep := by simp [Kripke.Semantics.interp]

instance upwards_semantics [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_upwards
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance upwards_strong_wand [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M]  : Kripke.StrongWandSemantics M B upwards_semantics where
  interp_wand := by simp [Kripke.Semantics.interp]

instance upwards_weak_sep [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M]  : Kripke.WeakSepSemantics M B upwards_semantics where
  interp_sep := by simp [Kripke.Semantics.interp]

instance downwards_semantics [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] : Kripke.Semantics M B where
  interp := Kripke.interp_downwards
  interp_base := by simp
  interp_bot  := by simp
  interp_and  := by simp
  interp_or   := by simp
  interp_imp  := by simp

instance downwards_weak_wand [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] : Kripke.WeakWandSemantics M B downwards_semantics where
  interp_wand := by simp [Kripke.Semantics.interp]

instance downwards_strong_sep [Kripke.Structure M] [Kripke.AtomicInterp M B] [SepC M] : Kripke.StrongSepSemantics M B downwards_semantics where
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

theorem Mono.weak_sep [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.WeakSepSemantics M B S] [UCSA M] :
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

theorem Mono.weak_wand [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.WeakWandSemantics M B S] [DCSA M] :
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

theorem Mono.strong_sep [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.StrongSepSemantics M B S] :
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

theorem Mono.strong_wand [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [W : Kripke.StrongWandSemantics M B S] :
    -- Kripke.monotonic_denotation S e1 ->
    -- Kripke.monotonic_denotation S e2 ->
    Kripke.monotonic_denotation S (L.wand e1 e2) := by
  intro m n Hmn
  simp [W.interp_wand]
  intro H m0 m1 Hm0m1 Hi1
  apply H
  · exact Kripke.Structure.kle_trans n m m0 Hmn Hm0m1
  apply Hi1

theorem Mono.base [Kripke.Structure M] (S : Kripke.Semantics M B) [Mod : Kripke.Model M B] :
    Kripke.monotonic_denotation S (L.base b) := by
  unfold Kripke.monotonic_denotation
  intro m n Hnm
  simp [Kripke.Semantics.interp_base]
  intro H1
  apply Mod.kle_ainterp_mono
  · apply Hnm
  · apply H1

theorem Mono.bot [Kripke.Structure M] (S : Kripke.Semantics M B) :
    Kripke.monotonic_denotation S L.bot := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.Semantics.interp_bot]

theorem Mono.and [Kripke.Structure M] (S : Kripke.Semantics M B) :
    Kripke.monotonic_denotation S φ ->
    Kripke.monotonic_denotation S ψ ->
    Kripke.monotonic_denotation S (L.and φ ψ) := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.Semantics.interp_and]
  intro Hm1 Hm2 m n Hnm Hφ Hψ
  apply And.intro
  · apply (Hm1 _ _ Hnm)
    trivial
  · apply (Hm2 _ _ Hnm)
    trivial

theorem Mono.or [Kripke.Structure M] (S : Kripke.Semantics M B) :
    Kripke.monotonic_denotation S φ ->
    Kripke.monotonic_denotation S ψ ->
    Kripke.monotonic_denotation S (L.or φ ψ) := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.Semantics.interp_or]
  intro Hm1 Hm2 m n Hnm H
  cases H
  · left
    apply (Hm1 _ _ Hnm)
    trivial
  · right
    apply (Hm2 _ _ Hnm)
    trivial

theorem Mono.imp [Kripke.Structure M] (S : Kripke.Semantics M B) :
    Kripke.monotonic_denotation S (L.imp φ ψ) := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.Semantics.interp_imp]
  intro m n Hmn H m1 Hm1 H2
  apply H
  · exact Kripke.Structure.kle_trans n m m1 Hmn Hm1
  trivial

theorem Mono.emp_dcsa [Kripke.Structure M] [SepC M] (S : Kripke.Semantics M B) [Kripke.EmpSemantics M B S] [DCSA M] :
    Kripke.monotonic_denotation S L.emp := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.EmpSemantics.interp_emp]
  intro m n Hnm
  simp [is_increasing]
  intro h1 m2
  rcases (DCSA.dcsa m m2 (m ∗ m2) n m2 (by rfl) Hnm (Kripke.Structure.kle_refl m2)) with ⟨ n', Hn', H'n' ⟩
  apply Kripke.Structure.kle_trans _ _ _ _ H'n'
  rw [<- Hn']
  apply h1

-- TODO: Lemma 1: make conversion instances for StrongWand and WeakWand in a UCSA, resp. DCSA

-- TODO: In upwards and downwards closed model, all programs in the flat semantics have monotonic denotation

-- TODO: Semantic equivalence lemmas

/-
Residue and unitality
-/

/--
m is a residue of m
-/
def residue [Kripke.Ord M] [SepC M] (m n : M) : Prop :=
  ∃ n', m ∗ n' = n ∧ n << n'

/--
All elements have an increasing residue
-/
class Unital (M : Type) [Kripke.Ord M] [SepC M] where
  unital : ∀ m, ∃ unit : M, residue unit m ∧ is_increasing unit

/-
Soundness of IP rules against in a model that is upwards closed, downwards closed, and unital
-/

class SoundIPModel (M : Type) [Kripke.Ord M] where
  inst_sepC : SepC M
  inst_SA : SA M
  inst_ucsa : UCSA M
  inst_dcsa : DCSA M
  inst_unital : Unital M

instance SoundIPModel_SepC [Kripke.Ord M] [I : SoundIPModel M] : SepC M := by cases I; trivial

instance SoundIPModel_DCSA [Kripke.Ord M] [I : SoundIPModel M] : DCSA M := by cases I; trivial

instance SoundIPModel_UCSA [Kripke.Ord M] [I : SoundIPModel M] : UCSA M := by cases I; trivial

instance SoundIPModel_SA [Kripke.Ord M] [I : SoundIPModel M] : SA M := by cases I; trivial

instance SoundIPModel_Unital [Kripke.Ord M] [I : SoundIPModel M] : Unital M := by cases I; trivial



class StongSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) where
   inst_EmpSemantics : Kripke.EmpSemantics M B S
   inst_WeakWandSemantics : Kripke.StrongWandSemantics M B S
   inst_WeakSepSemantics : Kripke.StrongSepSemantics M B S

instance StongSemantics_EmpSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) [I : StongSemantics M B S] :
    Kripke.EmpSemantics M B S := by
  cases I; trivial

instance StongSemantics_WeakWandSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) [I : StongSemantics M B S] :
    Kripke.StrongWandSemantics M B S := by
  cases I; trivial

instance StongSemantics_WeakSepSemantics (M B : Type) [Kripke.Ord M] [SepC M] (S : Kripke.Semantics M B) [I : StongSemantics M B S] :
    Kripke.StrongSepSemantics M B S := by
  cases I; trivial

/--
Monotonicity for the weak semantics
-/
theorem SoundIPModel.mono (M B : Type) [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B]
        [SoundIPModel M] [StongSemantics M B S] :
    ∀ e, Kripke.monotonic_denotation S e := by
  intro e
  induction e
  · apply Mono.base
  · apply Mono.bot
  · apply Mono.and <;> trivial
  · apply Mono.or <;> trivial
  · apply Mono.imp
  · apply Mono.emp_dcsa
  · apply Mono.strong_sep <;> trivial
  · apply Mono.strong_wand <;> trivial

theorem Soundness.imp1 (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp φ <| imp ψ φ := by
  intro m
  rw [Kripke.Semantics.interp_imp]
  intro m0 _ Hφ
  rw [Kripke.Semantics.interp_imp]
  intro m1 Hm1 _
  apply SoundIPModel.mono
  · apply Hm1
  apply Hφ

theorem Soundness.imp2 (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp (imp φ (imp ψ χ)) <| imp (imp φ ψ) <| imp φ χ := by
  intro m
  simp [Kripke.Semantics.interp_imp]
  intro m1 _ H m2 Hm2 H3 m4 Hm4 Hm4φ
  apply (H _ ?G1 Hm4φ m4 ?G2)
  case G1 => exact Kripke.Structure.kle_trans m1 m2 m4 Hm2 Hm4
  case G2 => exact Kripke.Structure.kle_refl m4
  apply (H3 _ Hm4 Hm4φ)

theorem Soundness.andI (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp φ <| imp ψ (and φ ψ) := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_and]
  intro m0 m1 _ Hφ m3 Hm1m3 Hψ
  apply And.intro
  · apply SoundIPModel.mono _ _ _ _ _ _ Hm1m3
    trivial
  · trivial

theorem Soundness.andE1 (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp (and φ ψ) φ := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_and]
  intros
  trivial

theorem Soundness.andE2 (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp (and φ ψ) ψ := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_and]

theorem Soundness.orI1 (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp φ (or φ ψ) := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_or]
  intros
  left
  trivial

theorem Soundness.orI2 (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp ψ (or φ ψ) := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_or]
  intros
  right
  trivial

theorem Soundness.orE (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp (imp φ χ) <| imp (imp ψ χ) <| imp (or φ ψ) χ := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_or]
  intro m0 m1 _ H1 m2 m1m2 H2 m3 m2m3 H3
  cases H3
  · apply H1
    · exact Kripke.Structure.kle_trans m1 m2 m3 m1m2 m2m3
    · trivial
  · apply H2
    · exact m2m3
    · trivial

theorem Soundness.botE (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp bot φ := by
  simp [Kripke.Semantics.interp_imp, Kripke.Semantics.interp_bot]

-- In this one, should m be the same in each? Or should it increase?
theorem Soundness.mp (R : L B -> Prop) [IP R] {φ ψ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m φ -> S.interp m (imp φ ψ) -> S.interp m ψ := by
  simp [Kripke.Semantics.interp_imp]
  intro m Hφ H
  apply H
  · exact Kripke.Structure.kle_refl m
  · trivial

/-
Soundness for the SL axioms
-/


theorem Soundness.scomm (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp (sep φ ψ) (sep ψ φ) := by
  simp [Kripke.Semantics.interp_imp]
  intro m0 m1 m0m1
  simp [Kripke.StrongSepSemantics.interp_sep]
  intro m2 m2m1 m3 m4 m3m4m2 Hφ Hψ
  sorry

theorem Soundness.sA1 (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, (S.interp m <| imp (sep φ ψ) χ) -> (S.interp m <| imp φ (wand ψ χ)) := by
  sorry

theorem Soundness.sA2 (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, (S.interp m <| imp φ (wand ψ χ)) -> (S.interp m <| imp (sep φ ψ) χ) := by
  sorry


theorem Soundness.semp (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] [SA M] :
    ∀ m : M, S.interp m <| iff (sep φ emp) φ := by
  unfold L.iff
  simp [Kripke.Semantics.interp_and, Kripke.Semantics.interp_imp, Kripke.StrongSepSemantics.interp_sep, Kripke.EmpSemantics.interp_emp]
  intro m0
  apply And.intro
  · intro m1 _ m2 m2m1 m3 m4 m342 Hφ Hm4
    unfold is_increasing at Hm4
    apply SoundIPModel.mono _ _ _ _ _ m3 ?G2 ?G3
    case G2 =>
      apply Kripke.Structure.kle_trans
      · apply Hm4
        rw [SA.sepC_comm]
      · rw [m342]
        apply m2m1
    case G3 => apply Hφ
  · intro m1 _ Hφ
    exists m1
    apply And.intro
    · apply Kripke.Structure.kle_refl m1
    rcases (Unital.unital m1) with ⟨ m1u, ⟨ m1r, Em1, Hm1r ⟩, Hu ⟩
    exists m1r
    exists m1u
    apply And.intro
    · rw [<- SA.sepC_comm]
      trivial
    apply And.intro
    · apply SoundIPModel.mono _ _ _ _ _ m1 ?G2 ?G3
      case G2 => trivial
      case G3 => trivial
    · trivial

theorem Soundness.sassoc (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, S.interp m <| imp (sep (sep φ ψ) χ) <| (sep φ (sep ψ χ)) := by
  simp [Kripke.Semantics.interp_imp, Kripke.StrongSepSemantics.interp_sep]
  intros m0 m1 m0m1 m2 m2m1 m3 m4 m342 m5 m5m3 m6 m7 m675 Hφ Hψ Hχ
  exists m2
  apply And.intro
  · trivial
  exists m3
  exists m4
  apply And.intro
  · trivial
  apply And.intro
  · apply SoundIPModel.mono
    · -- Need m6 << m3?
      sorry
    · apply Hφ
  sorry

theorem Soundness.smono (R : L B -> Prop) [IP R] {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [StongSemantics M B S] :
    ∀ m : M, (S.interp m <| imp φ1 ψ1) -> (S.interp m <| imp φ2 ψ2) -> (S.interp m <| imp (sep φ1 φ2) (sep ψ1 ψ2)) := by
  sorry


/-
Soundness for the extensions
-/
