import Order.Lib

/-
# Separation Logic
-/

/-
## Syntax
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

open L






/-
## Separation Algebras
-/

/-- A type equipped with separating conjunction -/
class SepC (M : Type) where
  sepC : M -> M -> M

infixl:65 " ∗ " => SepC.sepC

/-- A sepration algebra over M -/
class SeparationAlgebra (M : Type) [S : SepC M] extends (Std.Associative S.sepC), (Std.Commutative S.sepC)



/-
## Kripke Models
-/

/-- Validity of base propositions B in a sepration algebra M -/
class Kripke.AtomicInterp (M B : Type) where
  ainterp : M -> B -> Prop

/-- A type equipped with an order -/
class Kripke.Ord (M : Type) where
  kle : M -> M -> Prop
infixl:65 " << " => Kripke.Ord.kle

/-- An element is increasing -/
def Kripke.is_increasing [Ord M] [SepC M] (e : M) : Prop :=
  ∀ m n : M, e ∗ m = n -> m << n

/-- A type equipped with a reflexive, transitive order -/
class Kripke.Structure (M : Type) [O : Ord M] extends (Reflexive O.kle), (Transitive O.kle)

/-- A Kripke model is a Kripke structure where atomic propositions have monotnic denotation -/
class Kripke.Model (M B : Type) [Ord M] [Structure M] extends AtomicInterp M B where
  kle_ainterp_mono : ∀ m n σ, m << n -> ainterp m σ -> ainterp n σ






/-
## Kripke Semantics
-/

/--
A type has a Kripke semantics (an interpretation for (L B) terms under a world m)
-/
class Kripke.Semantics (M B : Type) [Ord M] [Structure M] extends Model M B where
  interp : M -> L B -> Prop

/-- A Kripke semantics obeys the base interpretation -/
class Kripke.BaseSemantics (M B : Type) [Ord M] [Structure M] (S : Semantics M B) where
  interp_base : S.interp m (L.base b) = S.ainterp m b
  interp_bot  : S.interp m L.bot = False
  interp_and  : S.interp m (L.and l r) = (S.interp m l ∧ S.interp m r)
  interp_or   : S.interp m (L.or l r) = (S.interp m l ∨ S.interp m r)
  interp_imp  : S.interp m (L.imp l r) = ∀ m0, m << m0 -> S.interp m0 l -> S.interp m0 r

/-- A Kripke semantics obeys the strong wand interpretation -/
class Kripke.StrongWandSemantics (M B : Type) [Ord M] [SepC M] [Structure M] (S : Semantics M B) where
  interp_wand : S.interp m (L.wand l r) = ∀ m0 m1 m2 : M, m << m0 -> m0 ∗ m1 = m2 -> S.interp m1 l -> S.interp m2 r

/-- A Kripke semantics obeys the strong separating conjunction interpretation -/
class Kripke.StrongSepSemantics (M B : Type) [Ord M] [SepC M] [Structure M] (S : Semantics M B) where
  interp_sep : S.interp m (L.sep l r) = ∃ m0 m1 m2 : M, m0 << m ∧ m1 ∗ m2 = m0 ∧ S.interp m1 l ∧ S.interp m2 r

/-- A Kripke semantics obeys the strong weak wand interpretation -/
class Kripke.WeakWandSemantics (M B : Type) [Ord M] [SepC M] [Structure M] (S : Semantics M B) where
  interp_wand : S.interp m (L.wand l r) = ∀ m1 m2 : M, m ∗ m1 = m2 -> S.interp m1 l -> S.interp m2 r

/-- A Kripke semantics obeys the strong weak separating conjunction interpretation -/
class Kripke.WeakSepSemantics (M B : Type) [Ord M] [SepC M] [Structure M] (S : Semantics M B) where
  interp_sep : S.interp m (L.sep l r) = ∃ m1 m2 : M, m1 ∗ m2 = m ∧ S.interp m1 l ∧ S.interp m2 r

/-- A Kripke semantics obeys the interpretation of emp -/
class Kripke.EmpSemantics (M B : Type) [Ord M] [SepC M] [Structure M] (S : Semantics M B) where
  interp_emp  : S.interp m L.emp = is_increasing m

/--
A Flat Kripke semantics has weak wand and weak sep
-/
class Kripke.FlatSemantics (M B : Type) [Ord M] [SepC M] [Structure M] (S : Semantics M B) extends
  BaseSemantics M B S,
  WeakWandSemantics M B S,
  WeakSepSemantics M B S,
  EmpSemantics M B S



/-
## Variants of separation algebras
-/


/-- A separation algebra is upwards closed -/
class UCSA (M : Type) [Kripke.Ord M] [SepC M] where
  ucsa : ∀ {m1 m2 m n}, m1 ∗ m2 = m -> m << n -> ∃ (n1 n2 : M), n1 ∗ n2 = n ∧ m1 << n1 ∧ m2 << n2

/-- A separation algebra is downwards closed -/
class DCSA (M : Type) [Kripke.Ord M] [SepC M] where
  dcsa : ∀ {m1 m2 m n1 n2}, m1 ∗ m2 = m -> n1 << m1 -> n2 << m2 -> ∃(n : M), n1 ∗ n2 = n ∧ n << m


/-- m is a residue of n -/
def residue [Kripke.Ord M] [SepC M] (m n : M) : Prop :=
  ∃ n', m ∗ n' = n ∧ n << n'

/-- All elements have an increasing residue -/
class Unital (M : Type) [Kripke.Ord M] [SepC M] where
  unital : ∀ m, ∃ unit : M, residue unit m ∧ Kripke.is_increasing unit


/-- Variant of separation algebra where the base soundness proof applies -/
class BaseAlgebra (M : Type) [Kripke.Ord M] [SepC M] extends
  SeparationAlgebra M,
  UCSA M,
  DCSA M,
  Unital M







/-
## Monotonicity
-/

/-- A term has monotonic denotation inside a Kripke semantics -/
def Kripke.monotonic_denotation {M B : Type} [Ord M] [SepC M] [Structure M] (S : Kripke.Semantics M B) (e : L B) : Prop :=
  ∀ {m n : M}, n << m -> S.interp n e -> S.interp m e


section Mono

variable {M : Type}
variable [Kripke.Ord M] [SepC M] [Kripke.Structure M]
variable (S : Kripke.Semantics M B)

/-- Weak conjunction preserves monotonic denotation in a UCSA -/
theorem Mono.weak_sep [W : Kripke.WeakSepSemantics M B S] [UCSA M] :
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
  · apply M1 H2 He1
  · apply M2 H3 He2

/--
Weak wand preserves monotonic denotation in a DCSA

The left argument does not need to have monotonic denotation.
-/
theorem Mono.weak_wand [W : Kripke.WeakWandSemantics M B S] [DCSA M] :
    Kripke.monotonic_denotation S e2 ->
    Kripke.monotonic_denotation S (L.wand e1 e2) := by
  unfold Kripke.monotonic_denotation
  simp [W.interp_wand]
  intro H2 m n Hmn H m1 He1
  have Hm1 : m1 << m1 := by apply Reflexive.refl
  rcases (@DCSA.dcsa _ _ _ _ m m1 (m ∗ m1) n m1 (by rfl) Hmn Hm1) with ⟨ n', Hn', Hn'mm1 ⟩
  apply (H2 Hn'mm1)
  rw [<- Hn']
  apply H
  apply He1


/-- Strong conjunction has monotonic denotation -/
theorem Mono.strong_sep [W : Kripke.StrongSepSemantics M B S] :
    Kripke.monotonic_denotation S (L.sep e1 e2) := by
  intro m n Hmn
  simp [W.interp_sep]
  intro x Hx x1 x2 Hx1x2 Hi1 Hi2
  exists x
  apply And.intro
  · apply Transitive.trans Hx Hmn
  exists x1
  exists x2


/-- Strong wand has monotonic denotation -/
theorem Mono.strong_wand [W : Kripke.StrongWandSemantics M B S] :
    Kripke.monotonic_denotation S (L.wand e1 e2) := by
  intro m n Hmn
  simp [W.interp_wand]
  intro H m0 m1 Hm0m1 Hi1
  apply H
  · apply Transitive.trans Hmn Hm0m1
  apply Hi1

/-- Base semantics have monotonic denoatation -/
theorem Mono.base [Kripke.BaseSemantics M B S] :
    Kripke.monotonic_denotation S (L.base b) := by
  unfold Kripke.monotonic_denotation
  intro m n Hnm
  simp [Kripke.BaseSemantics.interp_base]
  intro H1
  apply S.kle_ainterp_mono
  · apply Hnm
  · apply H1



/-- bot has monotonic denotation -/
theorem Mono.bot [Kripke.BaseSemantics M B S] :
    Kripke.monotonic_denotation S L.bot := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.BaseSemantics.interp_bot]



/-- and preserves monotonic denotation -/
theorem Mono.and [Kripke.BaseSemantics M B S] :
    Kripke.monotonic_denotation S φ ->
    Kripke.monotonic_denotation S ψ ->
    Kripke.monotonic_denotation S (L.and φ ψ) := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.BaseSemantics.interp_and]
  intros Hm1 Hm2 ; intros
  apply And.intro
  · apply Hm1 <;> trivial
  · apply Hm2 <;> trivial


/-- or preserves monotonic denotation -/
theorem Mono.or [Kripke.BaseSemantics M B S] :
    Kripke.monotonic_denotation S φ ->
    Kripke.monotonic_denotation S ψ ->
    Kripke.monotonic_denotation S (L.or φ ψ) := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.BaseSemantics.interp_or]
  intro Hm1 Hm2 _ _ _ H
  cases H
  · left
    apply Hm1 <;> trivial
  · right
    apply Hm2  <;> trivial

/-- imp preserves monotonic denotation -/
theorem Mono.imp  [Kripke.BaseSemantics M B S] :
    Kripke.monotonic_denotation S (L.imp φ ψ) := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.BaseSemantics.interp_imp ]
  intro m n Hmn H m1 Hm1 H2
  apply H
  · apply Transitive.trans Hmn Hm1
  trivial


/-- emp has monotonic denotation in any downwards-closed semantics -/
theorem Mono.emp_dcsa [Kripke.EmpSemantics M B S] [DCSA M] :
    Kripke.monotonic_denotation S L.emp := by
  unfold Kripke.monotonic_denotation
  simp [Kripke.EmpSemantics.interp_emp]
  intro m n Hnm
  simp [Kripke.is_increasing]
  intro h1 m2
  rcases (DCSA.dcsa (by rfl) Hnm Reflexive.refl) with ⟨ n', Hn', H'n' ⟩
  apply Transitive.trans _ H'n'
  rw [<- Hn']
  apply h1


/--
Monotonicity of the flat semantics in a base model (Base algebra with flat semantics )
-/
theorem BaseModel.mono [BaseAlgebra M] [Kripke.FlatSemantics M B S] :
    ∀ {e}, Kripke.monotonic_denotation S e := by
  intro e
  induction e
  · apply Mono.base
  · apply Mono.bot
  · apply Mono.and <;> trivial
  · apply Mono.or <;> trivial
  · apply Mono.imp
  · apply Mono.emp_dcsa
  · apply Mono.weak_sep <;> trivial
  · apply Mono.weak_wand <;> trivial

end Mono





/-
## Soudness for the base model
-/

section soundness

variable {M B : Type}
variable [Kripke.Ord M] [Kripke.Structure M] [SepC M]
variable (S : Kripke.Semantics M B)
variable [BaseAlgebra M]
variable [Kripke.FlatSemantics M B S]

theorem Soundness.imp1 {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp φ <| imp ψ φ := by
  intro m
  rw [Kripke.BaseSemantics.interp_imp]
  intro m0 _ Hφ
  rw [Kripke.BaseSemantics.interp_imp]
  intro m1 Hm1 _
  apply BaseModel.mono
  · apply Hm1
  apply Hφ

omit [BaseAlgebra M] in
theorem Soundness.imp2 {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp (imp φ (imp ψ χ)) <| imp (imp φ ψ) <| imp φ χ := by
  intro m
  simp [Kripke.BaseSemantics.interp_imp]
  intro m1 _ H m2 Hm2 H3 m4 Hm4 Hm4φ
  apply (H _ ?G1 Hm4φ m4 ?G2)
  case G1 => apply Transitive.trans Hm2 Hm4
  case G2 => apply Reflexive.refl
  apply (H3 _ Hm4 Hm4φ)

theorem Soundness.andI {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp φ <| imp ψ (and φ ψ) := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_and]
  intro m0 m1 _ Hφ m3 Hm1m3 Hψ
  apply And.intro
  · apply BaseModel.mono _ Hm1m3
    trivial
  · trivial

omit [BaseAlgebra M] in
theorem Soundness.andE1 {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp (and φ ψ) φ := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_and]
  intros
  trivial

omit [BaseAlgebra M] in
theorem Soundness.andE2 {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp (and φ ψ) ψ := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_and]

omit [BaseAlgebra M] in
theorem Soundness.orI1 {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp φ (or φ ψ) := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_or]
  intros
  left
  trivial

omit [BaseAlgebra M] in
theorem Soundness.orI2 {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp ψ (or φ ψ) := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_or]
  intros
  right
  trivial

omit [BaseAlgebra M] in
theorem Soundness.orE {φ ψ : L B} :
    ∀ m : M, S.interp m <| imp (imp φ χ) <| imp (imp ψ χ) <| imp (or φ ψ) χ := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_or]
  intro m0 m1 _ H1 m2 m1m2 H2 m3 m2m3 H3
  cases H3
  · apply H1
    · exact Transitive.trans m1m2 m2m3
    · trivial
  · apply H2
    · exact m2m3
    · trivial

omit [BaseAlgebra M] in
theorem Soundness.botE {φ : L B} :
    ∀ m : M, S.interp m <| imp bot φ := by
  simp [Kripke.BaseSemantics.interp_imp, Kripke.BaseSemantics.interp_bot]

omit [BaseAlgebra M] in
theorem Soundness.mp {φ ψ : L B} :
    ∀ m : M, S.interp m φ -> S.interp m (imp φ ψ) -> S.interp m ψ := by
  simp [Kripke.BaseSemantics.interp_imp]
  intro m Hφ H
  apply H
  · apply Reflexive.refl
  · trivial

theorem Soundness.scomm {φ : L B} :
    ∀ m : M, S.interp m <| imp (sep φ ψ) (sep ψ φ) := by
  simp [Kripke.BaseSemantics.interp_imp]
  intro m0 m1 _
  simp [Kripke.WeakSepSemantics.interp_sep]
  intro m2 m3 m2m3 Hφ Hψ
  exists m3
  exists m2
  apply And.intro
  ·
    sorry
    -- rw [SeparationAlgebra.sepC_comm]
    -- trivial
  apply And.intro
  · trivial
  · trivial

/-
theorem Soundness.sA1 {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [FlatSemantics M B S] [SeparationAlgebra M] :
    (∀ m : M, (S.interp m <| imp (sep φ ψ) χ)) -> (∀ m : M, (S.interp m <| imp φ (wand ψ χ))) := by
  simp [Kripke.Semantics.interp_imp, Kripke.WeakSepSemantics.interp_sep, Kripke.WeakWandSemantics.interp_wand]
  intro H m1 m2 _ Hφ m3 Hψ
  apply H (m2 ∗ m3) (m2 ∗ m3) (Kripke.Structure.kle_refl (m2 ∗ m3)) m2 m3 (by rfl) Hφ Hψ

theorem Soundness.sA2 {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [FlatSemantics M B S] [SeparationAlgebra M] :
    (∀ m : M, (S.interp m <| imp φ (wand ψ χ))) -> (∀ m : M, S.interp m <| imp (sep φ ψ) χ) := by
  simp [Kripke.Semantics.interp_imp, Kripke.WeakSepSemantics.interp_sep, Kripke.WeakWandSemantics.interp_wand]
  intro H m1 m2 m0m1 m3 m4 m3m42 Hφ Hψ
  subst m3m42
  apply H m3 m3 (Kripke.Structure.kle_refl m3) Hφ m4 Hψ

theorem Soundness.semp {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [FlatSemantics M B S] [SeparationAlgebra M] :
    ∀ m : M, S.interp m <| iff (sep φ emp) φ := by
  unfold L.iff
  simp [Kripke.Semantics.interp_and, Kripke.Semantics.interp_imp, Kripke.WeakSepSemantics.interp_sep, Kripke.EmpSemantics.interp_emp]
  intro m0
  apply And.intro
  · intro m1 _ m2 m3 m231 Hφ HI
    apply SoundIPModel.mono _ _ _ _ _ m2 ?G2 ?G3
    · apply HI
      sorry
      -- rw [SA.sepC_comm]
      -- trivial
    · trivial
  · intro m1 _ Hφ
    rcases (Unital.unital m1) with ⟨ m1u, ⟨ m1r, Em1, Hm1r ⟩, Hu ⟩
    exists m1r
    exists m1u
    apply And.intro
    · sorry
      -- rw [SA.sepC_comm]
      -- trivial
    apply And.intro
    · apply SoundIPModel.mono _ _ _ _ _ m1 Hm1r Hφ
    · trivial

theorem Soundness.sassoc {φ : L B}
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [FlatSemantics M B S] [SeparationAlgebra M] :
    ∀ m : M, S.interp m <| imp (sep (sep φ ψ) χ) <| (sep φ (sep ψ χ)) := by
  simp [Kripke.Semantics.interp_imp, Kripke.WeakSepSemantics.interp_sep]
  intro m0 m1 m0m1 m2 m3 m231 m4 m5 m452
  subst m231
  subst m452
  intro Hφ Hψ Hχ
  exists m4
  exists (m5 ∗ m3)
  apply And.intro
  ·
    sorry
    -- apply Eq.symm (SA.sepC_assoc m4 m5 m3)
  apply And.intro
  · trivial
  exists m5
  exists m3

theorem Soundness.smono
    [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [FlatSemantics M B S] [SeparationAlgebra M] :
    (∀ m : M, (S.interp m <| imp φ1 ψ1)) -> (∀ m : M, S.interp m <| imp φ2 ψ2) -> (∀ m : M, S.interp m <| imp (sep φ1 φ2) (sep ψ1 ψ2)) := by
  simp [Kripke.Semantics.interp_imp, Kripke.WeakSepSemantics.interp_sep]
  intro H1 H2 m0 m1 m01 m2 m3 m231 Hp1 Hp2
  subst m231
  exists m2
  exists m3
  apply And.intro
  · rfl
  apply And.intro
  · apply H1 m2 m2 (Kripke.Structure.kle_refl m2) Hp1
  · apply H2 m3 m3 (Kripke.Structure.kle_refl m3) Hp2

-/
end soundness

/-
/-
Soundness for the extensions
-/



/-
Soundness for the basic IP+SL system (removed base props)
-/

inductive IPSL_deriv {B : Type} : L B -> Prop
| mp     : IPSL_deriv φ -> IPSL_deriv (imp φ ψ) -> IPSL_deriv ψ
| imp1   : IPSL_deriv <| imp φ <| imp ψ φ
| imp2   : IPSL_deriv <| imp (imp φ (imp ψ χ)) <| imp (imp φ ψ) <| imp φ χ
| andI   : IPSL_deriv <| imp φ <| imp ψ (and φ ψ)
| andE1  : IPSL_deriv <| imp (and φ ψ) φ
| andE2  : IPSL_deriv <| imp (and φ ψ) ψ
| orI1   : IPSL_deriv <| imp φ (or φ ψ)
| orI2   : IPSL_deriv <| imp ψ (or φ ψ)
| orE    : IPSL_deriv <| imp (imp φ χ) <| imp (imp ψ χ) <| imp (or φ ψ) χ
| botE   : IPSL_deriv <| imp bot φ
| scomm  : IPSL_deriv <| imp (sep φ ψ) (sep ψ φ)
| sA1    : IPSL_deriv (imp (sep φ ψ) χ) -> IPSL_deriv (imp φ (wand ψ χ))
| sA2    : IPSL_deriv (imp φ (wand ψ χ)) -> IPSL_deriv (imp (sep φ ψ) χ)
| semp   : IPSL_deriv (iff (sep φ emp) φ)
| sassoc : IPSL_deriv (imp (sep (sep φ ψ) χ) <| (sep φ (sep ψ χ)))
| smono  : IPSL_deriv (imp φ1 ψ1) -> IPSL_deriv (imp φ2 ψ2) -> IPSL_deriv (imp (sep φ1 φ2) (sep ψ1 ψ2))

/-
instance ISPL_deriv_IP_inst {B} : IP (@IPSL_deriv B) where
mp     := IPSL_deriv.mp
imp1   := IPSL_deriv.imp1
imp2   := IPSL_deriv.imp2
andI   := IPSL_deriv.andI
andE1  := IPSL_deriv.andE1
andE2  := IPSL_deriv.andE2
orI1   := IPSL_deriv.orI1
orI2   := IPSL_deriv.orI2
orE    := IPSL_deriv.orE
botE   := IPSL_deriv.botE

instance ISPL_deriv_SL_inst {B} : SL (@IPSL_deriv B) where
scomm  := IPSL_deriv.scomm
sA1    := IPSL_deriv.sA1
sA2    := IPSL_deriv.sA2
semp   := IPSL_deriv.semp
sassoc := IPSL_deriv.sassoc
smono  := IPSL_deriv.smono
-/


theorem IPSL_kripke_soundness {B : Type} [Kripke.Structure M] (S : Kripke.Semantics M B) [Kripke.Model M B] [SoundIPModel M] [FlatSemantics M B S] :
    ∀ φ : L B, IPSL_deriv φ -> ∀ m, S.interp m φ := by
  intro φ H
  induction H
  · rename_i _ _ _ _ IH1 IH2
    intro m
    apply Soundness.mp
    · apply IH1
    · apply IH2
  · apply Soundness.imp1
  · apply Soundness.imp2
  · apply Soundness.andI
  · apply Soundness.andE1
  · apply Soundness.andE2
  · apply Soundness.orI1
  · apply Soundness.orI2
  · apply Soundness.orE
  · apply Soundness.botE
  · apply Soundness.scomm
  · apply Soundness.sA1
    trivial
  · apply Soundness.sA2
    trivial
  · apply Soundness.semp
  · apply Soundness.sassoc
  · apply Soundness.smono
    · trivial
    · trivial





/-
section sound_model

-- Now if we can exhibit _some_ Kripke model with the above requirements, to prove the IPSL system is sound

instance discrete_order {T : Type} : Kripke.Ord T where
  kle := Eq

instance discrete_structure {T : Type} : Kripke.Structure T where
  kle_refl _ := by rfl
  kle_trans := by
    unfold Kripke.Ord.kle
    unfold discrete_order
    simp

instance discrete_triv_ainterp {T1 T2: Type} : Kripke.AtomicInterp T1 T2 where
  ainterp _ _ := True

instance sepC_unit : SepC Unit where
  sepC _ _ := PUnit.unit

-- #check
instance discrete_model {T : Type} : Kripke.Model T Unit  where
  kle_ainterp_mono _ _ _ H _ := by rw [<- H]; trivial



instance unit_SA : SeparationAlgebra Unit where
  sepC_assoc := by sorry
  sepC_comm  := by sorry


instance unit_UCSA : UCSA Unit where
  ucsa := by simp [Kripke.Ord.kle]

instance unit_DCSA : DCSA Unit where
  dcsa := by simp [Kripke.Ord.kle]

instance unit_Unital : Unital Unit where
  unital := by simp [residue, is_increasing, Kripke.Ord.kle]

instance unit_SoundIPModel : SoundIPModel Unit where
  inst_sepC := sepC_unit
  inst_SA := unit_SA
  inst_ucsa := unit_UCSA
  inst_dcsa := unit_DCSA
  inst_unital := unit_Unital


def UnitSemantics : Kripke.Semantics Unit Unit := (@flat_semantics Unit Unit _ _ _)

instance unit_empSemantics : Kripke.EmpSemantics Unit Unit UnitSemantics where
  interp_emp := by simp [Kripke.Semantics.interp, UnitSemantics, flat_semantics]

instance unit_weakWand : Kripke.WeakWandSemantics Unit Unit UnitSemantics where
  interp_wand := by simp [Kripke.Semantics.interp, UnitSemantics, flat_semantics]

instance unit_weakSep : Kripke.WeakSepSemantics Unit Unit UnitSemantics where
  interp_sep := by simp [Kripke.Semantics.interp, UnitSemantics, flat_semantics]

instance unit_flatSemantics : FlatSemantics Unit _ UnitSemantics where
  inst_EmpSemantics := unit_empSemantics
  inst_WeakWandSemantics := unit_weakWand
  inst_WeakSepSemantics := unit_weakSep

-- theorem IPSL_unit_soundness : @IPSL_deriv Unit bot -> False := by
--   intro K
--   have X := @IPSL_kripke_soundness Unit Unit _ UnitSemantics discrete_model unit_SoundIPModel _ bot K PUnit.unit
--   simp [Kripke.Semantics.interp, UnitSemantics, flat_semantics] at X

end sound_model
-/
-/
/-

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


-/

/-
-- TODO: Lemma 1: make conversion instances for StrongWand and WeakWand in a UCSA, resp. DCSA

-- TODO: In upwards and downwards closed model, all programs in the flat semantics have monotonic denotation

-- TODO: Semantic equivalence lemmas
-/
