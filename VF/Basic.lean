import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.TFAE

variable {α : Type*}

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | bot : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
deriving DecidableEq, Encodable

namespace Formula

prefix:100 "#" => atom
notation:90 "⊥" => bot
infixr:85 " 🡒 " => imp
infixl:84 " ⋏ " => and
infixl:83 " ⋎ " => or

@[match_pattern]
abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
prefix:90 "∼" => neg

@[match_pattern]
abbrev top : Formula α := ∼⊥
notation:91 "⊤" => top

@[match_pattern]
abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
infix:82 " 🡘 " => iff

@[simp, grind]
def lconj : List (Formula α) → Formula α
  | [] => ⊤
  | [A] => A
  | A :: X => A ⋏ (lconj X)
prefix:100 "⋀" => lconj

@[simp, grind]
def ldisj : List (Formula α) → Formula α
  | [] => ⊥
  | [A] => A
  | A :: X => A ⋎ (ldisj X)
prefix:100 "⋁" => ldisj

noncomputable def fconj (s : Finset (Formula α)) : Formula α := ⋀(s.toList)
prefix:100 "⋀" => fconj

@[simp, grind =_] lemma fconj_emptyset : (fconj (∅ : Finset (Formula α))) = ⊤ := by simp [fconj, lconj];
@[simp, grind =] lemma fconj_singleton {A : Formula α} : (fconj {A}) = A := by simp [fconj, lconj];

noncomputable def fdisj (s : Finset (Formula α)) : Formula α := ⋁(s.toList)
prefix:100 "⋁" => fdisj

@[simp, grind =_] lemma fdisj_emptyset : (fdisj (∅ : Finset (Formula α))) = ⊥ := by simp [fdisj, ldisj];
@[simp, grind =] lemma fdisj_singleton {A : Formula α} : (fdisj {A}) = A := by simp [fdisj, ldisj];

@[grind]
def Closed : Formula α → Prop
  | #_ => False
  | ⊥ => True
  | A ⋎ B
  | A ⋏ B
  | A 🡒 B => A.Closed ∧ B.Closed

end Formula


abbrev Axioms (α : Type*) := Finset (Formula α)

inductive Proof (Λ : Axioms α) : Formula α → Type _
| axm {A}                 : A ∈ Λ → Proof Λ A
| andElimL {A B}          : Proof Λ $ (A ⋏ B) 🡒 A
| andElimR {A B}          : Proof Λ $ (A ⋏ B) 🡒 B
| orIntroL {A B}          : Proof Λ $ A 🡒 (A ⋎ B)
| orIntroR {A B}          : Proof Λ $ B 🡒 (A ⋎ B)
| distributeAndOr {A B C} : Proof Λ $ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))
| impId {A}               : Proof Λ $ A 🡒 A
| efq {A}                 : Proof Λ $ ⊥ 🡒 A
| mdp {A B}               : Proof Λ (A 🡒 B) → Proof Λ A → Proof Λ B
| af {A B}                : Proof Λ A → Proof Λ (B 🡒 A)
| ruleC {A B C}           : Proof Λ (A 🡒 B) → Proof Λ (A 🡒 C) → Proof Λ (A 🡒 (B ⋏ C))
| ruleD {A B C}           : Proof Λ (A 🡒 C) → Proof Λ (B 🡒 C) → Proof Λ ((A ⋎ B) 🡒 C)
| ruleI {A B C}           : Proof Λ (A 🡒 B) → Proof Λ (B 🡒 C) → Proof Λ (A 🡒 C)

infix:25 " ⊢! " => Proof

namespace Proof

variable {Λ : Axioms α} {A B C : Formula α}

def andComm : Λ ⊢! (A ⋏ B) 🡒 (B ⋏ A) := ruleC andElimR andElimL
def orComm  : Λ ⊢! (A ⋎ B) 🡒 (B ⋎ A) := ruleD orIntroR orIntroL

def distributeOrAnd : Λ ⊢! ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := by
  letI D := A ⋎ (B ⋏ C);
  haveI P₁ : Λ ⊢! ((A ⋎ B) ⋏ A) 🡒 D := ruleI andElimR orIntroL
  haveI P₂ : Λ ⊢! ((A ⋎ B) ⋏ C) 🡒 ((C ⋏ A) ⋎ (C ⋏ B)) := ruleI andComm distributeAndOr
  haveI P₃ : Λ ⊢! (C ⋏ A) 🡒 D := ruleI andElimR orIntroL;
  haveI P₄ : Λ ⊢! (C ⋏ B) 🡒 D := ruleI andComm orIntroR;
  haveI P₅ : Λ ⊢! ((C ⋏ A) ⋎ (C ⋏ B)) 🡒 D := ruleD P₃ P₄;
  haveI P₆ : Λ ⊢! ((A ⋎ B) ⋏ C) 🡒 D := ruleI P₂ P₅;
  haveI P₇ : Λ ⊢! ((A ⋎ B) ⋏ A ⋎ (A ⋎ B) ⋏ C) 🡒 D := ruleD P₁ P₆;
  exact ruleI distributeAndOr P₇;

def verum : Λ ⊢! ⊤ := impId

def orIntroRuleL : Λ ⊢! A → Λ ⊢! (A ⋎ B) := λ h => mdp orIntroL h
def orIntroRuleR : Λ ⊢! B → Λ ⊢! (A ⋎ B) := λ h => mdp orIntroR h

def andIntro : Λ ⊢! A → Λ ⊢! B → Λ ⊢! A ⋏ B := λ h₁ h₂ => mdp (ruleC (af h₁) (af h₂)) (verum)

noncomputable def ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢! A → Λ₂ ⊢! A := λ h => by
  induction h with
  | axm h₁ => exact axm (hsub h₁)
  | andElimL => exact andElimL
  | andElimR => exact andElimR
  | orIntroL => exact orIntroL
  | orIntroR => exact orIntroR
  | distributeAndOr => exact distributeAndOr
  | impId => exact impId
  | efq => exact efq
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA
  | af _ ihA => exact af ihA
  | ruleC _ _ ihAB ihAC => exact ruleC ihAB ihAC
  | ruleD _ _ ihAC ihBC => exact ruleD ihAC ihBC
  | ruleI _ _ ihAB ihBC => exact ruleI ihAB ihBC

end Proof


abbrev Provable (Λ : Axioms α) (A : Formula α) : Prop := Nonempty (Λ ⊢! A)
infix:25 " ⊢ " => Provable

abbrev Unprovable (Λ : Axioms α) (A : Formula α) : Prop := ¬(Λ ⊢ A)
infix:25 " ⊬ " => Unprovable

namespace Provable

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ Λ → Λ ⊢ A := λ h => ⟨Proof.axm h⟩
@[simp, grind .] lemma andElimL : Λ ⊢ (A ⋏ B) 🡒 A := ⟨Proof.andElimL⟩
@[simp, grind .] lemma andElimR : Λ ⊢ (A ⋏ B) 🡒 B := ⟨Proof.andElimR⟩
@[simp, grind .] lemma orIntroL : Λ ⊢ A 🡒 (A ⋎ B) := ⟨Proof.orIntroL⟩
@[simp, grind .] lemma orIntroR : Λ ⊢ B 🡒 (A ⋎ B) := ⟨Proof.orIntroR⟩
@[simp, grind .] lemma distributeAndOr : Λ ⊢ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := ⟨Proof.distributeAndOr⟩
@[simp, grind .] lemma impId : Λ ⊢ A 🡒 A := ⟨Proof.impId⟩
@[simp, grind .] lemma efq : Λ ⊢ ⊥ 🡒 A := ⟨Proof.efq⟩
@[simp, grind .] lemma verum : Λ ⊢ ⊤ := ⟨Proof.verum⟩
@[grind =>] lemma mdp : Λ ⊢ A 🡒 B → Λ ⊢ A → Λ ⊢ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨Proof.mdp h₁ h₂⟩
@[grind <=] lemma af : Λ ⊢ A → Λ ⊢ B 🡒 A := λ ⟨h⟩ => ⟨Proof.af h⟩
@[grind <=] lemma ruleC : Λ ⊢ A 🡒 B → Λ ⊢ A 🡒 C → Λ ⊢ A 🡒 (B ⋏ C) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨Proof.ruleC h₁ h₂⟩
@[grind <=] lemma ruleD : Λ ⊢ A 🡒 C → Λ ⊢ B 🡒 C → Λ ⊢ (A ⋎ B) 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨Proof.ruleD h₁ h₂⟩
@[grind =>] lemma ruleI : Λ ⊢ A 🡒 B → Λ ⊢ B 🡒 C → Λ ⊢ A 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨Proof.ruleI h₁ h₂⟩

@[grind <=] lemma orIntroRuleL : Λ ⊢ A → Λ ⊢ (A ⋎ B) := λ h => mdp orIntroL h
@[grind <=] lemma orIntroRuleR : Λ ⊢ B → Λ ⊢ (A ⋎ B) := λ h => mdp orIntroR h
@[grind <=] lemma andIntro : Λ ⊢ A → Λ ⊢ B → Λ ⊢ A ⋏ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨Proof.andIntro h₁ h₂⟩

lemma ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ A → Λ₂ ⊢ A := λ ⟨h⟩ => ⟨Proof.ofSubsetAxm hsub h⟩
lemma ofEmpty : ∅ ⊢ A → Λ ⊢ A := ofSubsetAxm (by grind)

lemma ruleI₃ : Λ ⊢ A 🡒 B → Λ ⊢ B 🡒 C → Λ ⊢ C 🡒 D → Λ ⊢ A 🡒 D := by
  intro hAB hBC hCD;
  exact ruleI (ruleI hAB hBC) hCD;

lemma distributeOrAnd : Λ ⊢ ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := ⟨Proof.distributeOrAnd⟩

lemma replaceAnd₂ (h : Λ ⊢ B 🡒 C) : Λ ⊢ (A ⋏ B) 🡒 (A ⋏ C) := by
  apply ruleC;
  . exact andElimL;
  . exact ruleI andElimR h;

lemma replaceOr₂ (h : Λ ⊢ B 🡒 C) : Λ ⊢ (A ⋎ B) 🡒 (A ⋎ C) := by
  apply ruleD;
  . exact orIntroL;
  . exact ruleI h orIntroR;


@[grind <=]
lemma lconj_of_mem {X : List (Formula α)} (h : A ∈ X) : Λ ⊢ ⋀X 🡒 A := by
  match X with
  | [] => grind;
  | [B] => grind;
  | B :: C :: X =>
    simp_all only [List.mem_cons, Formula.lconj];
    rcases h with (rfl | rfl | h);
    . exact andElimL;
    . exact ruleI andElimR (lconj_of_mem (by grind));
    . exact ruleI andElimR (lconj_of_mem (by grind));

@[grind <=]
lemma fconj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ ⋀X 🡒 A := lconj_of_mem (by simpa)


@[grind <=]
lemma ldisj_of_mem {X : List (Formula α)} (h : A ∈ X) : Λ ⊢ A 🡒 ⋁X := by
  match X with
  | [] => grind;
  | [B] => grind;
  | B :: C :: X =>
    simp_all only [List.mem_cons, Formula.ldisj];
    rcases h with (rfl | rfl | h);
    . exact orIntroL;
    . exact ruleI (ldisj_of_mem (by grind)) orIntroR;
    . exact ruleI (ldisj_of_mem (by grind)) orIntroR;

@[grind <=]
lemma fdisj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ A 🡒 ⋁X := ldisj_of_mem (by simpa)


lemma ldisj_insert {X : List (Formula α)} {A} : Λ ⊢ ⋁(A :: X) 🡒 (⋁X ⋎ A) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleD <;> simp;

lemma ldisj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : Λ ⊢ ⋁X 🡒 ⋁Y := by
  match X with
  | [] => grind;
  | [B] => grind;
  | B :: X =>
    simp_all only [List.cons_subset];
    rcases h with ⟨hB, hXY⟩;
    apply ruleI;
    . exact ldisj_insert;
    . apply ruleD;
      . exact ldisj_of_subset hXY;
      . exact ldisj_of_mem hB;

lemma fdisj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ ⋁X 🡒 ⋁Y := ldisj_of_subset $ by intro A; simpa using @h A;

lemma fdisj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ ⋁(insert A X) 🡒 (⋁X ⋎ A) := by
  apply ruleI ?_ ldisj_insert;
  apply ldisj_of_subset;
  intro B;
  simp;


lemma lconj_insert {X : List (Formula α)} {A} : Λ ⊢ (⋀X ⋏ A) 🡒 ⋀(A :: X) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleC <;> simp;

lemma lconj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : Λ ⊢ ⋀Y 🡒 ⋀X := by
  match X with
  | [] => grind;
  | [B] => grind;
  | B :: X =>
    simp_all only [List.cons_subset];
    rcases h with ⟨hB, hXY⟩;
    apply ruleI;
    . apply ruleC;
      . exact lconj_of_subset hXY;
      . exact lconj_of_mem hB;
    . apply lconj_insert;

lemma fconj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ ⋀Y 🡒 ⋀X := lconj_of_subset $ by intro A; simpa using @h A;

lemma fconj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ (⋀X ⋏ A) 🡒 ⋀(insert A X) := by
  apply ruleI lconj_insert;
  apply lconj_of_subset;
  intro B;
  simp;


@[induction_eliminator]
protected lemma rec_provable
  {motive          : (A : Formula α) → (Λ ⊢ A) → Prop}
  (axm             : ∀ {A}, (h : A ∈ Λ) → motive A (axm h))
  (mdp             : ∀ {A B}, {hAB : Λ ⊢ A 🡒 B} → {hA : Λ ⊢ A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (af              : ∀ {A B}, {hA : Λ ⊢ A} → (motive A hA) → (motive (B 🡒 A) (af hA)))
  (ruleC           : ∀ {A B C}, {hAB : Λ ⊢ A 🡒 B} → {hAC : Λ ⊢ A 🡒 C} → (motive (A 🡒 B) hAB) → (motive (A 🡒 C) hAC) → (motive (A 🡒 (B ⋏ C)) (ruleC hAB hAC)))
  (ruleD           : ∀ {A B C}, {hAC : Λ ⊢ A 🡒 C} → {hBC : Λ ⊢ B 🡒 C} → (motive (A 🡒 C) hAC) → (motive (B 🡒 C) hBC) → (motive ((A ⋎ B) 🡒 C) (ruleD hAC hBC)))
  (ruleI           : ∀ {A B C}, {hAB : Λ ⊢ A 🡒 B} → {hBC : Λ ⊢ B 🡒 C} → (motive (A 🡒 B) hAB) → (motive (B 🡒 C) hBC) → (motive (A 🡒 C) (ruleI hAB hBC)))
  (distributeAndOr : ∀ {A B C : Formula α}, (motive ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) distributeAndOr))
  (impId           : ∀ {A}, (motive (A 🡒 A) impId))
  (andElimL        : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR        : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (orIntroL        : ∀ {A B}, (motive (A 🡒 (A ⋎ B)) orIntroL))
  (orIntroR        : ∀ {A B}, (motive (B 🡒 (A ⋎ B)) orIntroR))
  (efq             : ∀ {A}, (motive (⊥ 🡒 A) efq))
  : ∀ {A}, (d : Λ ⊢ A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end Provable



section Semantics

structure Frame (κ : Type*) (α : Type*) where
  Rel' : Formula α → κ → κ → Prop
  root' : κ
  root_rooted' : ∀ {A x}, Rel' A root' x

namespace Frame

variable {κ α : Type*} {F : Frame κ α}

abbrev World (_ : Frame κ α) := κ
abbrev Rel {F : Frame κ α} (A : Formula α) (x y : F.World) := F.Rel' A x y
notation:45 x:90 " ≺[" φ "] " y:90 => Frame.Rel φ x y

abbrev root : F.World := F.root'
@[grind .] lemma root_rooted : ∀ {A x}, F.root ≺[A] x := F.root_rooted'

end Frame


structure Model (κ : Type*) (α : Type*) extends Frame κ α where
  Val : α → (toFrame.World) → Prop

namespace Model

instance : CoeFun (Model κ α) (λ M => α → M.World → Prop) := ⟨fun m => m.Val⟩

end Model

namespace Formula

variable {κ α : Type*} {M : Model κ α} {A B C : Formula α}

@[grind]
def Forced {M : Model κ α} (x : M.World) : Formula α → Prop
  | #a     => M a x
  | ⊥      => False
  | A ⋏ B   => Forced x A ∧ Forced x B
  | A ⋎ B  => Forced x A ∨ Forced x B
  | A 🡒 B => ∀ y, x ≺[A 🡒 B] y → (Forced y A → Forced y B)
infix:45 " ⊩ " => Forced

abbrev NotForced {M : Model κ α} (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForced

lemma iff_not_forced_imp : (x ⊮ A 🡒 B) ↔ (∃ y, x ≺[A 🡒 B] y ∧ (y ⊩ A ∧ y ⊮ B)) := by
  simp [NotForced, Forced];

@[grind] def Valid (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:45 " ⊨ " => Valid

@[grind] abbrev NotValid (M : Model κ α) (A : Formula α) : Prop := ¬(M ⊨ A)
infix:45 " ⊭ " => NotValid

lemma iff_Valid_exists_world_not_forced {M : Model κ α} {A : Formula α} : (M ⊭ A) ↔ (∃ x : M.World, x ⊮ A) := by
  simp only [NotValid, Valid, not_forall, NotForced];

@[grind] def FrameValid (F : Frame κ α) (A : Formula α) : Prop := ∀ V, Valid ⟨F, V⟩ A
infix:45 " ⊨ " => FrameValid

abbrev NotFrameValid (F : Frame κ α) (A : Formula α) : Prop := ¬(F ⊨ A)
infix:45 " ⊭ " => NotFrameValid

lemma iff_notFrameValid_exists_model_world {F : Frame κ α} {A : Formula α} : (F ⊭ A) ↔ (∃ V, ∃ x : (⟨F, V⟩ : Model κ α).World, x ⊮ A) := by
  simp only [NotFrameValid, FrameValid, Valid, not_forall, NotForced];

end Formula


variable {κ α : Type*} {M : Model κ α} {A B C : Formula α}

@[grind .] lemma valid_andElimL : M ⊨ (A ⋏ B) 🡒 A := by grind;
@[grind .] lemma valid_andElimR : M ⊨ (A ⋏ B) 🡒 B := by grind;
@[grind .] lemma valid_orIntroL : M ⊨ A 🡒 (A ⋎ B) := by grind;
@[grind .] lemma valid_orIntroR : M ⊨ B 🡒 (A ⋎ B) := by grind;
@[grind .] lemma valid_distributeAndOr : M ⊨ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by grind;
@[grind .] lemma valid_impId : M ⊨ A 🡒 A := by grind;
@[grind .] lemma valid_efq : M ⊨ ⊥ 🡒 A := by grind;

@[grind <=]
lemma valid_ruleI (hAB : M ⊨ A 🡒 B) (hBC : M ⊨ B 🡒 C) : M ⊨ A 🡒 C := by
  intro x y Rxy hya;
  exact hBC M.root y (by grind) $ hAB M.root y (by grind) hya;

@[grind <=]
lemma valid_ruleC (hAB : M ⊨ A 🡒 B) (hAC : M ⊨ A 🡒 C) : M ⊨ A 🡒 (B ⋏ C) := by
  intro x y Rxy hya;
  have := hAB M.root y (by grind) hya;
  have := hAC M.root y (by grind) hya;
  grind;

@[grind <=]
lemma valid_ruleD (hAC : M ⊨ A 🡒 C) (hBC : M ⊨ B 🡒 C) : M ⊨ (A ⋎ B) 🡒 C := by
  rintro x y Rxy (h | h);
  . exact hAC M.root y (by grind) h;
  . exact hBC M.root y (by grind) h;

@[grind =>]
lemma valid_mdp (hAB : M ⊨ A 🡒 B) (hA : M ⊨ A) : M ⊨ B := by
  intro x;
  exact hAB _ x (show M.root ≺[A 🡒 B] x by grind) (by grind);

@[grind <=]
lemma valid_af (hA : M ⊨ A) : M ⊨ B 🡒 A := by grind;

theorem soundness : (Λ ⊢ A) → (∀ {κ}, ∀ M : Model κ α, (∀ φ ∈ Λ, M ⊨ φ) → M ⊨ A) := by
  intro h _ M hΛ; induction h <;> grind;

@[grind .]
theorem consistency_of_VF : (∅ ⊬ (⊥ : Formula α)) := by
  by_contra!;
  let M : Model (Fin 1) α := {
    Rel' := λ _ _ _ => True,
    root' := 1,
    root_rooted' := by grind;
    Val := λ _ _ => True
  };
  have : (1 : M.World) ⊩ ⊥ := soundness this M (by grind) _;
  contradiction;

@[grind .]
theorem consistency_VF : (∅ ⊬ (⊥ : Formula α)) := by
  by_contra!;
  let M : Model (Fin 1) α := {
    Rel' := λ _ _ _ => True,
    root' := 1,
    root_rooted' := by grind;
    Val := λ _ _ => True
  };
  have : (1 : M.World) ⊩ ⊥ := soundness this M (by grind) _;
  contradiction;

example : (∅ ⊬ (⊤ 🡒 (#0 ⋏ #1) 🡘 (⊤ 🡒 (#1 ⋏ #0)))) := by
  by_contra!;
  let M : Model (Fin 3) ℕ := {
    Rel' := λ A x y =>
      match A with
      | (⊤ 🡒 (#0 ⋏ #1)) => x ≠ 1
      | (⊤ 🡒 (#1 ⋏ #0)) => x ≤ y
      | _ => True
    ,
    root' := 0,
    root_rooted' := by grind;
    Val := λ a x =>
      match a with
      | 0 => x = 2
      | _ => False
  };
  have : (0 : M.World) ⊩ (⊤ 🡒 (#0 ⋏ #1) 🡘 (⊤ 🡒 (#1 ⋏ #0))) := soundness this M (by grind) 0;
  have : (2 : M.World) ⊩ #1 := @this.1 1 (by grind) (by grind) 2 (by grind) (by grind) |>.1;
  contradiction;


section

@[grind]
def Formula.FrameForced {F : Frame κ α} (x : F.World) (A : Formula α) (A_closed : A.Closed) : Prop :=
  match A with
  | ⊥ => False
  | A ⋏ B => A.FrameForced x (by grind) ∧ B.FrameForced x (by grind)
  | A ⋎ B => A.FrameForced x (by grind) ∨ B.FrameForced x (by grind)
  | A 🡒 B => ∀ {y}, F.Rel (A 🡒 B) x y → (A.FrameForced y (by grind) → B.FrameForced y (by grind))

end

variable {F : Frame κ α}

@[grind =_]
lemma iff_frameForced_forced_of_closed {F : Frame κ α} {x : F.World} {V : α → F.World → Prop} {A : Formula α} (A_closed : A.Closed) : A.FrameForced x A_closed ↔ (A.Forced (M := ⟨F, V⟩) x) := by
  induction A generalizing x <;> grind;

lemma iff_forced_CNA (hA : A.Closed) : (∼A).FrameValid F ↔ ∀ x : F.World, ¬(A.FrameForced x (by grind)) := by
  constructor;
  . intro h x;
    by_contra!
    exact h (λ _ _ => True) F.root x (by grind) $ iff_frameForced_forced_of_closed (by grind) |>.mp this;
  . intro h V x;
    grind;

@[grind =_]
lemma iff_closed_not_and : (∼(A ⋎ B)).FrameValid F ↔ ((∼A).FrameValid F ∧ (∼B).FrameValid F) := by grind;

lemma iff_closed_not_imp (hA : A.Closed) (hB : B.Closed)
  : (∼(A 🡒 B)).FrameValid F ↔ (∀ x : F.World, ∃ y : F.World, x ≺[A 🡒 B] y ∧ (A.FrameForced y (by grind) ∧ ¬B.FrameForced y (by grind))) := by
  apply Iff.trans (iff_forced_CNA (A := A 🡒 B) (by grind));
  simp [Formula.FrameForced];

lemma iff_closed_dn (hA : A.Closed) : (∼∼A).FrameValid F ↔ (∀ x : F.World, ∃ y : F.World, x ≺[∼A] y ∧ (A.FrameForced y (by grind))) := by
  apply Iff.trans (iff_closed_not_imp (A := A) (B := ⊥) (by grind) (by grind));
  simp [Formula.FrameForced];

end Semantics



section

@[grind]
def AczelSlash (Λ : Axioms α) : Formula α → Prop
  | #a => Λ ⊢ #a
  | ⊥ => False
  | φ ⋎ ψ => AczelSlash Λ φ ∨ AczelSlash Λ ψ
  | φ ⋏ ψ => AczelSlash Λ φ ∧ AczelSlash Λ ψ
  | φ 🡒 ψ => (Λ ⊢ φ 🡒 ψ) ∧ (AczelSlash Λ φ → AczelSlash Λ ψ)
infix:25 " ∕ " => AczelSlash

namespace AczelSlash

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>]
lemma mdp : Λ ∕ (A 🡒 B) → Λ ∕ A → Λ ∕ B := by grind;

end AczelSlash

variable {Λ : Axioms α} {A B C : Formula α}

lemma provable_of_slashable : (Λ ∕ A) → (Λ ⊢ A) := by induction A <;> grind;

lemma iff_slashable_provable_of_CNA (H : ∀ A ∈ Λ, A.IsCNA) : (Λ ∕ A) ↔ (Λ ⊢ A) := by
  constructor;
  . exact provable_of_slashable;
  . intro h;
    induction h with
    | @axm A h =>
      obtain ⟨B, rfl, _, _⟩ := Formula.of_isCNA $ H _ h;
      constructor;
      . exact Provable.axm h;
      . intro hB;
        have : Λ ⊢ ⊥ := .mdp (.axm h) (provable_of_slashable hB);
        sorry;
    | _ => grind;

lemma disjunctive_of_CNA (H : ∀ A ∈ Λ, A.IsCNA) : (Λ ⊢ (A ⋎ B)) → (Λ ⊢ A) ∨ (Λ ⊢ B) := by
  intro h;
  rcases iff_slashable_provable_of_CNA H |>.mpr h with h | h;
  . left; exact iff_slashable_provable_of_CNA H |>.mp h;
  . right; exact iff_slashable_provable_of_CNA H |>.mp h;


variable [Fact (∀ {A B}, (Λ ⊢ (A ⋎ B)) → (Λ ⊢ A) ∨ (Λ ⊢ B))]

lemma Provable.ldisj_disjunctive {l : List _} (hl : l ≠ []) : Λ ⊢ ⋁l → ∃ B ∈ l, Λ ⊢ B := by
  match l with
  | [] => contradiction
  | [A] => intro _; use A; simpa;
  | A :: B :: l =>
    intro hAB;
    unfold Formula.ldisj at hAB;
    rcases (Fact.elim (p := ∀ {A B}, (Λ ⊢ (A ⋎ B)) → (Λ ⊢ A) ∨ (Λ ⊢ B)) inferInstance hAB) with hA | hB;
    . use A;
      grind;
    . obtain ⟨C, hC⟩ := ldisj_disjunctive (by grind) hB;
      use C;
      grind;

lemma Provable.fdisj_disujunctive {s : Finset _} (hs : s ≠ ∅) : Λ ⊢ ⋁s → ∃ B ∈ s, Λ ⊢ B := by
  intro h;
  simpa using ldisj_disjunctive (by simpa) h;


end



section Completeness

namespace Formula

@[grind]
def subfml [DecidableEq α] : Formula α → Finset (Formula α)
  | #a => {#a}
  | ⊥  => {⊥}
  | A ⋏ B => insert (A ⋏ B) (A.subfml ∪ B.subfml)
  | A ⋎ B => insert (A ⋎ B) (A.subfml ∪ B.subfml)
  | A 🡒 B => insert (A 🡒 B) (A.subfml ∪ B.subfml)

variable {A B C : Formula α} [DecidableEq α]

@[grind .] lemma mem_subfml_self : A ∈ A.subfml := by induction A <;> grind;
@[grind! =>] lemma mem_subfml_of_mem_and_subfml : (B ⋏ C) ∈ A.subfml → B ∈ A.subfml ∧ C ∈ A.subfml := by induction A <;> grind;
@[grind! =>] lemma mem_subfml_of_mem_or_subfml : (B ⋎ C) ∈ A.subfml → B ∈ A.subfml ∧ C ∈ A.subfml := by induction A <;> grind;
@[grind! =>] lemma mem_subfml_of_mem_imp_subfml : (B 🡒 C) ∈ A.subfml → B ∈ A.subfml ∧ C ∈ A.subfml := by induction A <;> grind;

end Formula


variable {α : Type u} [DecidableEq α]
variable {Λ : Axioms α} {A : Formula α}

@[grind]
def scope (Λ : Axioms α) (A : Formula α) : Finset (Formula α) :=
  {⊤, ⊥} ∪
  A.subfml ∪
  Λ.biUnion (·.subfml)

section

variable {A B C : Formula α}

@[simp, grind .] lemma mem_scope_self : A ∈ scope Λ A := by grind [scope];
@[simp, grind .] lemma mem_scope_top : ⊤ ∈ scope Λ A := by grind [scope];
@[simp, grind .] lemma mem_scope_bot : ⊥ ∈ scope Λ A := by grind [scope];

@[grind =>] lemma mem_scope_of_mem_subfml (h : B ∈ A.subfml) : B ∈ scope Λ A := by grind [scope]
@[grind =>] lemma mem_scope_of_mem_axioms_subfmls (h : B ∈ Λ.biUnion (·.subfml)) : B ∈ scope Λ A := by grind [scope]
@[grind =>] lemma mem_scope_of_mem_axioms (h : B ∈ Λ) : B ∈ scope Λ A := by grind [scope]

@[grind =>] lemma mem_scope_of_mem_and_scope (h : (B ⋏ C) ∈ scope Λ A) : B ∈ scope Λ A ∧ C ∈ scope Λ A := by grind;
@[grind =>] lemma mem_scope_of_mem_or_scope (h : (B ⋎ C) ∈ scope Λ A) : B ∈ scope Λ A ∧ C ∈ scope Λ A := by grind;
@[grind =>] lemma mem_scope_of_mem_imp_scope (h : (B 🡒 C) ∈ scope Λ A) : B ∈ scope Λ A ∧ C ∈ scope Λ A := by grind;

end


abbrev ScopeOf (Λ : Axioms α) (A : Formula α) := { B // B ∈ (scope Λ A) }

instance : Fintype (Finset (ScopeOf Λ A)) where
  elems := Finset.univ.powerset;
  complete := by grind;


structure Tableau (Λ : Axioms α) (A : Formula α) where
  ant : (Finset (ScopeOf Λ A))
  con : (Finset (ScopeOf Λ A))

instance : Finite (Tableau Λ A) := Finite.of_injective (λ T => (T.ant, T.con)) $ by
  rintro ⟨_, _⟩ ⟨_, _⟩;
  simp;

namespace Tableau

variable {T : Tableau Λ A}

def Inconsistent (T : Tableau Λ A) : Prop := Λ ⊢ ⋀(T.ant.image (·.1)) 🡒 ⋁(T.con.image (·.1))
abbrev Consistent (T : Tableau Λ A) : Prop := ¬(T.Inconsistent)

lemma iff_inconsistent : T.Inconsistent ↔ Λ ⊢ ⋀ (T.ant.image (·.1)) 🡒 ⋁ (T.con.image (·.1)) := by tauto;

def insertAnt (T : Tableau Λ A) (B : ScopeOf Λ A) : Tableau Λ A := { T with ant := insert B T.ant }
def insertCon (T : Tableau Λ A) (B : ScopeOf Λ A) : Tableau Λ A := { T with con := insert B T.con }

open Provable in
lemma either_consistent_insert
  (T : Tableau Λ A) (B : ScopeOf Λ A) (T_consis : T.Consistent)
  : Tableau.Consistent (Tableau.insertAnt T B) ∨ Tableau.Consistent (Tableau.insertCon T B) := by
  by_contra! hC;
  rcases hC with ⟨hB₁, hB₂⟩;
  apply T_consis;
  simp only [Inconsistent, insertAnt, insertCon] at hB₁ hB₂ ⊢;
  generalize eΓ : T.ant.image (·.1) = Γ at ⊢ hB₁ hB₂;
  generalize eΔ : T.con.image (·.1) = Δ at ⊢ hB₁ hB₂;
  generalize eΔB : (insert B T.con).image (·.1) = ΔB at ⊢ hB₁ hB₂;
  generalize eΓB : (insert B T.ant).image (·.1) = ΓB at ⊢ hB₁ hB₂;
  apply ruleI₃ (B := (⋁Δ ⋎ ⋀Γ) ⋏ ⋁ΔB) (C := (⋁Δ ⋎ ⋀ΓB))
  . exact ruleC orIntroR hB₂;
  . apply ruleI₃ (B := ((⋁Δ ⋎ ⋀Γ) ⋏ (⋁Δ ⋎ B))) (C := ⋁Δ ⋎ (⋀Γ ⋏ B));
    . apply replaceAnd₂;
      subst eΔB eΔ;
      simpa using fdisj_insert;
    . exact distributeOrAnd
    . apply replaceOr₂;
      subst eΓB eΓ;
      simpa using fconj_insert;
  . exact ruleD impId hB₁;

def Saturated (T : Tableau Λ A) := T.ant ∪ T.con = Finset.univ

@[grind =>]
lemma mem_ant_of_not_mem_con_of_saturated {T : Tableau Λ A} (hT : T.Saturated) {B : ScopeOf Λ A} : B ∉ T.con → B ∈ T.ant := by
  have := hT ▸ Finset.mem_univ B;
  grind only [= Finset.mem_union];

@[grind =>]
lemma mem_con_of_not_mem_ant_of_saturated {T : Tableau Λ A} (hT : T.Saturated) {B : ScopeOf Λ A} : B ∉ T.ant → B ∈ T.con := by
  have := hT ▸ Finset.mem_univ B;
  grind only [= Finset.mem_union];

end Tableau


structure SaturatedConsistentTableau (Λ : Axioms α) (A : Formula α) extends Tableau Λ A where
  consistent : toTableau.Consistent
  saturated : toTableau.Saturated

namespace SaturatedConsistentTableau

instance : Finite (SaturatedConsistentTableau Λ A) := Finite.of_injective (·.toTableau) $ by
  rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩;
  simp;

variable {T : SaturatedConsistentTableau Λ A}

@[grind =]
lemma iff_mem_ant_not_mem_con : B ∈ T.ant ↔ B ∉ T.con := by
  constructor;
  . intro hB₁;
    by_contra! hB₂;
    apply T.consistent;
    apply Provable.ruleI₃ (B := B) (C := B) <;> grind;
  . apply T.toTableau.mem_ant_of_not_mem_con_of_saturated T.saturated;

@[grind =]
lemma iff_mem_con_not_mem_ant : B ∈ T.con ↔ B ∉ T.ant := by
  constructor;
  . contrapose!;
    exact iff_mem_ant_not_mem_con.mp;
  . apply T.toTableau.mem_con_of_not_mem_ant_of_saturated T.saturated;

lemma imp_closed : Λ ⊢ (B.1 🡒 C.1) → B ∈ T.ant → C ∈ T.ant := by
  rintro hBC hB;
  by_contra! hC;
  apply T.consistent;
  apply Provable.ruleI₃ (B := B) (C := C) <;> grind;

@[simp, grind .]
lemma mem_ant_top : ⟨⊤, by grind⟩ ∈ T.ant := by
  have := T.consistent;
  contrapose! this;
  exact Provable.ruleI (Provable.af (show Λ ⊢ ⊤ by simp)) $ Provable.fdisj_of_mem (by grind);

@[simp, grind .]
lemma mem_con_bot : ⟨⊥, by grind⟩ ∈ T.con := by
  have := T.consistent;
  contrapose! this;
  exact Provable.ruleI (Provable.fconj_of_mem (by grind)) Provable.efq;

@[grind =>]
lemma iff_mem_ant_and (hBC : (B ⋏ C) ∈ scope Λ A) : (⟨B ⋏ C, hBC⟩ ∈ T.ant) ↔ (⟨B, by grind⟩ ∈ T.ant ∧ ⟨C, by grind⟩ ∈ T.ant) := by
  constructor;
  . rintro h;
    constructor <;> exact T.imp_closed (by grind) h;
  . rintro ⟨hB, hC⟩;
    by_contra! hBC;
    apply T.consistent;
    apply Provable.ruleI (B := B ⋏ C);
    . apply Provable.ruleC <;> grind;
    . grind;

@[grind =>]
lemma iff_mem_ant_or (hBC : (B ⋎ C) ∈ scope Λ A) : (⟨B ⋎ C, hBC⟩ ∈ T.ant) ↔ (⟨B, by grind⟩ ∈ T.ant ∨ ⟨C, by grind⟩ ∈ T.ant) := by
  constructor;
  . rintro hBC;
    by_contra!;
    rcases this with ⟨hB, hC⟩;
    apply T.consistent;
    apply Provable.ruleI (B := B ⋎ C);
    . grind;
    . apply Provable.ruleD <;> grind;
  . rintro (hB | hC);
    . exact T.imp_closed (by grind) hB;
    . exact T.imp_closed (by grind) hC;

@[grind =>]
lemma mem_ant_of_provable (hB : Λ ⊢ B.1) : B ∈ T.ant := imp_closed (by grind) mem_ant_top

@[grind .]
lemma not_mem_both : ¬(B ∈ T.ant ∧ B ∈ T.con) := by grind;


namespace lindenbaum

open Classical

noncomputable def next (T : Tableau Λ A) (B : ScopeOf Λ A) : Tableau Λ A :=
  if Tableau.Consistent (Tableau.insertAnt T B) then Tableau.insertAnt T B else Tableau.insertCon T B

variable {T : Tableau Λ A} {B : ScopeOf Λ A}

lemma next_consistent (hT : T.Consistent) : Tableau.Consistent (next T B) := by
  dsimp [next];
  split;
  . trivial;
  . grind [Tableau.either_consistent_insert];

lemma next_monotone_ant : T.ant ⊆ (next T B).ant := by grind [next, Tableau.insertAnt, Tableau.insertCon];
lemma next_monotone_con : T.con ⊆ (next T B).con := by grind [next, Tableau.insertAnt, Tableau.insertCon];

lemma next_of_mem : B ∈ (next T B).ant ∨ B ∈ (next T B).con := by grind [next, Tableau.insertAnt, Tableau.insertCon];

noncomputable def enum (T : Tableau Λ A) : List (ScopeOf Λ A) → Tableau Λ A
  | [] => T
  | B :: X => next (enum T X) B

variable {X : List (ScopeOf Λ A)}

@[simp, grind .]
lemma enum_consistent (hT : T.Consistent) {X : List (ScopeOf Λ A)} : Tableau.Consistent (enum T X) := by
  induction X with
  | nil => trivial
  | cons _ _ ih => apply next_consistent ih;

lemma enum_monotone_ant : T.ant ⊆ (enum T X).ant := by
  induction X with
  | nil => simp [enum];
  | cons B X ih =>
    trans (enum T X).ant;
    . exact ih;
    . exact next_monotone_ant;

lemma enum_monotone_con : T.con ⊆ (enum T X).con := by
  induction X with
  | nil => simp [enum];
  | cons B X ih =>
    trans (enum T X).con;
    . exact ih;
    . exact next_monotone_con;

lemma enum_of_mem (hB : B ∈ X) : B ∈ (enum T X).ant ∨ B ∈ (enum T X).con := by
  induction X with
  | nil => contradiction
  | cons C X ih =>
    simp only [List.mem_cons] at hB;
    rcases hB with rfl | hB;
    . rcases next_of_mem (T := enum T X) (B := B) with h | h <;> grind [enum];
    . rcases ih hB with h | h;
      . left; apply next_monotone_ant h;
      . right; apply next_monotone_con h;

end lindenbaum

noncomputable def lindenbaum (T : Tableau Λ A) (T_consis : T.Consistent) : SaturatedConsistentTableau Λ A where
  toTableau := lindenbaum.enum (Λ := Λ) (A := A) T (Finset.univ.toList)
  consistent := lindenbaum.enum_consistent T_consis
  saturated := by
    ext B;
    simp only [Finset.mem_union, Finset.mem_univ, iff_true];
    apply lindenbaum.enum_of_mem;
    simp;

@[simp, grind .] lemma lindenbaum_subset_ant {T : Tableau Λ A} {T_consis : T.Consistent} : T.ant ⊆ (lindenbaum T T_consis).ant := lindenbaum.enum_monotone_ant
@[simp, grind .] lemma lindenbaum_subset_con {T : Tableau Λ A} {T_consis : T.Consistent} : T.con ⊆ (lindenbaum T T_consis).con := lindenbaum.enum_monotone_con

end SaturatedConsistentTableau

open Classical
noncomputable abbrev countermodel.rootSeed (Λ : Axioms α) (A : Formula α) : Tableau Λ A where
  ant := ∅
  con := Finset.univ.filter (λ ⟨B, _⟩ => ∃ C D, B = C.1 🡒 D.1 ∧ ∃ T : SaturatedConsistentTableau Λ A, C ∈ T.ant ∧ D ∈ T.con )

@[simp, grind .]
lemma countermodel.rootSeed_consistent {Λ : Axioms α} {A : Formula α} [Fact (Λ ⊬ ⊥)] [Fact (∀ {A B}, Λ ⊢ A ⋎ B → (Λ ⊢ A) ∨ (Λ ⊢ B))]
  : (countermodel.rootSeed Λ A).Consistent := by
  by_contra! hC;
  replace hC : Λ ⊢ ⊤ 🡒 ⋁((rootSeed Λ A).con.image (·.1)) := by
    simpa only [rootSeed, Subtype.exists, exists_and_left, Finset.image_empty, Formula.fconj_emptyset]
    using (Tableau.iff_inconsistent.mp hC);
  replace hC := Provable.mdp hC (Provable.verum);
  wlog ne : (rootSeed Λ A).con.image (·.1) ≠ ∅;
  . apply Fact.elim (p := Λ ⊬ ⊥) inferInstance;
    grind;
  obtain ⟨C, D, T, hC, hD, hCD⟩ : ∃ C D : ScopeOf Λ A, ∃ T : SaturatedConsistentTableau Λ A, C ∈ T.ant ∧ D ∈ T.con ∧ (Λ ⊢ C.1 🡒 D.1) := by
    have := Provable.fdisj_disujunctive ne hC;
    unfold rootSeed at this;
    grind;
  apply T.consistent;
  apply Provable.ruleI₃ (B := C.1) (C := D.1) <;> grind;

noncomputable def countermodel (Λ : Axioms α) (A) [Fact (Λ ⊬ ⊥)] [Fact (∀ {A B}, Λ ⊢ A ⋎ B → (Λ ⊢ A) ∨ (Λ ⊢ B))] : Model (SaturatedConsistentTableau Λ A) α where
  Val a T := (ha : #a ∈ scope Λ A) → ⟨#a, ha⟩ ∈ T.ant
  Rel' B T₁ T₂ :=
    match B with
    | (C 🡒 D) => (h : C 🡒 D ∈ scope Λ A) → ⟨C 🡒 D, h⟩ ∈ T₁.con ∨ ⟨C, (by grind)⟩ ∈ T₂.con ∨ ⟨D, (by grind)⟩ ∈ T₂.ant
    | _ => True
  root' := SaturatedConsistentTableau.lindenbaum (countermodel.rootSeed Λ A) (countermodel.rootSeed_consistent)
  root_rooted' := by
    intro B T;
    split;
    . rename_i B C D;
      intro h;
      by_contra!;
      rcases this with ⟨hCD, hC, hD⟩;
      apply hCD;
      apply SaturatedConsistentTableau.lindenbaum_subset_con;
      grind;
    . trivial;

variable [Fact (Λ ⊬ ⊥)] [Fact (∀ {A B}, Λ ⊢ A ⋎ B → (Λ ⊢ A) ∨ (Λ ⊢ B))]

lemma countermodel.truthlemma {T : (countermodel Λ A).World} (hB : B ∈ scope Λ A) : ⟨B, hB⟩ ∈ T.ant ↔ T ⊩ B := by
  induction B generalizing T with
  | atom a => tauto;
  | bot => grind;
  | and => apply Iff.trans $ SaturatedConsistentTableau.iff_mem_ant_and hB; grind;
  | or => apply Iff.trans $ SaturatedConsistentTableau.iff_mem_ant_or hB; grind;
  | imp C D ihC ihD =>
    constructor;
    . intro h S RTS hC;
      replace hC_ant := @ihC S (by grind) |>.mpr hC;
      rcases RTS hB with hCD | hC_con | hD_ant;
      . grind;
      . grind;
      . apply ihD _ |>.mp (by grind);
        grind;
    . contrapose!;
      intro h;
      apply Formula.iff_not_forced_imp.mpr;
      use SaturatedConsistentTableau.lindenbaum ⟨{⟨C, (by grind)⟩}, {⟨D, (by grind)⟩}⟩ $ by
        by_contra;
        replace : Λ ⊢ C 🡒 D := by simpa using Tableau.iff_inconsistent.mp this;
        exact h $ T.mem_ant_of_provable this;
      refine ⟨?_, ?_, ?_⟩
      . intro _;
        left;
        exact T.iff_mem_con_not_mem_ant.mpr h;
      . apply ihC (by grind) |>.mp;
        apply SaturatedConsistentTableau.lindenbaum_subset_ant;
        simp;
      . apply ihD (by grind) |>.not.mp;
        apply SaturatedConsistentTableau.iff_mem_con_not_mem_ant.mp;
        apply SaturatedConsistentTableau.lindenbaum_subset_con;
        simp;

lemma countermodel.valid_axioms : ∀ B ∈ Λ, (countermodel Λ A) ⊨ B := by
  intro B hB T;
  exact countermodel.truthlemma _ |>.mp $ T.mem_ant_of_provable (B := ⟨B, mem_scope_of_mem_axioms hB⟩) (Provable.axm hB);

theorem finite_model_property : (∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A) → Λ ⊢ A := by
  contrapose;
  intro h;
  push Not;
  use (SaturatedConsistentTableau Λ A), inferInstance, countermodel Λ A;
  constructor;
  . exact countermodel.valid_axioms;
  . apply Formula.iff_Valid_exists_world_not_forced.mpr;
    use SaturatedConsistentTableau.lindenbaum (Λ := Λ) (A := A) ⟨∅, {⟨A, by grind⟩}⟩ $ by
      by_contra;
      replace : Λ ⊢ ⊤ 🡒 A := by simpa using Tableau.iff_inconsistent.mp this;
      exact h $ Provable.mdp this (Provable.verum);;
    apply countermodel.truthlemma (by grind) |>.not.mp;
    apply SaturatedConsistentTableau.iff_mem_con_not_mem_ant.mp;
    apply SaturatedConsistentTableau.lindenbaum_subset_con;
    simp;

theorem result : List.TFAE [
  Λ ⊢ A,
  ∀ {κ : Type u}, ∀ M : Model κ α, (∀ φ ∈ Λ, M ⊨ φ) → M ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ φ ∈ Λ, M ⊨ φ) → M ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _; apply soundness h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_model_property
  tfae_finish;

end Completeness
