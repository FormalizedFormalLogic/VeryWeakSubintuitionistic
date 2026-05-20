import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Finset.Basic

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

def lconj : List (Formula α) → Formula α
  | [] => ⊤
  | [A] => A
  | A :: l => A ⋏ (lconj l)
prefix:100 "⋀" => lconj

def ldisj : List (Formula α) → Formula α
  | [] => ⊥
  | [A] => A
  | A :: l => A ⋎ (ldisj l)
prefix:100 "⋁" => ldisj


noncomputable def fconj (s : Finset (Formula α)) : Formula α := ⋀(s.toList)
prefix:100 "⋀" => fconj

noncomputable def fdisj (s : Finset (Formula α)) : Formula α := ⋁(s.toList)
prefix:100 "⋁" => fdisj

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
@[grind .] lemma andElimL : Λ ⊢ (A ⋏ B) 🡒 A := ⟨Proof.andElimL⟩
@[grind .] lemma andElimR : Λ ⊢ (A ⋏ B) 🡒 B := ⟨Proof.andElimR⟩
@[grind .] lemma orIntroL : Λ ⊢ A 🡒 (A ⋎ B) := ⟨Proof.orIntroL⟩
@[grind .] lemma orIntroR : Λ ⊢ B 🡒 (A ⋎ B) := ⟨Proof.orIntroR⟩
@[grind .] lemma distributeAndOr : Λ ⊢ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := ⟨Proof.distributeAndOr⟩
@[grind .] lemma impId : Λ ⊢ A 🡒 A := ⟨Proof.impId⟩
@[grind .] lemma efq : Λ ⊢ ⊥ 🡒 A := ⟨Proof.efq⟩
@[grind .] lemma verum : Λ ⊢ ⊤ := ⟨Proof.verum⟩
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



namespace Formula

@[grind]
def IsCNA : Formula α → Prop
  | ∼A => A.Closed ∧ (∅ ⊢ A) -- TODO: proves by Int
  | _ => False

lemma of_isCNA (h : A.IsCNA) : ∃ B, (A = ∼B) ∧ B.Closed ∧ (∅ ⊢ B) := by sorry;

end Formula


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

@[grind]
def Forced {M : Model κ α} (x : M.World) : Formula α → Prop
  | #a     => M a x
  | ⊥      => False
  | A ⋏ B   => Forced x A ∧ Forced x B
  | A ⋎ B  => Forced x A ∨ Forced x B
  | A 🡒 B => ∀ y, x ≺[A 🡒 B] y → (Forced y A → Forced y B)
infix:45 " ⊩ " => Forced

@[grind] abbrev NotForced {M : Model κ α} (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForced

@[grind] def Valid (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:45 " ⊨ " => Valid

@[grind] abbrev NotValid (M : Model κ α) (A : Formula α) : Prop := ¬(M ⊨ A)

@[grind] def FrameValid (F : Frame κ α) (A : Formula α) : Prop := ∀ V, Valid ⟨F, V⟩ A
infix:45 " ⊨ " => FrameValid

abbrev NotFrameValid (F : Frame κ α) (A : Formula α) : Prop := ¬(F ⊨ A)
infix:45 " ⊭ " => NotFrameValid

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

end AczelSlash

end
