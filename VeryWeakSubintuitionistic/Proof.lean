module

public import VeryWeakSubintuitionistic.Syntax

@[expose] public section

variable {α : Type*}

abbrev Axioms (α) := Finset (Formula α)

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

variable {Λ Λ₁ Λ₂ : Axioms α} {A B C : Formula α}

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
lemma sconj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ ⋀X 🡒 A := lconj_of_mem (by simpa)


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
lemma sdisj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ A 🡒 ⋁X := ldisj_of_mem (by simpa)


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

lemma sdisj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ ⋁X 🡒 ⋁Y := ldisj_of_subset $ by intro A; simpa using @h A;

lemma sdisj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ ⋁(insert A X) 🡒 (⋁X ⋎ A) := by
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

lemma sconj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ ⋀Y 🡒 ⋀X := lconj_of_subset $ by intro A; simpa using @h A;

lemma sconj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ (⋀X ⋏ A) 🡒 ⋀(insert A X) := by
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



class Axioms.Consistent (Λ : Axioms α) : Prop where
  unprovable_bot : Λ ⊬ ⊥

namespace Provable

export Axioms.Consistent (unprovable_bot)
attribute [simp, grind .] unprovable_bot

end Provable



section Disjunctive

class Axioms.Disjunctive (Λ : Axioms α) : Prop where
  disjunctive : ∀ {A B}, (Λ ⊢ (A ⋎ B)) → (Λ ⊢ A) ∨ (Λ ⊢ B)

namespace Provable

export Axioms.Disjunctive (disjunctive)

variable {Λ : Axioms α} [Axioms.Disjunctive Λ] {A B C : Formula α}

lemma ldisj_disjunctive {l : List _} (hl : l ≠ []) : Λ ⊢ ⋁l → ∃ B ∈ l, Λ ⊢ B := by
  match l with
  | [] => contradiction
  | [A] => intro _; use A; simpa;
  | A :: B :: l =>
    intro hAB;
    rcases disjunctive hAB with hA | hB;
    . use A;
      grind;
    . obtain ⟨C, hC⟩ := ldisj_disjunctive (by grind) hB;
      use C;
      grind;

lemma sdisj_disujunctive {s : Finset _} (hs : s ≠ ∅) : Λ ⊢ ⋁s → ∃ B ∈ s, Λ ⊢ B := by
  intro h;
  simpa using ldisj_disjunctive (by simpa) h;

end Provable

end Disjunctive
