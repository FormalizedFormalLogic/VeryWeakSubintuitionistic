module

public import VeryWeakSubintuitionistic.Propositional.Proof.Basic

@[expose] public section

variable {α : Type*}

inductive ProofVF (Λ : Axioms α) : Formula α → Type _
| axm {A}                 : A ∈ Λ → ProofVF Λ A
| andElimL {A B}          : ProofVF Λ $ (A ⋏ B) 🡒 A
| andElimR {A B}          : ProofVF Λ $ (A ⋏ B) 🡒 B
| orIntroL {A B}          : ProofVF Λ $ A 🡒 (A ⋎ B)
| orIntroR {A B}          : ProofVF Λ $ B 🡒 (A ⋎ B)
| distributeAndOr {A B C} : ProofVF Λ $ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))
| impId {A}               : ProofVF Λ $ A 🡒 A
| efq {A}                 : ProofVF Λ $ ⊥ 🡒 A
| mdp {A B}               : ProofVF Λ (A 🡒 B) → ProofVF Λ A → ProofVF Λ B
| af {A B}                : ProofVF Λ A → ProofVF Λ (B 🡒 A)
| ruleC {A B C}           : ProofVF Λ (A 🡒 B) → ProofVF Λ (A 🡒 C) → ProofVF Λ (A 🡒 (B ⋏ C))
| ruleD {A B C}           : ProofVF Λ (A 🡒 C) → ProofVF Λ (B 🡒 C) → ProofVF Λ ((A ⋎ B) 🡒 C)
| ruleI {A B C}           : ProofVF Λ (A 🡒 B) → ProofVF Λ (B 🡒 C) → ProofVF Λ (A 🡒 C)

infix:25 " ⊢ⱽ! " => ProofVF

namespace ProofVF

variable {Λ Λ₁ Λ₂ : Axioms α} {A B C : Formula α}

def andComm : Λ ⊢ⱽ! (A ⋏ B) 🡒 (B ⋏ A) := ruleC andElimR andElimL
def orComm  : Λ ⊢ⱽ! (A ⋎ B) 🡒 (B ⋎ A) := ruleD orIntroR orIntroL

def distributeOrAnd : Λ ⊢ⱽ! ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := by
  letI D := A ⋎ (B ⋏ C);
  haveI P₁ : Λ ⊢ⱽ! ((A ⋎ B) ⋏ A) 🡒 D := ruleI andElimR orIntroL
  haveI P₂ : Λ ⊢ⱽ! ((A ⋎ B) ⋏ C) 🡒 ((C ⋏ A) ⋎ (C ⋏ B)) := ruleI andComm distributeAndOr
  haveI P₃ : Λ ⊢ⱽ! (C ⋏ A) 🡒 D := ruleI andElimR orIntroL;
  haveI P₄ : Λ ⊢ⱽ! (C ⋏ B) 🡒 D := ruleI andComm orIntroR;
  haveI P₅ : Λ ⊢ⱽ! ((C ⋏ A) ⋎ (C ⋏ B)) 🡒 D := ruleD P₃ P₄;
  haveI P₆ : Λ ⊢ⱽ! ((A ⋎ B) ⋏ C) 🡒 D := ruleI P₂ P₅;
  haveI P₇ : Λ ⊢ⱽ! ((A ⋎ B) ⋏ A ⋎ (A ⋎ B) ⋏ C) 🡒 D := ruleD P₁ P₆;
  exact ruleI distributeAndOr P₇;

def verum : Λ ⊢ⱽ! ⊤ := impId

def orIntroRuleL : Λ ⊢ⱽ! A → Λ ⊢ⱽ! (A ⋎ B) := λ h => mdp orIntroL h
def orIntroRuleR : Λ ⊢ⱽ! B → Λ ⊢ⱽ! (A ⋎ B) := λ h => mdp orIntroR h

def andIntro : Λ ⊢ⱽ! A → Λ ⊢ⱽ! B → Λ ⊢ⱽ! A ⋏ B := λ h₁ h₂ => mdp (ruleC (af h₁) (af h₂)) (verum)

noncomputable def ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ⱽ! A → Λ₂ ⊢ⱽ! A := λ h => by
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

end ProofVF


abbrev ProvableVF (Λ : Axioms α) (A : Formula α) : Prop := Nonempty (Λ ⊢ⱽ! A)
infix:25 " ⊢ⱽ " => ProvableVF

abbrev UnprovableVF (Λ : Axioms α) (A : Formula α) : Prop := ¬(Λ ⊢ⱽ A)
infix:25 " ⊬ " => UnprovableVF

namespace ProvableVF

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ Λ → Λ ⊢ⱽ A := λ h => ⟨ProofVF.axm h⟩
@[simp, grind .] lemma andElimL : Λ ⊢ⱽ (A ⋏ B) 🡒 A := ⟨ProofVF.andElimL⟩
@[simp, grind .] lemma andElimR : Λ ⊢ⱽ (A ⋏ B) 🡒 B := ⟨ProofVF.andElimR⟩
@[simp, grind .] lemma orIntroL : Λ ⊢ⱽ A 🡒 (A ⋎ B) := ⟨ProofVF.orIntroL⟩
@[simp, grind .] lemma orIntroR : Λ ⊢ⱽ B 🡒 (A ⋎ B) := ⟨ProofVF.orIntroR⟩
@[simp, grind .] lemma distributeAndOr : Λ ⊢ⱽ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := ⟨ProofVF.distributeAndOr⟩
@[simp, grind .] lemma impId : Λ ⊢ⱽ A 🡒 A := ⟨ProofVF.impId⟩
@[simp, grind .] lemma efq : Λ ⊢ⱽ ⊥ 🡒 A := ⟨ProofVF.efq⟩
@[simp, grind .] lemma verum : Λ ⊢ⱽ ⊤ := ⟨ProofVF.verum⟩
@[grind =>] lemma mdp : Λ ⊢ⱽ A 🡒 B → Λ ⊢ⱽ A → Λ ⊢ⱽ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVF.mdp h₁ h₂⟩
@[grind <=] lemma af : Λ ⊢ⱽ A → Λ ⊢ⱽ B 🡒 A := λ ⟨h⟩ => ⟨ProofVF.af h⟩
@[grind <=] lemma ruleC : Λ ⊢ⱽ A 🡒 B → Λ ⊢ⱽ A 🡒 C → Λ ⊢ⱽ A 🡒 (B ⋏ C) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVF.ruleC h₁ h₂⟩
@[grind <=] lemma ruleD : Λ ⊢ⱽ A 🡒 C → Λ ⊢ⱽ B 🡒 C → Λ ⊢ⱽ (A ⋎ B) 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVF.ruleD h₁ h₂⟩
@[grind =>] lemma ruleI : Λ ⊢ⱽ A 🡒 B → Λ ⊢ⱽ B 🡒 C → Λ ⊢ⱽ A 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVF.ruleI h₁ h₂⟩

@[grind <=] lemma orIntroRuleL : Λ ⊢ⱽ A → Λ ⊢ⱽ (A ⋎ B) := λ h => mdp orIntroL h
@[grind <=] lemma orIntroRuleR : Λ ⊢ⱽ B → Λ ⊢ⱽ (A ⋎ B) := λ h => mdp orIntroR h
@[grind <=] lemma andIntro : Λ ⊢ⱽ A → Λ ⊢ⱽ B → Λ ⊢ⱽ A ⋏ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVF.andIntro h₁ h₂⟩

lemma ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ⱽ A → Λ₂ ⊢ⱽ A := λ ⟨h⟩ => ⟨ProofVF.ofSubsetAxm hsub h⟩
lemma ofEmpty : ∅ ⊢ⱽ A → Λ ⊢ⱽ A := ofSubsetAxm (by grind)

lemma ruleI₃ : Λ ⊢ⱽ A 🡒 B → Λ ⊢ⱽ B 🡒 C → Λ ⊢ⱽ C 🡒 D → Λ ⊢ⱽ A 🡒 D := by
  intro hAB hBC hCD;
  exact ruleI (ruleI hAB hBC) hCD;

lemma distributeOrAnd : Λ ⊢ⱽ ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := ⟨ProofVF.distributeOrAnd⟩

lemma replaceAnd₂ (h : Λ ⊢ⱽ B 🡒 C) : Λ ⊢ⱽ (A ⋏ B) 🡒 (A ⋏ C) := by
  apply ruleC;
  . exact andElimL;
  . exact ruleI andElimR h;

lemma replaceOr₂ (h : Λ ⊢ⱽ B 🡒 C) : Λ ⊢ⱽ (A ⋎ B) 🡒 (A ⋎ C) := by
  apply ruleD;
  . exact orIntroL;
  . exact ruleI h orIntroR;


@[grind <=]
lemma lconj_of_mem {X : List (Formula α)} (h : A ∈ X) : Λ ⊢ⱽ ⋀X 🡒 A := by
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
lemma sconj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ⱽ ⋀X 🡒 A := lconj_of_mem (by simpa)


@[grind <=]
lemma ldisj_of_mem {X : List (Formula α)} (h : A ∈ X) : Λ ⊢ⱽ A 🡒 ⋁X := by
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
lemma sdisj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ⱽ A 🡒 ⋁X := ldisj_of_mem (by simpa)


lemma ldisj_insert {X : List (Formula α)} {A} : Λ ⊢ⱽ ⋁(A :: X) 🡒 (⋁X ⋎ A) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleD <;> simp;

lemma ldisj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : Λ ⊢ⱽ ⋁X 🡒 ⋁Y := by
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

lemma sdisj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ⱽ ⋁X 🡒 ⋁Y := ldisj_of_subset $ by intro A; simpa using @h A;

lemma sdisj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ⱽ ⋁(insert A X) 🡒 (⋁X ⋎ A) := by
  apply ruleI ?_ ldisj_insert;
  apply ldisj_of_subset;
  intro B;
  simp;


lemma lconj_insert {X : List (Formula α)} {A} : Λ ⊢ⱽ (⋀X ⋏ A) 🡒 ⋀(A :: X) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleC <;> simp;

lemma lconj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : Λ ⊢ⱽ ⋀Y 🡒 ⋀X := by
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

lemma sconj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ⱽ ⋀Y 🡒 ⋀X := lconj_of_subset $ by intro A; simpa using @h A;

lemma sconj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ⱽ (⋀X ⋏ A) 🡒 ⋀(insert A X) := by
  apply ruleI lconj_insert;
  apply lconj_of_subset;
  intro B;
  simp;


@[induction_eliminator]
protected lemma rec_provable
  {motive          : (A : Formula α) → (Λ ⊢ⱽ A) → Prop}
  (axm             : ∀ {A}, (h : A ∈ Λ) → motive A (axm h))
  (mdp             : ∀ {A B}, {hAB : Λ ⊢ⱽ A 🡒 B} → {hA : Λ ⊢ⱽ A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (af              : ∀ {A B}, {hA : Λ ⊢ⱽ A} → (motive A hA) → (motive (B 🡒 A) (af hA)))
  (ruleC           : ∀ {A B C}, {hAB : Λ ⊢ⱽ A 🡒 B} → {hAC : Λ ⊢ⱽ A 🡒 C} → (motive (A 🡒 B) hAB) → (motive (A 🡒 C) hAC) → (motive (A 🡒 (B ⋏ C)) (ruleC hAB hAC)))
  (ruleD           : ∀ {A B C}, {hAC : Λ ⊢ⱽ A 🡒 C} → {hBC : Λ ⊢ⱽ B 🡒 C} → (motive (A 🡒 C) hAC) → (motive (B 🡒 C) hBC) → (motive ((A ⋎ B) 🡒 C) (ruleD hAC hBC)))
  (ruleI           : ∀ {A B C}, {hAB : Λ ⊢ⱽ A 🡒 B} → {hBC : Λ ⊢ⱽ B 🡒 C} → (motive (A 🡒 B) hAB) → (motive (B 🡒 C) hBC) → (motive (A 🡒 C) (ruleI hAB hBC)))
  (distributeAndOr : ∀ {A B C : Formula α}, (motive ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) distributeAndOr))
  (impId           : ∀ {A}, (motive (A 🡒 A) impId))
  (andElimL        : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR        : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (orIntroL        : ∀ {A B}, (motive (A 🡒 (A ⋎ B)) orIntroL))
  (orIntroR        : ∀ {A B}, (motive (B 🡒 (A ⋎ B)) orIntroR))
  (efq             : ∀ {A}, (motive (⊥ 🡒 A) efq))
  : ∀ {A}, (d : Λ ⊢ⱽ A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end ProvableVF



class Axioms.ConsistentVF (Λ : Axioms α) : Prop where
  unprovable_bot : Λ ⊬ ⊥

namespace ProvableVF

export Axioms.ConsistentVF (unprovable_bot)
attribute [simp, grind .] unprovable_bot

end ProvableVF



section Disjunctive

class Axioms.DisjunctiveVF (Λ : Axioms α) : Prop where
  disjunctive : ∀ {A B}, (Λ ⊢ⱽ (A ⋎ B)) → (Λ ⊢ⱽ A) ∨ (Λ ⊢ⱽ B)

namespace ProvableVF

export Axioms.DisjunctiveVF (disjunctive)

variable {Λ : Axioms α} [Axioms.DisjunctiveVF Λ] {A B C : Formula α}

lemma ldisj_disjunctive {l : List _} (hl : l ≠ []) : Λ ⊢ⱽ ⋁l → ∃ B ∈ l, Λ ⊢ⱽ B := by
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

lemma sdisj_disjunctive {s : Finset _} (hs : s ≠ ∅) : Λ ⊢ⱽ ⋁s → ∃ B ∈ s, Λ ⊢ⱽ B := by
  intro h;
  simpa using ldisj_disjunctive (by simpa) h;

end ProvableVF

end Disjunctive
