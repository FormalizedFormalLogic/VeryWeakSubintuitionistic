module

public import VeryWeakSubintuitionistic.Propositional.Proof.Basic

@[expose] public section

variable {α : Type*}

inductive ProofVFR (Λ : Axioms α) : Formula α → Type _
| axm {A}                 : A ∈ Λ → ProofVFR Λ A
| andElimL {A B}          : ProofVFR Λ $ (A ⋏ B) 🡒 A
| andElimR {A B}          : ProofVFR Λ $ (A ⋏ B) 🡒 B
| orIntroL {A B}          : ProofVFR Λ $ A 🡒 (A ⋎ B)
| orIntroR {A B}          : ProofVFR Λ $ B 🡒 (A ⋎ B)
| distributeAndOr {A B C} : ProofVFR Λ $ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))
| impId {A}               : ProofVFR Λ $ A 🡒 A
| efq {A}                 : ProofVFR Λ $ ⊥ 🡒 A
| mdp {A B}               : ProofVFR Λ (A 🡒 B) → ProofVFR Λ A → ProofVFR Λ B
| af {A B}                : ProofVFR Λ A → ProofVFR Λ (B 🡒 A)
| ruleC {A B C}           : ProofVFR Λ (A 🡒 B) → ProofVFR Λ (A 🡒 C) → ProofVFR Λ (A 🡒 (B ⋏ C))
| ruleD {A B C}           : ProofVFR Λ (A 🡒 C) → ProofVFR Λ (B 🡒 C) → ProofVFR Λ ((A ⋎ B) 🡒 C)
| ruleI {A B C}           : ProofVFR Λ (A 🡒 B) → ProofVFR Λ (B 🡒 C) → ProofVFR Λ (A 🡒 C)
| ros {A B}               : ProofVFR Λ (∼A) → ProofVFR Λ B → ProofVFR Λ (∼(B 🡒 A))

infix:25 " ⊢ᴿ! " => ProofVFR

namespace ProofVFR

variable {Λ Λ₁ Λ₂ : Axioms α} {A B C : Formula α}

def andComm : Λ ⊢ᴿ! (A ⋏ B) 🡒 (B ⋏ A) := ruleC andElimR andElimL
def orComm  : Λ ⊢ᴿ! (A ⋎ B) 🡒 (B ⋎ A) := ruleD orIntroR orIntroL

def distributeOrAnd : Λ ⊢ᴿ! ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := by
  letI D := A ⋎ (B ⋏ C);
  haveI P₁ : Λ ⊢ᴿ! ((A ⋎ B) ⋏ A) 🡒 D := ruleI andElimR orIntroL
  haveI P₂ : Λ ⊢ᴿ! ((A ⋎ B) ⋏ C) 🡒 ((C ⋏ A) ⋎ (C ⋏ B)) := ruleI andComm distributeAndOr
  haveI P₃ : Λ ⊢ᴿ! (C ⋏ A) 🡒 D := ruleI andElimR orIntroL;
  haveI P₄ : Λ ⊢ᴿ! (C ⋏ B) 🡒 D := ruleI andComm orIntroR;
  haveI P₅ : Λ ⊢ᴿ! ((C ⋏ A) ⋎ (C ⋏ B)) 🡒 D := ruleD P₃ P₄;
  haveI P₆ : Λ ⊢ᴿ! ((A ⋎ B) ⋏ C) 🡒 D := ruleI P₂ P₅;
  haveI P₇ : Λ ⊢ᴿ! ((A ⋎ B) ⋏ A ⋎ (A ⋎ B) ⋏ C) 🡒 D := ruleD P₁ P₆;
  exact ruleI distributeAndOr P₇;

def verum : Λ ⊢ᴿ! ⊤ := impId

def orIntroRuleL : Λ ⊢ᴿ! A → Λ ⊢ᴿ! (A ⋎ B) := λ h => mdp orIntroL h
def orIntroRuleR : Λ ⊢ᴿ! B → Λ ⊢ᴿ! (A ⋎ B) := λ h => mdp orIntroR h

def andIntro : Λ ⊢ᴿ! A → Λ ⊢ᴿ! B → Λ ⊢ᴿ! A ⋏ B := λ h₁ h₂ => mdp (ruleC (af h₁) (af h₂)) (verum)

noncomputable def ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ᴿ! A → Λ₂ ⊢ᴿ! A := λ h => by
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
  | ros _ _ ihA ihB => exact ros ihA ihB

end ProofVFR


abbrev ProvableVFR (Λ : Axioms α) (A : Formula α) : Prop := Nonempty (Λ ⊢ᴿ! A)
infix:25 " ⊢ᴿ " => ProvableVFR

abbrev UnprovableVFR (Λ : Axioms α) (A : Formula α) : Prop := ¬(Λ ⊢ᴿ A)
infix:25 " ⊬ᴿ " => UnprovableVFR

namespace ProvableVFR

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ Λ → Λ ⊢ᴿ A := λ h => ⟨ProofVFR.axm h⟩
@[simp, grind .] lemma andElimL : Λ ⊢ᴿ (A ⋏ B) 🡒 A := ⟨ProofVFR.andElimL⟩
@[simp, grind .] lemma andElimR : Λ ⊢ᴿ (A ⋏ B) 🡒 B := ⟨ProofVFR.andElimR⟩
@[simp, grind .] lemma orIntroL : Λ ⊢ᴿ A 🡒 (A ⋎ B) := ⟨ProofVFR.orIntroL⟩
@[simp, grind .] lemma orIntroR : Λ ⊢ᴿ B 🡒 (A ⋎ B) := ⟨ProofVFR.orIntroR⟩
@[simp, grind .] lemma distributeAndOr : Λ ⊢ᴿ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := ⟨ProofVFR.distributeAndOr⟩
@[simp, grind .] lemma impId : Λ ⊢ᴿ A 🡒 A := ⟨ProofVFR.impId⟩
@[simp, grind .] lemma efq : Λ ⊢ᴿ ⊥ 🡒 A := ⟨ProofVFR.efq⟩
@[simp, grind .] lemma verum : Λ ⊢ᴿ ⊤ := ⟨ProofVFR.verum⟩
@[grind =>] lemma mdp : Λ ⊢ᴿ A 🡒 B → Λ ⊢ᴿ A → Λ ⊢ᴿ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVFR.mdp h₁ h₂⟩
@[grind <=] lemma af : Λ ⊢ᴿ A → Λ ⊢ᴿ B 🡒 A := λ ⟨h⟩ => ⟨ProofVFR.af h⟩
@[grind <=] lemma ruleC : Λ ⊢ᴿ A 🡒 B → Λ ⊢ᴿ A 🡒 C → Λ ⊢ᴿ A 🡒 (B ⋏ C) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVFR.ruleC h₁ h₂⟩
@[grind <=] lemma ruleD : Λ ⊢ᴿ A 🡒 C → Λ ⊢ᴿ B 🡒 C → Λ ⊢ᴿ (A ⋎ B) 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVFR.ruleD h₁ h₂⟩
@[grind =>] lemma ruleI : Λ ⊢ᴿ A 🡒 B → Λ ⊢ᴿ B 🡒 C → Λ ⊢ᴿ A 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVFR.ruleI h₁ h₂⟩
@[grind <=] lemma ros : Λ ⊢ᴿ ∼A → Λ ⊢ᴿ B → Λ ⊢ᴿ ∼(B 🡒 A) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVFR.ros h₁ h₂⟩

@[grind <=] lemma orIntroRuleL : Λ ⊢ᴿ A → Λ ⊢ᴿ (A ⋎ B) := λ h => mdp orIntroL h
@[grind <=] lemma orIntroRuleR : Λ ⊢ᴿ B → Λ ⊢ᴿ (A ⋎ B) := λ h => mdp orIntroR h
@[grind <=] lemma andIntro : Λ ⊢ᴿ A → Λ ⊢ᴿ B → Λ ⊢ᴿ A ⋏ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofVFR.andIntro h₁ h₂⟩

lemma ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ᴿ A → Λ₂ ⊢ᴿ A := λ ⟨h⟩ => ⟨ProofVFR.ofSubsetAxm hsub h⟩
lemma ofEmpty : ∅ ⊢ᴿ A → Λ ⊢ᴿ A := ofSubsetAxm (by grind)

lemma ruleI₃ : Λ ⊢ᴿ A 🡒 B → Λ ⊢ᴿ B 🡒 C → Λ ⊢ᴿ C 🡒 D → Λ ⊢ᴿ A 🡒 D := by
  intro hAB hBC hCD;
  exact ruleI (ruleI hAB hBC) hCD;

lemma distributeOrAnd : Λ ⊢ᴿ ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := ⟨ProofVFR.distributeOrAnd⟩

lemma replaceAnd₂ (h : Λ ⊢ᴿ B 🡒 C) : Λ ⊢ᴿ (A ⋏ B) 🡒 (A ⋏ C) := by
  apply ruleC;
  . exact andElimL;
  . exact ruleI andElimR h;

lemma replaceOr₂ (h : Λ ⊢ᴿ B 🡒 C) : Λ ⊢ᴿ (A ⋎ B) 🡒 (A ⋎ C) := by
  apply ruleD;
  . exact orIntroL;
  . exact ruleI h orIntroR;


@[grind <=]
lemma lconj_of_mem {X : List (Formula α)} (h : A ∈ X) : Λ ⊢ᴿ ⋀X 🡒 A := by
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
lemma sconj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ᴿ ⋀X 🡒 A := lconj_of_mem (by simpa)


@[grind <=]
lemma ldisj_of_mem {X : List (Formula α)} (h : A ∈ X) : Λ ⊢ᴿ A 🡒 ⋁X := by
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
lemma sdisj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : Λ ⊢ᴿ A 🡒 ⋁X := ldisj_of_mem (by simpa)


lemma ldisj_insert {X : List (Formula α)} {A} : Λ ⊢ᴿ ⋁(A :: X) 🡒 (⋁X ⋎ A) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleD <;> simp;

lemma ldisj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : Λ ⊢ᴿ ⋁X 🡒 ⋁Y := by
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

lemma sdisj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ᴿ ⋁X 🡒 ⋁Y := ldisj_of_subset $ by intro A; simpa using @h A;

lemma sdisj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ᴿ ⋁(insert A X) 🡒 (⋁X ⋎ A) := by
  apply ruleI ?_ ldisj_insert;
  apply ldisj_of_subset;
  intro B;
  simp;


lemma lconj_insert {X : List (Formula α)} {A} : Λ ⊢ᴿ (⋀X ⋏ A) 🡒 ⋀(A :: X) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleC <;> simp;

lemma lconj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : Λ ⊢ᴿ ⋀Y 🡒 ⋀X := by
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

lemma sconj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : Λ ⊢ᴿ ⋀Y 🡒 ⋀X := lconj_of_subset $ by intro A; simpa using @h A;

lemma sconj_insert [DecidableEq α] {X : Finset (Formula α)} : Λ ⊢ᴿ (⋀X ⋏ A) 🡒 ⋀(insert A X) := by
  apply ruleI lconj_insert;
  apply lconj_of_subset;
  intro B;
  simp;


@[induction_eliminator]
protected lemma rec_provable
  {motive          : (A : Formula α) → (Λ ⊢ᴿ A) → Prop}
  (axm             : ∀ {A}, (h : A ∈ Λ) → motive A (axm h))
  (mdp             : ∀ {A B}, {hAB : Λ ⊢ᴿ A 🡒 B} → {hA : Λ ⊢ᴿ A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (af              : ∀ {A B}, {hA : Λ ⊢ᴿ A} → (motive A hA) → (motive (B 🡒 A) (af hA)))
  (ruleC           : ∀ {A B C}, {hAB : Λ ⊢ᴿ A 🡒 B} → {hAC : Λ ⊢ᴿ A 🡒 C} → (motive (A 🡒 B) hAB) → (motive (A 🡒 C) hAC) → (motive (A 🡒 (B ⋏ C)) (ruleC hAB hAC)))
  (ruleD           : ∀ {A B C}, {hAC : Λ ⊢ᴿ A 🡒 C} → {hBC : Λ ⊢ᴿ B 🡒 C} → (motive (A 🡒 C) hAC) → (motive (B 🡒 C) hBC) → (motive ((A ⋎ B) 🡒 C) (ruleD hAC hBC)))
  (ruleI           : ∀ {A B C}, {hAB : Λ ⊢ᴿ A 🡒 B} → {hBC : Λ ⊢ᴿ B 🡒 C} → (motive (A 🡒 B) hAB) → (motive (B 🡒 C) hBC) → (motive (A 🡒 C) (ruleI hAB hBC)))
  (ros             : ∀ {A B}, {hA : Λ ⊢ᴿ ∼A} → {hB : Λ ⊢ᴿ B} → (motive (∼A) hA) → (motive B hB) → (motive (∼(B 🡒 A)) (ros hA hB)))
  (distributeAndOr : ∀ {A B C : Formula α}, (motive ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) distributeAndOr))
  (impId           : ∀ {A}, (motive (A 🡒 A) impId))
  (andElimL        : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR        : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (orIntroL        : ∀ {A B}, (motive (A 🡒 (A ⋎ B)) orIntroL))
  (orIntroR        : ∀ {A B}, (motive (B 🡒 (A ⋎ B)) orIntroR))
  (efq             : ∀ {A}, (motive (⊥ 🡒 A) efq))
  : ∀ {A}, (d : Λ ⊢ᴿ A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end ProvableVFR



class Axioms.ConsistentVFR (Λ : Axioms α) : Prop where
  unprovable_bot : Λ ⊬ᴿ ⊥

namespace ProvableVFR

export Axioms.ConsistentVFR (unprovable_bot)
attribute [simp, grind .] unprovable_bot

end ProvableVFR



section Disjunctive

class Axioms.DisjunctiveVFR (Λ : Axioms α) : Prop where
  disjunctive : ∀ {A B}, (Λ ⊢ᴿ (A ⋎ B)) → (Λ ⊢ᴿ A) ∨ (Λ ⊢ᴿ B)

namespace ProvableVFR

export Axioms.DisjunctiveVFR (disjunctive)

variable {Λ : Axioms α} [Axioms.DisjunctiveVFR Λ] {A B C : Formula α}

lemma ldisj_disjunctive {l : List _} (hl : l ≠ []) : Λ ⊢ᴿ ⋁l → ∃ B ∈ l, Λ ⊢ᴿ B := by
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

lemma sdisj_disjunctive {s : Finset _} (hs : s ≠ ∅) : Λ ⊢ᴿ ⋁s → ∃ B ∈ s, Λ ⊢ᴿ B := by
  intro h;
  simpa using ldisj_disjunctive (by simpa) h;

end ProvableVFR

end Disjunctive
