module

public import VeryWeakSubintuitionistic.Propositional.Proof.VF

@[expose] public section

variable {α : Type*}

namespace VFR

inductive ProofHilbert (𝔸 : Axioms α) : Formula α → Type _
| axm {A}                 : A ∈ 𝔸 → ProofHilbert 𝔸 A
| andElimL {A B}          : ProofHilbert 𝔸 $ (A ⋏ B) 🡒 A
| andElimR {A B}          : ProofHilbert 𝔸 $ (A ⋏ B) 🡒 B
| orIntroL {A B}          : ProofHilbert 𝔸 $ A 🡒 (A ⋎ B)
| orIntroR {A B}          : ProofHilbert 𝔸 $ B 🡒 (A ⋎ B)
| distributeAndOr {A B C} : ProofHilbert 𝔸 $ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))
| impId {A}               : ProofHilbert 𝔸 $ A 🡒 A
| efq {A}                 : ProofHilbert 𝔸 $ ⊥ 🡒 A
| mdp {A B}               : ProofHilbert 𝔸 (A 🡒 B) → ProofHilbert 𝔸 A → ProofHilbert 𝔸 B
| af {A B}                : ProofHilbert 𝔸 A → ProofHilbert 𝔸 (B 🡒 A)
| ruleC {A B C}           : ProofHilbert 𝔸 (A 🡒 B) → ProofHilbert 𝔸 (A 🡒 C) → ProofHilbert 𝔸 (A 🡒 (B ⋏ C))
| ruleD {A B C}           : ProofHilbert 𝔸 (A 🡒 C) → ProofHilbert 𝔸 (B 🡒 C) → ProofHilbert 𝔸 ((A ⋎ B) 🡒 C)
| ruleI {A B C}           : ProofHilbert 𝔸 (A 🡒 B) → ProofHilbert 𝔸 (B 🡒 C) → ProofHilbert 𝔸 (A 🡒 C)
| ros {A B}               : ProofHilbert 𝔸 (∼A) → ProofHilbert 𝔸 B → ProofHilbert 𝔸 (∼(B 🡒 A))

notation:50 "⊢ʰ![VFR;" 𝔸 "] " A:51 => VFR.ProofHilbert 𝔸 A

namespace ProofHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C : Formula α}

def andComm : ⊢ʰ![VFR;𝔸] ((A ⋏ B) 🡒 (B ⋏ A)) := ruleC andElimR andElimL
def orComm  : ⊢ʰ![VFR;𝔸] ((A ⋎ B) 🡒 (B ⋎ A)) := ruleD orIntroR orIntroL

def distributeOrAnd : ⊢ʰ![VFR;𝔸] (((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C))) := by
  letI D := A ⋎ (B ⋏ C);
  haveI P₁ : ⊢ʰ![VFR;𝔸] (((A ⋎ B) ⋏ A) 🡒 D) := ruleI andElimR orIntroL
  haveI P₂ : ⊢ʰ![VFR;𝔸] (((A ⋎ B) ⋏ C) 🡒 ((C ⋏ A) ⋎ (C ⋏ B))) := ruleI andComm distributeAndOr
  haveI P₃ : ⊢ʰ![VFR;𝔸] ((C ⋏ A) 🡒 D) := ruleI andElimR orIntroL;
  haveI P₄ : ⊢ʰ![VFR;𝔸] ((C ⋏ B) 🡒 D) := ruleI andComm orIntroR;
  haveI P₅ : ⊢ʰ![VFR;𝔸] (((C ⋏ A) ⋎ (C ⋏ B)) 🡒 D) := ruleD P₃ P₄;
  haveI P₆ : ⊢ʰ![VFR;𝔸] (((A ⋎ B) ⋏ C) 🡒 D) := ruleI P₂ P₅;
  haveI P₇ : ⊢ʰ![VFR;𝔸] (((A ⋎ B) ⋏ A ⋎ (A ⋎ B) ⋏ C) 🡒 D) := ruleD P₁ P₆;
  exact ruleI distributeAndOr P₇;

def verum : ⊢ʰ![VFR;𝔸] (⊤ : Formula α) := impId

def orIntroRuleL : ⊢ʰ![VFR;𝔸] A → ⊢ʰ![VFR;𝔸] (A ⋎ B) := λ h => mdp orIntroL h
def orIntroRuleR : ⊢ʰ![VFR;𝔸] B → ⊢ʰ![VFR;𝔸] (A ⋎ B) := λ h => mdp orIntroR h

def andIntro : ⊢ʰ![VFR;𝔸] A → ⊢ʰ![VFR;𝔸] B → ⊢ʰ![VFR;𝔸] (A ⋏ B) := λ h₁ h₂ => mdp (ruleC (af h₁) (af h₂)) (verum)

noncomputable def ofSubsetAxm (hsub : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ![VFR;𝔸₁] A) → ⊢ʰ![VFR;𝔸₂] A := λ h => by
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

noncomputable def ofProofHilbertVF : (⊢ʰ![VF;𝔸] A) → ⊢ʰ![VFR;𝔸] A := λ h => by
  induction h with
  | axm h => exact axm h
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

end ProofHilbert


abbrev ProvableHilbert (𝔸 : Axioms α) (A : Formula α) : Prop := Nonempty (⊢ʰ![VFR;𝔸] A)

end VFR

notation:50 "⊢ʰ[VFR;" 𝔸 "] " A:51 => VFR.ProvableHilbert 𝔸 A
notation:50 "⊬ʰ[VFR;" 𝔸 "] " A:51 => ¬(VFR.ProvableHilbert 𝔸 A)

namespace VFR.ProvableHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ 𝔸 → ⊢ʰ[VFR;𝔸] A := λ h => ⟨ProofHilbert.axm h⟩
@[simp, grind .] lemma andElimL : ⊢ʰ[VFR;𝔸] (A ⋏ B) 🡒 A := ⟨ProofHilbert.andElimL⟩
@[simp, grind .] lemma andElimR : ⊢ʰ[VFR;𝔸] (A ⋏ B) 🡒 B := ⟨ProofHilbert.andElimR⟩
@[simp, grind .] lemma orIntroL : ⊢ʰ[VFR;𝔸] A 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroL⟩
@[simp, grind .] lemma orIntroR : ⊢ʰ[VFR;𝔸] B 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroR⟩
@[simp, grind .] lemma distributeAndOr : ⊢ʰ[VFR;𝔸] (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := ⟨ProofHilbert.distributeAndOr⟩
@[simp, grind .] lemma impId : ⊢ʰ[VFR;𝔸] A 🡒 A := ⟨ProofHilbert.impId⟩
@[simp, grind .] lemma efq : ⊢ʰ[VFR;𝔸] ⊥ 🡒 A := ⟨ProofHilbert.efq⟩
@[simp, grind .] lemma verum : ⊢ʰ[VFR;𝔸] (⊤ : Formula α) := ⟨ProofHilbert.verum⟩
@[grind =>] lemma mdp : (⊢ʰ[VFR;𝔸] A 🡒 B) → (⊢ʰ[VFR;𝔸] A) → ⊢ʰ[VFR;𝔸] B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[grind <=] lemma af : (⊢ʰ[VFR;𝔸] A) → ⊢ʰ[VFR;𝔸] B 🡒 A := λ ⟨h⟩ => ⟨ProofHilbert.af h⟩
@[grind <=] lemma ruleC : (⊢ʰ[VFR;𝔸] A 🡒 B) → (⊢ʰ[VFR;𝔸] A 🡒 C) → ⊢ʰ[VFR;𝔸] A 🡒 (B ⋏ C) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.ruleC h₁ h₂⟩
@[grind <=] lemma ruleD : (⊢ʰ[VFR;𝔸] A 🡒 C) → (⊢ʰ[VFR;𝔸] B 🡒 C) → ⊢ʰ[VFR;𝔸] (A ⋎ B) 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.ruleD h₁ h₂⟩
@[grind =>] lemma ruleI : (⊢ʰ[VFR;𝔸] A 🡒 B) → (⊢ʰ[VFR;𝔸] B 🡒 C) → ⊢ʰ[VFR;𝔸] A 🡒 C := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.ruleI h₁ h₂⟩
@[grind <=] lemma ros : (⊢ʰ[VFR;𝔸] ∼A) → (⊢ʰ[VFR;𝔸] B) → ⊢ʰ[VFR;𝔸] ∼(B 🡒 A) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.ros h₁ h₂⟩

@[grind <=] lemma orIntroRuleL : (⊢ʰ[VFR;𝔸] A) → ⊢ʰ[VFR;𝔸] (A ⋎ B) := λ h => mdp orIntroL h
@[grind <=] lemma orIntroRuleR : (⊢ʰ[VFR;𝔸] B) → ⊢ʰ[VFR;𝔸] (A ⋎ B) := λ h => mdp orIntroR h
@[grind <=] lemma andIntro : (⊢ʰ[VFR;𝔸] A) → (⊢ʰ[VFR;𝔸] B) → ⊢ʰ[VFR;𝔸] A ⋏ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.andIntro h₁ h₂⟩

lemma ofSubsetAxm (hsub : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ[VFR;𝔸₁] A) → ⊢ʰ[VFR;𝔸₂] A := λ ⟨h⟩ => ⟨ProofHilbert.ofSubsetAxm hsub h⟩
lemma ofEmpty : (⊢ʰ[VFR;∅] A) → ⊢ʰ[VFR;𝔸] A := ofSubsetAxm (by grind)

@[grind =>] lemma ofProvableVF : (⊢ʰ[VF;𝔸] A) → ⊢ʰ[VFR;𝔸] A := λ ⟨h⟩ => ⟨ProofHilbert.ofProofHilbertVF h⟩

lemma ruleI₃ : (⊢ʰ[VFR;𝔸] A 🡒 B) → (⊢ʰ[VFR;𝔸] B 🡒 C) → (⊢ʰ[VFR;𝔸] C 🡒 D) → ⊢ʰ[VFR;𝔸] A 🡒 D := by
  intro hAB hBC hCD;
  exact ruleI (ruleI hAB hBC) hCD;

lemma distributeOrAnd : ⊢ʰ[VFR;𝔸] ((A ⋎ B) ⋏ (A ⋎ C)) 🡒 (A ⋎ (B ⋏ C)) := ⟨ProofHilbert.distributeOrAnd⟩

lemma dnVerum : ⊢ʰ[VFR;𝔸] ∼∼⊤ := ros impId verum

lemma replaceAnd₂ (h : ⊢ʰ[VFR;𝔸] B 🡒 C) : ⊢ʰ[VFR;𝔸] (A ⋏ B) 🡒 (A ⋏ C) := by
  apply ruleC;
  . exact andElimL;
  . exact ruleI andElimR h;

lemma replaceOr₂ (h : ⊢ʰ[VFR;𝔸] B 🡒 C) : ⊢ʰ[VFR;𝔸] (A ⋎ B) 🡒 (A ⋎ C) := by
  apply ruleD;
  . exact orIntroL;
  . exact ruleI h orIntroR;


@[grind <=]
lemma lconj_of_mem {X : List (Formula α)} (h : A ∈ X) : ⊢ʰ[VFR;𝔸] ⋀X 🡒 A := by
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
lemma sconj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : ⊢ʰ[VFR;𝔸] ⋀X 🡒 A := lconj_of_mem (by simpa)


@[grind <=]
lemma ldisj_of_mem {X : List (Formula α)} (h : A ∈ X) : ⊢ʰ[VFR;𝔸] A 🡒 ⋁X := by
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
lemma sdisj_of_mem {X : Finset (Formula α)} (h : A ∈ X) : ⊢ʰ[VFR;𝔸] A 🡒 ⋁X := ldisj_of_mem (by simpa)


lemma ldisj_insert {X : List (Formula α)} {A} : ⊢ʰ[VFR;𝔸] ⋁(A :: X) 🡒 (⋁X ⋎ A) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleD <;> simp;

lemma ldisj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : ⊢ʰ[VFR;𝔸] ⋁X 🡒 ⋁Y := by
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

lemma sdisj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : ⊢ʰ[VFR;𝔸] ⋁X 🡒 ⋁Y := ldisj_of_subset $ by intro A; simpa using @h A;

lemma sdisj_insert [DecidableEq α] {X : Finset (Formula α)} : ⊢ʰ[VFR;𝔸] ⋁(insert A X) 🡒 (⋁X ⋎ A) := by
  apply ruleI ?_ ldisj_insert;
  apply ldisj_of_subset;
  intro B;
  simp;


lemma lconj_insert {X : List (Formula α)} {A} : ⊢ʰ[VFR;𝔸] (⋀X ⋏ A) 🡒 ⋀(A :: X) := by
  match X with
  | [] | [B] => grind;
  | B :: X => apply ruleC <;> simp;

lemma lconj_of_subset {X Y : List (Formula α)} (h : X ⊆ Y) : ⊢ʰ[VFR;𝔸] ⋀Y 🡒 ⋀X := by
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

lemma sconj_of_subset {X Y : Finset (Formula α)} (h : X ⊆ Y) : ⊢ʰ[VFR;𝔸] ⋀Y 🡒 ⋀X := lconj_of_subset $ by intro A; simpa using @h A;

lemma sconj_insert [DecidableEq α] {X : Finset (Formula α)} : ⊢ʰ[VFR;𝔸] (⋀X ⋏ A) 🡒 ⋀(insert A X) := by
  apply ruleI lconj_insert;
  apply lconj_of_subset;
  intro B;
  simp;


@[induction_eliminator]
protected lemma rec_provable
  {motive          : (A : Formula α) → (⊢ʰ[VFR;𝔸] A) → Prop}
  (axm             : ∀ {A}, (h : A ∈ 𝔸) → motive A (axm h))
  (mdp             : ∀ {A B}, {hAB : ⊢ʰ[VFR;𝔸] A 🡒 B} → {hA : ⊢ʰ[VFR;𝔸] A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (af              : ∀ {A B}, {hA : ⊢ʰ[VFR;𝔸] A} → (motive A hA) → (motive (B 🡒 A) (af hA)))
  (ruleC           : ∀ {A B C}, {hAB : ⊢ʰ[VFR;𝔸] A 🡒 B} → {hAC : ⊢ʰ[VFR;𝔸] A 🡒 C} → (motive (A 🡒 B) hAB) → (motive (A 🡒 C) hAC) → (motive (A 🡒 (B ⋏ C)) (ruleC hAB hAC)))
  (ruleD           : ∀ {A B C}, {hAC : ⊢ʰ[VFR;𝔸] A 🡒 C} → {hBC : ⊢ʰ[VFR;𝔸] B 🡒 C} → (motive (A 🡒 C) hAC) → (motive (B 🡒 C) hBC) → (motive ((A ⋎ B) 🡒 C) (ruleD hAC hBC)))
  (ruleI           : ∀ {A B C}, {hAB : ⊢ʰ[VFR;𝔸] A 🡒 B} → {hBC : ⊢ʰ[VFR;𝔸] B 🡒 C} → (motive (A 🡒 B) hAB) → (motive (B 🡒 C) hBC) → (motive (A 🡒 C) (ruleI hAB hBC)))
  (ros             : ∀ {A B}, {hA : ⊢ʰ[VFR;𝔸] ∼A} → {hB : ⊢ʰ[VFR;𝔸] B} → (motive (∼A) hA) → (motive B hB) → (motive (∼(B 🡒 A)) (ros hA hB)))
  (distributeAndOr : ∀ {A B C : Formula α}, (motive ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) distributeAndOr))
  (impId           : ∀ {A}, (motive (A 🡒 A) impId))
  (andElimL        : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR        : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (orIntroL        : ∀ {A B}, (motive (A 🡒 (A ⋎ B)) orIntroL))
  (orIntroR        : ∀ {A B}, (motive (B 🡒 (A ⋎ B)) orIntroR))
  (efq             : ∀ {A}, (motive (⊥ 🡒 A) efq))
  : ∀ {A}, (d : ⊢ʰ[VFR;𝔸] A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end VFR.ProvableHilbert



namespace VFR

class Consistent (𝔸 : Axioms α) : Prop where
  unprovable_bot : ⊬ʰ[VFR;𝔸] ⊥

namespace ProvableHilbert

export Consistent (unprovable_bot)
attribute [simp, grind .] unprovable_bot

end ProvableHilbert



section Disjunctive

class Disjunctive (𝔸 : Axioms α) : Prop where
  disjunctive : ∀ {A B}, (⊢ʰ[VFR;𝔸] (A ⋎ B)) → (⊢ʰ[VFR;𝔸] A) ∨ (⊢ʰ[VFR;𝔸] B)

namespace ProvableHilbert

export Disjunctive (disjunctive)

variable {𝔸 : Axioms α} [Disjunctive 𝔸] {A B C : Formula α}

lemma ldisj_disjunctive {l : List _} (hl : l ≠ []) : (⊢ʰ[VFR;𝔸] ⋁l) → ∃ B ∈ l, ⊢ʰ[VFR;𝔸] B := by
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

lemma sdisj_disjunctive {s : Finset _} (hs : s ≠ ∅) : (⊢ʰ[VFR;𝔸] ⋁s) → ∃ B ∈ s, ⊢ʰ[VFR;𝔸] B := by
  intro h;
  simpa using ldisj_disjunctive (by simpa) h;

end ProvableHilbert

end Disjunctive

end VFR
