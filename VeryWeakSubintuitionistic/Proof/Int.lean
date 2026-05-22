module

public import VeryWeakSubintuitionistic.Proof.VF

@[expose] public section

variable {α : Type*}

inductive ProofInt (Λ : Axioms α) : Formula α → Type _
| axm {A}                 : A ∈ Λ → ProofInt Λ A
| andElimL {A B}          : ProofInt Λ $ (A ⋏ B) 🡒 A
| andElimR {A B}          : ProofInt Λ $ (A ⋏ B) 🡒 B
| andIntro {A B}          : ProofInt Λ $ (A 🡒 B 🡒 (A ⋏ B))
| orIntroL {A B}          : ProofInt Λ $ A 🡒 (A ⋎ B)
| orIntroR {A B}          : ProofInt Λ $ B 🡒 (A ⋎ B)
| orElim {A B C}          : ProofInt Λ $ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)
| implyK {A B}            : ProofInt Λ $ A 🡒 B 🡒 A
| implyS {A B C}          : ProofInt Λ $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| verum                   : ProofInt Λ $ ⊤
| efq {A}                 : ProofInt Λ $ ⊥ 🡒 A
| mdp {A B}               : ProofInt Λ (A 🡒 B) → ProofInt Λ A → ProofInt Λ B
infix:25 " ⊢ᴵ! " => ProofInt

namespace ProofInt

variable {Λ Λ₁ Λ₂ : Axioms α} {A B C : Formula α}

def af {A B} : Λ ⊢ᴵ! A → Λ ⊢ᴵ! (B 🡒 A) := λ h => mdp implyK h

def impId : Λ ⊢ᴵ! A 🡒 A := by
  haveI : Λ ⊢ᴵ! (A 🡒 (A 🡒 A) 🡒 A) 🡒 (A 🡒 A 🡒 A) 🡒 (A 🡒 A) := implyS;
  haveI : Λ ⊢ᴵ! (A 🡒 A 🡒 A) 🡒 (A 🡒 A) := mdp this implyK;
  haveI : Λ ⊢ᴵ! A 🡒 A := mdp this implyK;
  exact this;

def andElimRuleL : Λ ⊢ᴵ! A ⋏ B → Λ ⊢ᴵ! A := λ h => mdp andElimL h
def andElimRuleR : Λ ⊢ᴵ! A ⋏ B → Λ ⊢ᴵ! B := λ h => mdp andElimR h

noncomputable def ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ᴵ! A → Λ₂ ⊢ᴵ! A := λ h => by
  induction h with
  | axm h₁ => exact axm (hsub h₁)
  | andElimL => exact andElimL
  | andElimR => exact andElimR
  | andIntro => exact andIntro
  | orIntroL => exact orIntroL
  | orIntroR => exact orIntroR
  | orElim => exact orElim
  | implyK => exact implyK
  | implyS => exact implyS
  | verum => exact verum
  | efq => exact efq
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA

end ProofInt



abbrev ProvableInt (Λ : Axioms α) (A : Formula α) : Prop := Nonempty (Λ ⊢ᴵ! A)
infix:25 " ⊢ᴵ " => ProvableInt

abbrev UnprovableInt (Λ : Axioms α) (A : Formula α) : Prop := ¬(Λ ⊢ᴵ A)
infix:25 " ⊬ᴵ " => UnprovableInt

namespace ProvableInt

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ Λ → Λ ⊢ᴵ A := λ h => ⟨ProofInt.axm h⟩
@[simp, grind .] lemma implyK : Λ ⊢ᴵ A 🡒 B 🡒 A := ⟨ProofInt.implyK⟩
@[simp, grind .] lemma implyS : Λ ⊢ᴵ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofInt.implyS⟩
@[simp, grind .] lemma andElimL : Λ ⊢ᴵ (A ⋏ B) 🡒 A := ⟨ProofInt.andElimL⟩
@[simp, grind .] lemma andElimR : Λ ⊢ᴵ (A ⋏ B) 🡒 B := ⟨ProofInt.andElimR⟩
@[simp, grind .] lemma andIntro : Λ ⊢ᴵ (A 🡒 B 🡒 (A ⋏ B)) := ⟨ProofInt.andIntro⟩
@[simp, grind .] lemma orIntroL : Λ ⊢ᴵ A 🡒 (A ⋎ B) := ⟨ProofInt.orIntroL⟩
@[simp, grind .] lemma orIntroR : Λ ⊢ᴵ B 🡒 (A ⋎ B) := ⟨ProofInt.orIntroR⟩
@[simp, grind .] lemma orElim : Λ ⊢ᴵ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := ⟨ProofInt.orElim⟩
@[simp, grind .] lemma efq : Λ ⊢ᴵ ⊥ 🡒 A := ⟨ProofInt.efq⟩
@[simp, grind .] lemma verum : Λ ⊢ᴵ ⊤ := ⟨ProofInt.verum⟩
@[simp, grind .] lemma impId : Λ ⊢ᴵ A 🡒 A := ⟨ProofInt.impId⟩
@[grind =>] lemma mdp : Λ ⊢ᴵ A 🡒 B → Λ ⊢ᴵ A → Λ ⊢ᴵ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofInt.mdp h₁ h₂⟩
@[grind <=] lemma af : Λ ⊢ᴵ A → Λ ⊢ᴵ B 🡒 A := λ ⟨h⟩ => ⟨ProofInt.af h⟩

@[grind =>] lemma andElimRuleL : Λ ⊢ᴵ A ⋏ B → Λ ⊢ᴵ A := λ h => mdp andElimL h
@[grind =>] lemma andElimRuleR : Λ ⊢ᴵ A ⋏ B → Λ ⊢ᴵ B := λ h => mdp andElimR h

end ProvableInt


inductive IntDeduction (Λ : Axioms α) : Set (Formula α) → Formula α → Type _
| ofProof {X A} : ProofInt Λ A → IntDeduction Λ X A
| ofContext {X A} : A ∈ X → IntDeduction Λ X A
| mdp {X A B} : (IntDeduction Λ X (A 🡒 B)) → (IntDeduction Λ X A) → (IntDeduction Λ X B)
notation:25 X " ⊢ᴵ[" Λ "]! " A => IntDeduction Λ X A

abbrev IntDeducible (Λ : Axioms α) (X : Set (Formula α)) (A : Formula α) : Prop := Nonempty (X ⊢ᴵ[Λ]! A)
notation:25 X " ⊢ᴵ[" Λ "] " A => IntDeducible Λ X A

namespace IntDeducible

variable {Λ : Axioms α} {X : Set (Formula α)} {A B C : Formula α}

@[grind <=] lemma ofProvable {X A} : Λ ⊢ᴵ A → X ⊢ᴵ[Λ] A := λ ⟨h⟩ => ⟨IntDeduction.ofProof h⟩
@[grind <=] lemma ofContext {X A} : A ∈ X → X ⊢ᴵ[Λ] A := λ h => ⟨IntDeduction.ofContext h⟩
@[grind =>] lemma mdp {X A B} : (X ⊢ᴵ[Λ] A 🡒 B) → (X ⊢ᴵ[Λ] A) → (X ⊢ᴵ[Λ] B) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨IntDeduction.mdp h₁ h₂⟩

@[induction_eliminator]
protected lemma rec
  {motive : (X : Set (Formula α)) → (A : Formula α) → (X ⊢ᴵ[Λ] A) → Prop}
  (ofProvable : ∀ {X A}, (h : Λ ⊢ᴵ A) → motive X A (ofProvable h))
  (ofContext : ∀ {X A}, (h : A ∈ X) → motive X A (ofContext h))
  (mdp : ∀ {X A B}, (hAB : X ⊢ᴵ[Λ] A 🡒 B) → (hA : X ⊢ᴵ[Λ] A) → (motive X (A 🡒 B) hAB) → (motive X A hA) → (motive X B (mdp hAB hA)))
  : ∀ {X A}, (h : X ⊢ᴵ[Λ] A) → motive X A h := by
  rintro X A ⟨h⟩;
  induction h with
  | ofProof h => apply ofProvable ⟨h⟩;
  | _ => grind;

lemma of_subset_ctx {X Y : Set (Formula α)} (hXY : X ⊆ Y) : (X ⊢ᴵ[Λ] A) → (Y ⊢ᴵ[Λ] A) := λ h => by induction h <;> grind;

lemma to_ctx {X A B} : (X ⊢ᴵ[Λ] A 🡒 B) → (insert A X ⊢ᴵ[Λ] B) := λ h => by
  apply mdp;
  . apply of_subset_ctx (X := X) (Y := insert A X);
    . tauto;
    . exact h;
  . apply ofContext;
    simp;

lemma drop_ctx {X A B} : (insert A X ⊢ᴵ[Λ] B) → (X ⊢ᴵ[Λ] A 🡒 B) := λ h => by
  generalize eY : insert A X = Y at h
  induction h with
  | ofProvable h => grind;
  | ofContext hB =>
    subst eY;
    rcases hB with rfl | hB
    . exact ofProvable $ ProvableInt.impId;
    . apply mdp;
      . exact ofProvable ProvableInt.implyK;
      . exact ofContext hB;
  | mdp _ _ ihAB ihA =>
    subst eY;
    replace ihAB := ihAB rfl
    replace ihA := ihA rfl;
    exact mdp (mdp (ofProvable ProvableInt.implyS) ihAB) ihA;

theorem deduction_theorem {X A B} : (X ⊢ᴵ[Λ] A 🡒 B) ↔ (insert A X ⊢ᴵ[Λ] B) := by
  constructor
  . apply to_ctx;
  . apply drop_ctx;

lemma iff_empty_ctx {A} : (∅ ⊢ᴵ[Λ] A) ↔ (Λ ⊢ᴵ A) := by
  constructor
  . rintro h;
    generalize eX : (∅ : Set (Formula α)) = X at h;
    induction h <;> grind;
  . grind;

lemma iff_singleton_deducible_provable {A B} : ({A} ⊢ᴵ[Λ] B) ↔ (Λ ⊢ᴵ A 🡒 B) := by
  rw [show (({A} : Set (Formula α)) = (insert A ∅)) by grind];
  apply Iff.trans (deduction_theorem.symm) iff_empty_ctx;

lemma andElimRuleL : (X ⊢ᴵ[Λ] A ⋏ B) → (X ⊢ᴵ[Λ] A) := λ hAB => mdp (ofProvable $ ProvableInt.andElimL) hAB
lemma andElimRuleR : (X ⊢ᴵ[Λ] A ⋏ B) → (X ⊢ᴵ[Λ] B) := λ hAB => mdp (ofProvable $ ProvableInt.andElimR) hAB
lemma andIntroRule : (X ⊢ᴵ[Λ] A) → (X ⊢ᴵ[Λ] B) → (X ⊢ᴵ[Λ] A ⋏ B) := λ hA hB => mdp (mdp (ofProvable ProvableInt.andIntro) hA) hB
lemma orIntroRuleL : (X ⊢ᴵ[Λ] A) → (X ⊢ᴵ[Λ] A ⋎ B) := λ hA => mdp (ofProvable $ ProvableInt.orIntroL) hA
lemma orIntroRuleR : (X ⊢ᴵ[Λ] B) → (X ⊢ᴵ[Λ] A ⋎ B) := λ hB => mdp (ofProvable $ ProvableInt.orIntroR) hB
lemma orElimRule : (X ⊢ᴵ[Λ] A 🡒 C) → (X ⊢ᴵ[Λ] B 🡒 C) → (X ⊢ᴵ[Λ] (A ⋎ B)) → X ⊢ᴵ[Λ] C := λ hAC hBC hAB => mdp (mdp (mdp (ofProvable $ ProvableInt.orElim) hAC) hBC) hAB

end IntDeducible

namespace ProvableInt

variable {Λ : Axioms α} {A B C : Formula α}

@[grind <=]
lemma ruleC : Λ ⊢ᴵ A 🡒 B → Λ ⊢ᴵ A 🡒 C → Λ ⊢ᴵ A 🡒 (B ⋏ C) := by
  intro hAB hAC;
  apply IntDeducible.iff_singleton_deducible_provable.mp;
  replace hAB : {A} ⊢ᴵ[Λ] B := IntDeducible.iff_singleton_deducible_provable.mpr hAB;
  replace hAC : {A} ⊢ᴵ[Λ] C := IntDeducible.iff_singleton_deducible_provable.mpr hAC;
  have        : {A} ⊢ᴵ[Λ] (B 🡒 C 🡒 (B ⋏ C)) := IntDeducible.ofProvable $ ProvableInt.andIntro;
  exact IntDeducible.mdp (IntDeducible.mdp this hAB) hAC

@[grind <=]
lemma ruleD : Λ ⊢ᴵ A 🡒 C → Λ ⊢ᴵ B 🡒 C → Λ ⊢ᴵ (A ⋎ B) 🡒 C := by
  intro hAC hBC;
  apply IntDeducible.iff_singleton_deducible_provable.mp;
  have : ({A ⋎ B} : Set (Formula α)) ⊢ᴵ[Λ] (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := .ofProvable $ .orElim;
  have : {A ⋎ B} ⊢ᴵ[Λ] (A ⋎ B) 🡒 C := .mdp (.mdp this (.ofProvable hAC)) (.ofProvable hBC);
  exact .mdp this (.ofContext $ by simp);

@[grind =>]
lemma ruleI : Λ ⊢ᴵ A 🡒 B → Λ ⊢ᴵ B 🡒 C → Λ ⊢ᴵ A 🡒 C := by
  intro hAB hBC;
  apply IntDeducible.iff_singleton_deducible_provable.mp;
  replace hAB : {A} ⊢ᴵ[Λ] B := IntDeducible.iff_singleton_deducible_provable.mpr hAB;
  replace hBC : {A} ⊢ᴵ[Λ] B 🡒 C := IntDeducible.ofProvable hBC;
  exact IntDeducible.mdp hBC hAB;

@[grind .]
lemma distributeAndOr : Λ ⊢ᴵ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by
  apply IntDeducible.iff_singleton_deducible_provable.mp;
  have hA : {A ⋏ (B ⋎ C)} ⊢ᴵ[Λ] A := IntDeducible.andElimRuleL (B := B ⋎ C) $ IntDeducible.ofContext (by simp);
  have :=
    IntDeducible.ofProvable (X := {A ⋏ (B ⋎ C)}) $
    ProvableInt.orElim (Λ := Λ) (A := B) (B := C) (C := A ⋏ B ⋎ A ⋏ C);
  apply IntDeducible.mdp (IntDeducible.mdp (IntDeducible.mdp this ?_) ?_) ?_;
  . show {A ⋏ (B ⋎ C)} ⊢ᴵ[Λ] B 🡒 (A ⋏ B ⋎ A ⋏ C);
    apply IntDeducible.drop_ctx;
    apply IntDeducible.orIntroRuleL;
    apply IntDeducible.andIntroRule;
    . apply IntDeducible.of_subset_ctx (X := {A ⋏ (B ⋎ C)});
      . tauto;
      . exact hA;
    . apply IntDeducible.ofContext;
      simp;
  . show {A ⋏ (B ⋎ C)} ⊢ᴵ[Λ] C 🡒 (A ⋏ B ⋎ A ⋏ C);
    apply IntDeducible.drop_ctx;
    apply IntDeducible.orIntroRuleR;
    apply IntDeducible.andIntroRule;
    . apply IntDeducible.of_subset_ctx (X := {A ⋏ (B ⋎ C)});
      . tauto;
      . trivial;
    . apply IntDeducible.ofContext;
      simp;
  . exact IntDeducible.andElimRuleR (A := A) $ IntDeducible.ofContext (by simp);

end ProvableInt


theorem provableInt_of_provableVF (h : Λ ⊢ⱽ A) : Λ ⊢ᴵ A := by induction h <;> grind;
