module

public import VeryWeakSubintuitionistic.Propositional.Proof.VF

@[expose] public section

variable {α : Type*}

namespace Int

inductive ProofHilbert (𝔸 : Axioms α) : Formula α → Type _
| axm {A}                 : A ∈ 𝔸 → ProofHilbert 𝔸 A
| andElimL {A B}          : ProofHilbert 𝔸 $ (A ⋏ B) 🡒 A
| andElimR {A B}          : ProofHilbert 𝔸 $ (A ⋏ B) 🡒 B
| andIntro {A B}          : ProofHilbert 𝔸 $ (A 🡒 B 🡒 (A ⋏ B))
| orIntroL {A B}          : ProofHilbert 𝔸 $ A 🡒 (A ⋎ B)
| orIntroR {A B}          : ProofHilbert 𝔸 $ B 🡒 (A ⋎ B)
| orElim {A B C}          : ProofHilbert 𝔸 $ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)
| implyK {A B}            : ProofHilbert 𝔸 $ A 🡒 B 🡒 A
| implyS {A B C}          : ProofHilbert 𝔸 $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| verum                   : ProofHilbert 𝔸 $ ⊤
| efq {A}                 : ProofHilbert 𝔸 $ ⊥ 🡒 A
| mdp {A B}               : ProofHilbert 𝔸 (A 🡒 B) → ProofHilbert 𝔸 A → ProofHilbert 𝔸 B

notation:50 "⊢ʰ![Int;" 𝔸 "] " A:51 => Int.ProofHilbert 𝔸 A

namespace ProofHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C : Formula α}

def af {A B} : ⊢ʰ![Int;𝔸] A → ⊢ʰ![Int;𝔸] (B 🡒 A) := λ h => mdp implyK h

def impId : ⊢ʰ![Int;𝔸] (A 🡒 A) := by
  haveI : ⊢ʰ![Int;𝔸] ((A 🡒 (A 🡒 A) 🡒 A) 🡒 (A 🡒 A 🡒 A) 🡒 (A 🡒 A)) := implyS;
  haveI : ⊢ʰ![Int;𝔸] ((A 🡒 A 🡒 A) 🡒 (A 🡒 A)) := mdp this implyK;
  haveI : ⊢ʰ![Int;𝔸] (A 🡒 A) := mdp this implyK;
  exact this;

def andElimRuleL : ⊢ʰ![Int;𝔸] (A ⋏ B) → ⊢ʰ![Int;𝔸] A := λ h => mdp andElimL h
def andElimRuleR : ⊢ʰ![Int;𝔸] (A ⋏ B) → ⊢ʰ![Int;𝔸] B := λ h => mdp andElimR h

noncomputable def ofSubsetAxm (hsub : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ![Int;𝔸₁] A) → ⊢ʰ![Int;𝔸₂] A := λ h => by
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

end ProofHilbert


abbrev ProvableHilbert (𝔸 : Axioms α) (A : Formula α) : Prop := Nonempty (⊢ʰ![Int;𝔸] A)

end Int

notation:50 "⊢ʰ[Int;" 𝔸 "] " A:51 => Int.ProvableHilbert 𝔸 A
notation:50 "⊬ʰ[Int;" 𝔸 "] " A:51 => ¬(Int.ProvableHilbert 𝔸 A)

namespace Int.ProvableHilbert

variable {𝔸 : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ 𝔸 → ⊢ʰ[Int;𝔸] A := λ h => ⟨ProofHilbert.axm h⟩
@[simp, grind .] lemma implyK : ⊢ʰ[Int;𝔸] A 🡒 B 🡒 A := ⟨ProofHilbert.implyK⟩
@[simp, grind .] lemma implyS : ⊢ʰ[Int;𝔸] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofHilbert.implyS⟩
@[simp, grind .] lemma andElimL : ⊢ʰ[Int;𝔸] (A ⋏ B) 🡒 A := ⟨ProofHilbert.andElimL⟩
@[simp, grind .] lemma andElimR : ⊢ʰ[Int;𝔸] (A ⋏ B) 🡒 B := ⟨ProofHilbert.andElimR⟩
@[simp, grind .] lemma andIntro : ⊢ʰ[Int;𝔸] (A 🡒 B 🡒 (A ⋏ B)) := ⟨ProofHilbert.andIntro⟩
@[simp, grind .] lemma orIntroL : ⊢ʰ[Int;𝔸] A 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroL⟩
@[simp, grind .] lemma orIntroR : ⊢ʰ[Int;𝔸] B 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroR⟩
@[simp, grind .] lemma orElim : ⊢ʰ[Int;𝔸] (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := ⟨ProofHilbert.orElim⟩
@[simp, grind .] lemma efq : ⊢ʰ[Int;𝔸] ⊥ 🡒 A := ⟨ProofHilbert.efq⟩
@[simp, grind .] lemma verum : ⊢ʰ[Int;𝔸] (⊤ : Formula α) := ⟨ProofHilbert.verum⟩
@[simp, grind .] lemma impId : ⊢ʰ[Int;𝔸] A 🡒 A := ⟨ProofHilbert.impId⟩
@[grind =>] lemma mdp : (⊢ʰ[Int;𝔸] A 🡒 B) → (⊢ʰ[Int;𝔸] A) → ⊢ʰ[Int;𝔸] B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[grind <=] lemma af : (⊢ʰ[Int;𝔸] A) → ⊢ʰ[Int;𝔸] B 🡒 A := λ ⟨h⟩ => ⟨ProofHilbert.af h⟩

@[grind =>] lemma andElimRuleL : (⊢ʰ[Int;𝔸] A ⋏ B) → ⊢ʰ[Int;𝔸] A := λ h => mdp andElimL h
@[grind =>] lemma andElimRuleR : (⊢ʰ[Int;𝔸] A ⋏ B) → ⊢ʰ[Int;𝔸] B := λ h => mdp andElimR h

@[induction_eliminator]
protected lemma rec
  {motive          : (A : Formula α) → (⊢ʰ[Int;𝔸] A) → Prop}
  (axm             : ∀ {A}, (h : A ∈ 𝔸) → motive A (axm h))
  (mdp             : ∀ {A B}, {hAB : ⊢ʰ[Int;𝔸] A 🡒 B} → {hA : ⊢ʰ[Int;𝔸] A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (verum           : motive (⊤ : Formula α) verum)
  (andElimL        : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR        : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (andIntro        : ∀ {A B}, (motive (A 🡒 B 🡒 (A ⋏ B)) andIntro))
  (orIntroL        : ∀ {A B}, (motive (A 🡒 (A ⋎ B)) orIntroL))
  (orIntroR        : ∀ {A B}, (motive (B 🡒 (A ⋎ B)) orIntroR))
  (orElim          : ∀ {A B C}, (motive ((A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)) orElim))
  (implyK          : ∀ {A B}, (motive (A 🡒 B 🡒 A) implyK))
  (implyS          : ∀ {A B C}, (motive ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)) implyS))
  (efq             : ∀ {A}, (motive (⊥ 🡒 A) efq))
  : ∀ {A}, (d : ⊢ʰ[Int;𝔸] A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end Int.ProvableHilbert


namespace Int

inductive DeductionHilbert (𝔸 : Axioms α) : Set (Formula α) → Formula α → Type _
| ofProof {X A} : ⊢ʰ![Int;𝔸] A → DeductionHilbert 𝔸 X A
| ofContext {X A} : A ∈ X → DeductionHilbert 𝔸 X A
| mdp {X A B} : (DeductionHilbert 𝔸 X (A 🡒 B)) → (DeductionHilbert 𝔸 X A) → (DeductionHilbert 𝔸 X B)

abbrev DeducibleHilbert (𝔸 : Axioms α) (X : Set (Formula α)) (A : Formula α) : Prop := Nonempty (DeductionHilbert 𝔸 X A)

end Int

notation:50 X:51 " ⊢ʰ![Int;" 𝔸 "] " A:51 => Int.DeductionHilbert 𝔸 X A
notation:50 X:51 " ⊢ʰ[Int;" 𝔸 "] " A:51 => Int.DeducibleHilbert 𝔸 X A

namespace Int.DeducibleHilbert

variable {𝔸 : Axioms α} {X : Set (Formula α)} {A B C : Formula α}

@[grind <=] lemma ofProvable {X A} : (⊢ʰ[Int;𝔸] A) → X ⊢ʰ[Int;𝔸] A := λ ⟨h⟩ => ⟨DeductionHilbert.ofProof h⟩
@[grind <=] lemma ofContext {X A} : A ∈ X → X ⊢ʰ[Int;𝔸] A := λ h => ⟨DeductionHilbert.ofContext h⟩
@[grind =>] lemma mdp {X A B} : (X ⊢ʰ[Int;𝔸] A 🡒 B) → (X ⊢ʰ[Int;𝔸] A) → (X ⊢ʰ[Int;𝔸] B) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨DeductionHilbert.mdp h₁ h₂⟩

@[induction_eliminator]
protected lemma rec
  {motive : (X : Set (Formula α)) → (A : Formula α) → (X ⊢ʰ[Int;𝔸] A) → Prop}
  (ofProvable : ∀ {X A}, (h : ⊢ʰ[Int;𝔸] A) → motive X A (ofProvable h))
  (ofContext : ∀ {X A}, (h : A ∈ X) → motive X A (ofContext h))
  (mdp : ∀ {X A B}, (hAB : X ⊢ʰ[Int;𝔸] A 🡒 B) → (hA : X ⊢ʰ[Int;𝔸] A) → (motive X (A 🡒 B) hAB) → (motive X A hA) → (motive X B (mdp hAB hA)))
  : ∀ {X A}, (h : X ⊢ʰ[Int;𝔸] A) → motive X A h := by
  rintro X A ⟨h⟩;
  induction h with
  | ofProof h => apply ofProvable ⟨h⟩;
  | _ => grind;

lemma of_subset_ctx {X Y : Set (Formula α)} (hXY : X ⊆ Y) : (X ⊢ʰ[Int;𝔸] A) → (Y ⊢ʰ[Int;𝔸] A) := λ h => by induction h <;> grind;

lemma to_ctx {X A B} : (X ⊢ʰ[Int;𝔸] A 🡒 B) → (insert A X ⊢ʰ[Int;𝔸] B) := λ h => by
  apply mdp;
  . apply of_subset_ctx (X := X) (Y := insert A X);
    . tauto;
    . exact h;
  . apply ofContext;
    simp;

lemma drop_ctx {X A B} : (insert A X ⊢ʰ[Int;𝔸] B) → (X ⊢ʰ[Int;𝔸] A 🡒 B) := λ h => by
  generalize eY : insert A X = Y at h
  induction h with
  | ofProvable h => grind;
  | ofContext hB =>
    subst eY;
    rcases hB with rfl | hB
    . exact ofProvable $ ProvableHilbert.impId;
    . apply mdp;
      . exact ofProvable ProvableHilbert.implyK;
      . exact ofContext hB;
  | mdp _ _ ihAB ihA =>
    subst eY;
    replace ihAB := ihAB rfl
    replace ihA := ihA rfl;
    exact mdp (mdp (ofProvable ProvableHilbert.implyS) ihAB) ihA;

theorem deduction_theorem {X A B} : (X ⊢ʰ[Int;𝔸] A 🡒 B) ↔ (insert A X ⊢ʰ[Int;𝔸] B) := by
  constructor
  . apply to_ctx;
  . apply drop_ctx;

lemma iff_empty_ctx {A} : ((∅ : Set (Formula α)) ⊢ʰ[Int;𝔸] A) ↔ (⊢ʰ[Int;𝔸] A) := by
  constructor
  . rintro h;
    generalize eX : (∅ : Set (Formula α)) = X at h;
    induction h <;> grind;
  . grind;

lemma iff_singleton_deducible_provable {A B} : (({A} : Set (Formula α)) ⊢ʰ[Int;𝔸] B) ↔ (⊢ʰ[Int;𝔸] A 🡒 B) := by
  rw [show (({A} : Set (Formula α)) = (insert A ∅)) by grind];
  apply Iff.trans (deduction_theorem.symm) iff_empty_ctx;

lemma andElimRuleL : (X ⊢ʰ[Int;𝔸] A ⋏ B) → (X ⊢ʰ[Int;𝔸] A) := λ hAB => mdp (ofProvable $ ProvableHilbert.andElimL) hAB
lemma andElimRuleR : (X ⊢ʰ[Int;𝔸] A ⋏ B) → (X ⊢ʰ[Int;𝔸] B) := λ hAB => mdp (ofProvable $ ProvableHilbert.andElimR) hAB
lemma andIntroRule : (X ⊢ʰ[Int;𝔸] A) → (X ⊢ʰ[Int;𝔸] B) → (X ⊢ʰ[Int;𝔸] A ⋏ B) := λ hA hB => mdp (mdp (ofProvable ProvableHilbert.andIntro) hA) hB
lemma orIntroRuleL : (X ⊢ʰ[Int;𝔸] A) → (X ⊢ʰ[Int;𝔸] A ⋎ B) := λ hA => mdp (ofProvable $ ProvableHilbert.orIntroL) hA
lemma orIntroRuleR : (X ⊢ʰ[Int;𝔸] B) → (X ⊢ʰ[Int;𝔸] A ⋎ B) := λ hB => mdp (ofProvable $ ProvableHilbert.orIntroR) hB
lemma orElimRule : (X ⊢ʰ[Int;𝔸] A 🡒 C) → (X ⊢ʰ[Int;𝔸] B 🡒 C) → (X ⊢ʰ[Int;𝔸] (A ⋎ B)) → X ⊢ʰ[Int;𝔸] C := λ hAC hBC hAB => mdp (mdp (mdp (ofProvable $ ProvableHilbert.orElim) hAC) hBC) hAB

end Int.DeducibleHilbert

namespace Int.ProvableHilbert

variable {𝔸 : Axioms α} {A B C : Formula α}

@[grind <=]
lemma ruleC : (⊢ʰ[Int;𝔸] A 🡒 B) → (⊢ʰ[Int;𝔸] A 🡒 C) → ⊢ʰ[Int;𝔸] A 🡒 (B ⋏ C) := by
  intro hAB hAC;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  replace hAB : ({A} : Set (Formula α)) ⊢ʰ[Int;𝔸] B := DeducibleHilbert.iff_singleton_deducible_provable.mpr hAB;
  replace hAC : ({A} : Set (Formula α)) ⊢ʰ[Int;𝔸] C := DeducibleHilbert.iff_singleton_deducible_provable.mpr hAC;
  have        : ({A} : Set (Formula α)) ⊢ʰ[Int;𝔸] (B 🡒 C 🡒 (B ⋏ C)) := DeducibleHilbert.ofProvable $ ProvableHilbert.andIntro;
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp this hAB) hAC

@[grind <=]
lemma ruleD : (⊢ʰ[Int;𝔸] A 🡒 C) → (⊢ʰ[Int;𝔸] B 🡒 C) → ⊢ʰ[Int;𝔸] (A ⋎ B) 🡒 C := by
  intro hAC hBC;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have : ({A ⋎ B} : Set (Formula α)) ⊢ʰ[Int;𝔸] (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := .ofProvable $ .orElim;
  have : ({A ⋎ B} : Set (Formula α)) ⊢ʰ[Int;𝔸] (A ⋎ B) 🡒 C := .mdp (.mdp this (.ofProvable hAC)) (.ofProvable hBC);
  exact .mdp this (.ofContext $ by simp);

@[grind =>]
lemma ruleI : (⊢ʰ[Int;𝔸] A 🡒 B) → (⊢ʰ[Int;𝔸] B 🡒 C) → ⊢ʰ[Int;𝔸] A 🡒 C := by
  intro hAB hBC;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  replace hAB : ({A} : Set (Formula α)) ⊢ʰ[Int;𝔸] B := DeducibleHilbert.iff_singleton_deducible_provable.mpr hAB;
  replace hBC : ({A} : Set (Formula α)) ⊢ʰ[Int;𝔸] B 🡒 C := DeducibleHilbert.ofProvable hBC;
  exact DeducibleHilbert.mdp hBC hAB;

@[grind .]
lemma distributeAndOr : ⊢ʰ[Int;𝔸] (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hA : ({A ⋏ (B ⋎ C)} : Set (Formula α)) ⊢ʰ[Int;𝔸] A := DeducibleHilbert.andElimRuleL (B := B ⋎ C) $ DeducibleHilbert.ofContext (by simp);
  have :=
    DeducibleHilbert.ofProvable (X := {A ⋏ (B ⋎ C)}) $
    ProvableHilbert.orElim (𝔸 := 𝔸) (A := B) (B := C) (C := A ⋏ B ⋎ A ⋏ C);
  apply DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.mdp this ?_) ?_) ?_;
  . show ({A ⋏ (B ⋎ C)} : Set (Formula α)) ⊢ʰ[Int;𝔸] B 🡒 (A ⋏ B ⋎ A ⋏ C);
    apply DeducibleHilbert.drop_ctx;
    apply DeducibleHilbert.orIntroRuleL;
    apply DeducibleHilbert.andIntroRule;
    . apply DeducibleHilbert.of_subset_ctx (X := {A ⋏ (B ⋎ C)});
      . tauto;
      . exact hA;
    . apply DeducibleHilbert.ofContext;
      simp;
  . show ({A ⋏ (B ⋎ C)} : Set (Formula α)) ⊢ʰ[Int;𝔸] C 🡒 (A ⋏ B ⋎ A ⋏ C);
    apply DeducibleHilbert.drop_ctx;
    apply DeducibleHilbert.orIntroRuleR;
    apply DeducibleHilbert.andIntroRule;
    . apply DeducibleHilbert.of_subset_ctx (X := {A ⋏ (B ⋎ C)});
      . tauto;
      . trivial;
    . apply DeducibleHilbert.ofContext;
      simp;
  . exact DeducibleHilbert.andElimRuleR (A := A) $ DeducibleHilbert.ofContext (by simp);

@[simp, grind .]
lemma dni : ⊢ʰ[Int;𝔸] A 🡒 ∼∼A := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.drop_ctx;
  have h₁ : ({∼A, A} : Set (Formula α)) ⊢ʰ[Int;𝔸] ∼A := DeducibleHilbert.ofContext (by simp);
  have h₂ : ({∼A, A} : Set (Formula α)) ⊢ʰ[Int;𝔸] A := DeducibleHilbert.ofContext (by simp);
  exact DeducibleHilbert.mdp h₁ h₂;

@[grind <=]
lemma dniRule : (⊢ʰ[Int;𝔸] A) → ⊢ʰ[Int;𝔸] ∼∼A := λ h => mdp dni h

lemma ofVF {𝔸 : Axioms α} {A : Formula α} (h : ⊢ʰ[VF;𝔸] A) : ⊢ʰ[Int;𝔸] A := by induction h <;> grind;

end Int.ProvableHilbert
