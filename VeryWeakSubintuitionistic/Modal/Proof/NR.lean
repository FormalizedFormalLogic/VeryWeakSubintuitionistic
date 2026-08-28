module

public import VeryWeakSubintuitionistic.Modal.Proof.N

@[expose] public section

namespace Modal

variable {α : Type*}

namespace NR

inductive ProofHilbert (𝔸 : Axioms α) : Formula α → Type _
| axm {A}        : A ∈ 𝔸 → ProofHilbert 𝔸 A
| implyK {A B}   : ProofHilbert 𝔸 $ A 🡒 B 🡒 A
| implyS {A B C} : ProofHilbert 𝔸 $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| efq {A}        : ProofHilbert 𝔸 $ ⊥ 🡒 A
| dne {A}        : ProofHilbert 𝔸 $ ∼∼A 🡒 A
| andElimL {A B} : ProofHilbert 𝔸 $ (A ⋏ B) 🡒 A
| andElimR {A B} : ProofHilbert 𝔸 $ (A ⋏ B) 🡒 B
| andIntro {A B} : ProofHilbert 𝔸 $ A 🡒 B 🡒 (A ⋏ B)
| orElim {A B C} : ProofHilbert 𝔸 $ A ⋎ B 🡒 (A 🡒 C) 🡒 (B 🡒 C) 🡒 C
| mdp {A B}      : ProofHilbert 𝔸 (A 🡒 B) → ProofHilbert 𝔸 A → ProofHilbert 𝔸 B
| nec {A}        : ProofHilbert 𝔸 A → ProofHilbert 𝔸 (□A)
| ros {A}        : ProofHilbert 𝔸 (∼A) → ProofHilbert 𝔸 (∼□A)

notation:50 "⊢ʰ![NR;" 𝔸 "] " A:51 => Modal.NR.ProofHilbert 𝔸 A

namespace ProofHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C : Formula α}

noncomputable def ofSubsetAxm (hsub : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ![NR;𝔸₁] A) → ⊢ʰ![NR;𝔸₂] A := λ h => by
  induction h with
  | axm h₁ => exact axm (hsub h₁)
  | implyK => exact implyK
  | implyS => exact implyS
  | efq => exact efq
  | dne => exact dne
  | andElimL => exact andElimL
  | andElimR => exact andElimR
  | andIntro => exact andIntro
  | orElim => exact orElim
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA
  | nec _ ihA => exact nec ihA
  | ros _ ihA => exact ros ihA

noncomputable def ofProofHilbertN : (⊢ʰ![N;𝔸] A) → ⊢ʰ![NR;𝔸] A := λ h => by
  induction h with
  | axm h => exact axm h
  | implyK => exact implyK
  | implyS => exact implyS
  | efq => exact efq
  | dne => exact dne
  | andElimL => exact andElimL
  | andElimR => exact andElimR
  | andIntro => exact andIntro
  | orElim => exact orElim
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA
  | nec _ ihA => exact nec ihA

end ProofHilbert


abbrev ProvableHilbert (𝔸 : Axioms α) (A : Formula α) : Prop := Nonempty (⊢ʰ![NR;𝔸] A)

end NR

end Modal

notation:50 "⊢ʰ[NR;" 𝔸 "] " A:51 => Modal.NR.ProvableHilbert 𝔸 A
notation:50 "⊬ʰ[NR;" 𝔸 "] " A:51 => ¬(Modal.NR.ProvableHilbert 𝔸 A)

namespace Modal

namespace NR.ProvableHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C D : Formula α}

@[grind =>] lemma axm : A ∈ 𝔸 → ⊢ʰ[NR;𝔸] A := λ h => ⟨ProofHilbert.axm h⟩
@[simp, grind .] lemma implyK : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 A := ⟨ProofHilbert.implyK⟩
@[simp, grind .] lemma implyS : ⊢ʰ[NR;𝔸] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofHilbert.implyS⟩
@[simp, grind .] lemma efq : ⊢ʰ[NR;𝔸] ⊥ 🡒 A := ⟨ProofHilbert.efq⟩
@[simp, grind .] lemma dne : ⊢ʰ[NR;𝔸] ∼∼A 🡒 A := ⟨ProofHilbert.dne⟩
@[simp, grind .] lemma andElimL : ⊢ʰ[NR;𝔸] (A ⋏ B) 🡒 A := ⟨ProofHilbert.andElimL⟩
@[simp, grind .] lemma andElimR : ⊢ʰ[NR;𝔸] (A ⋏ B) 🡒 B := ⟨ProofHilbert.andElimR⟩
@[simp, grind .] lemma andIntro : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 (A ⋏ B) := ⟨ProofHilbert.andIntro⟩
@[simp, grind .] lemma orElim : ⊢ʰ[NR;𝔸] A ⋎ B 🡒 (A 🡒 C) 🡒 (B 🡒 C) 🡒 C := ⟨ProofHilbert.orElim⟩

@[grind =>] lemma mdp : (⊢ʰ[NR;𝔸] A 🡒 B) → (⊢ʰ[NR;𝔸] A) → ⊢ʰ[NR;𝔸] B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[grind =>] lemma mdp₂ (hABC : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 C) (hA : ⊢ʰ[NR;𝔸] A) (hB : ⊢ʰ[NR;𝔸] B) : ⊢ʰ[NR;𝔸] C := mdp (mdp hABC hA) hB
@[grind =>] lemma mdp₃ (hABCD : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 C 🡒 D) (hA : ⊢ʰ[NR;𝔸] A) (hB : ⊢ʰ[NR;𝔸] B) (hC : ⊢ʰ[NR;𝔸] C) : ⊢ʰ[NR;𝔸] D := mdp (mdp₂ hABCD hA hB) hC

@[grind <=] lemma af : (⊢ʰ[NR;𝔸] A) → ⊢ʰ[NR;𝔸] B 🡒 A := λ h => mdp implyK h
@[grind <=] lemma nec : (⊢ʰ[NR;𝔸] A) → ⊢ʰ[NR;𝔸] □A := λ ⟨h⟩ => ⟨ProofHilbert.nec h⟩
@[grind <=] lemma ros : (⊢ʰ[NR;𝔸] ∼A) → ⊢ʰ[NR;𝔸] ∼□A := λ ⟨h⟩ => ⟨ProofHilbert.ros h⟩

lemma ofSubsetAxm (h : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ[NR;𝔸₁] A) → ⊢ʰ[NR;𝔸₂] A := λ ⟨h₁⟩ => ⟨ProofHilbert.ofSubsetAxm h h₁⟩

@[grind =>] lemma ofProvableN : (⊢ʰ[N;𝔸] A) → ⊢ʰ[NR;𝔸] A := λ ⟨h⟩ => ⟨ProofHilbert.ofProofHilbertN h⟩

@[simp, grind .] lemma impId : ⊢ʰ[NR;𝔸] A 🡒 A := ofProvableN N.ProvableHilbert.impId
@[grind .] lemma lem : ⊢ʰ[NR;𝔸] A ⋎ ∼A := ofProvableN N.ProvableHilbert.lem
@[simp, grind .] lemma verum : ⊢ʰ[NR;𝔸] (⊤ : Formula α) := ofProvableN N.ProvableHilbert.verum

lemma andElimLRule (hAB : ⊢ʰ[NR;𝔸] A ⋏ B) : ⊢ʰ[NR;𝔸] A := mdp andElimL hAB
lemma andElimRRule (hAB : ⊢ʰ[NR;𝔸] A ⋏ B) : ⊢ʰ[NR;𝔸] B := mdp andElimR hAB
lemma andIntroRule (hA : ⊢ʰ[NR;𝔸] A) (hB : ⊢ʰ[NR;𝔸] B) : ⊢ʰ[NR;𝔸] A ⋏ B := mdp₂ andIntro hA hB

lemma orElimRule (hAB : ⊢ʰ[NR;𝔸] A ⋎ B) (hAC : ⊢ʰ[NR;𝔸] A 🡒 C) (hBC : ⊢ʰ[NR;𝔸] B 🡒 C) : ⊢ʰ[NR;𝔸] C := mdp₃ orElim hAB hAC hBC

@[grind <=] lemma efqRule (hA : ⊢ʰ[NR;𝔸] ⊥) : ⊢ʰ[NR;𝔸] A := mdp efq hA

@[grind =>]
lemma consistent_of_unprovable (h : ⊬ʰ[NR;𝔸] A) : ⊬ʰ[NR;𝔸] ⊥ := by
  contrapose! h;
  apply efqRule h;

@[grind =>] lemma dneRule (hA : ⊢ʰ[NR;𝔸] ∼∼A) : ⊢ʰ[NR;𝔸] A := mdp dne hA

lemma ctx_mdp {B} (hCAB : ⊢ʰ[NR;𝔸] C 🡒 A 🡒 B) (hCA : ⊢ʰ[NR;𝔸] C 🡒 A) : ⊢ʰ[NR;𝔸] C 🡒 B := mdp₂ implyS hCAB hCA

lemma impTrans : ⊢ʰ[NR;𝔸] (A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C) := ofProvableN N.ProvableHilbert.impTrans

lemma impTransRule (hAB : ⊢ʰ[NR;𝔸] A 🡒 B) (hBC : ⊢ʰ[NR;𝔸] B 🡒 C) : ⊢ʰ[NR;𝔸] A 🡒 C := mdp₂ impTrans hAB hBC

lemma fconjElim {X : Finset _} (hA : A ∈ X) : ⊢ʰ[NR;𝔸] ⋀X 🡒 A := ofProvableN $ N.ProvableHilbert.fconjElim hA

lemma sconj_subset {X Y : Finset _} (hsub : X ⊆ Y) : ⊢ʰ[NR;𝔸] ⋀Y 🡒 ⋀X := ofProvableN $ N.ProvableHilbert.sconj_subset hsub

lemma ctx_af {B} (hCA : ⊢ʰ[NR;𝔸] C 🡒 A) : ⊢ʰ[NR;𝔸] C 🡒 B 🡒 A := impTransRule hCA implyK

lemma ctxAndIntroRule (hA : ⊢ʰ[NR;𝔸] C 🡒 A) (hB : ⊢ʰ[NR;𝔸] C 🡒 B) : ⊢ʰ[NR;𝔸] C 🡒 (A ⋏ B) :=
  ctx_mdp (impTransRule hA $ andIntro) hB

lemma ctxOrElimRule (hAB : ⊢ʰ[NR;𝔸] C 🡒 A ⋎ B) (hAC : ⊢ʰ[NR;𝔸] C 🡒 A 🡒 D) (hBC : ⊢ʰ[NR;𝔸] C 🡒 B 🡒 D) : ⊢ʰ[NR;𝔸] C 🡒 D :=
  ctx_mdp (ctx_mdp (impTransRule hAB orElim) hAC) hBC

lemma ctxLconjIntroRule {X : List _} (hA : ∀ A ∈ X, ⊢ʰ[NR;𝔸] C 🡒 A) : ⊢ʰ[NR;𝔸] C 🡒 ⋀X := by
  match X with
  | [] => apply af; simp;
  | [A] => grind;
  | A :: B :: Y =>
    apply ctxAndIntroRule;
    . apply hA; grind;
    . apply ctxLconjIntroRule; grind;

lemma ctxFconjIntroRule {X : Finset _} (hA : ∀ A ∈ X, ⊢ʰ[NR;𝔸] C 🡒 A) : ⊢ʰ[NR;𝔸] C 🡒 ⋀X := ctxLconjIntroRule (X := X.toList) (by simpa)

lemma uncurry {A B C} (h : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 C) : ⊢ʰ[NR;𝔸] (A ⋏ B) 🡒 C := ctx_mdp (impTransRule andElimL h) andElimR

lemma curry {A B C} (h : ⊢ʰ[NR;𝔸] (A ⋏ B) 🡒 C) : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 C := by
  have h₁ : ⊢ʰ[NR;𝔸] A 🡒 B 🡒 (A ⋏ B) := andIntro;
  have h₂ : ⊢ʰ[NR;𝔸] A 🡒 (A ⋏ B 🡒 C) := af h;
  exact ctx_mdp (impTransRule h₁ impTrans) h₂;

variable [DecidableEq α] in
@[simp, grind .]
lemma dni : ⊢ʰ[NR;𝔸] A 🡒 ∼∼A := ofProvableN N.ProvableHilbert.dni

variable [DecidableEq α] in
lemma ctx_nc (hCA : ⊢ʰ[NR;𝔸] C 🡒 A) : ⊢ʰ[NR;𝔸] C 🡒 (∼A 🡒 D) :=
  impTransRule hCA $ ofProvableN $ N.ProvableHilbert.ctx_nc N.ProvableHilbert.impId

variable [DecidableEq α] in
lemma ctx_nc2 (hCA : ⊢ʰ[NR;𝔸] C 🡒 ∼A) : ⊢ʰ[NR;𝔸] C 🡒 (A 🡒 D) :=
  impTransRule hCA $ ofProvableN $ N.ProvableHilbert.ctx_nc2 N.ProvableHilbert.impId

@[induction_eliminator]
protected lemma rec
  {motive  : (A : Formula α) → (⊢ʰ[NR;𝔸] A) → Prop}
  (axm     : ∀ {A}, (h : A ∈ 𝔸) → motive A (axm h))
  (mdp     : ∀ {A B}, {hAB : ⊢ʰ[NR;𝔸] A 🡒 B} → {hA : ⊢ʰ[NR;𝔸] A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (nec     : ∀ {A}, {hA : ⊢ʰ[NR;𝔸] A} → (motive A hA) → (motive (□A) (nec hA)))
  (ros     : ∀ {A}, {hA : ⊢ʰ[NR;𝔸] ∼A} → (motive (∼A) hA) → (motive (∼□A) (ros hA)))
  (implyK  : ∀ {A B}, (motive (A 🡒 B 🡒 A) implyK))
  (implyS  : ∀ {A B C}, (motive ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)) implyS))
  (efq     : ∀ {A}, (motive (⊥ 🡒 A) efq))
  (dne     : ∀ {A}, (motive (∼∼A 🡒 A) dne))
  (andElimL : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (andIntro : ∀ {A B}, (motive (A 🡒 B 🡒 (A ⋏ B)) andIntro))
  (orElim   : ∀ {A B C}, (motive (A ⋎ B 🡒 (A 🡒 C) 🡒 (B 🡒 C) 🡒 C) orElim))
  : ∀ {A}, (d : ⊢ʰ[NR;𝔸] A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end NR.ProvableHilbert


def NR.FinitelyDerivableHilbert (𝔸 : Axioms α) (X : Finset (Formula α)) (A : Formula α) := ⊢ʰ[NR;𝔸] ⋀X 🡒 A

end Modal

notation:50 X:51 " ⊢ʰ[NR;" 𝔸 "] " A:51 => Modal.NR.FinitelyDerivableHilbert 𝔸 X A

namespace Modal

namespace NR.FinitelyDerivableHilbert

variable {𝔸 : Axioms α} {X Y : Finset (Formula α)} {A B C : Formula α}

open NR.ProvableHilbert

lemma iff_empty_derivable : (⊢ʰ[NR;𝔸] A) ↔ ((∅ : Finset (Formula α)) ⊢ʰ[NR;𝔸] A) := by
  unfold FinitelyDerivableHilbert;
  constructor;
  . intro h;
    exact af $ h;
  . intro h;
    exact mdp h (by simp);

lemma to_ctx [DecidableEq α] : (X ⊢ʰ[NR;𝔸] A 🡒 B) → ((insert A X) ⊢ʰ[NR;𝔸] B) := by
  unfold FinitelyDerivableHilbert;
  intro h;
  apply impTransRule;
  . show ⊢ʰ[NR;𝔸] ⋀insert A X 🡒 (⋀X ⋏ A);
    apply ctxAndIntroRule;
    . apply sconj_subset;
      grind;
    . apply fconjElim;
      grind;
  . exact uncurry h;

lemma from_ctx [DecidableEq α] : ((insert A X) ⊢ʰ[NR;𝔸] B) → (X ⊢ʰ[NR;𝔸] A 🡒 B) := by
  unfold FinitelyDerivableHilbert;
  intro h;
  apply curry;
  apply impTransRule;
  . show ⊢ʰ[NR;𝔸] (⋀X ⋏ A) 🡒 ⋀(insert A X);
    apply ctxFconjIntroRule;
    intro C hC;
    simp only [Finset.mem_insert] at hC;
    rcases hC with (rfl | hC);
    . grind;
    . apply impTransRule;
      . exact andElimL;
      . exact fconjElim hC;
  . exact h;

lemma of_mem_ctx (hA : A ∈ X) : X ⊢ʰ[NR;𝔸] A := by
  unfold FinitelyDerivableHilbert;
  apply ProvableHilbert.fconjElim hA;

lemma mdp (hAB : X ⊢ʰ[NR;𝔸] A 🡒 B) (hA : X ⊢ʰ[NR;𝔸] A) : X ⊢ʰ[NR;𝔸] B := by
  unfold FinitelyDerivableHilbert at hAB hA ⊢;
  exact ProvableHilbert.ctx_mdp hAB hA;

lemma weakening (hsub : X ⊆ Y) (hX : X ⊢ʰ[NR;𝔸] A) : Y ⊢ʰ[NR;𝔸] A := by
  unfold FinitelyDerivableHilbert at hX ⊢;
  apply ProvableHilbert.impTransRule ?_ hX;
  apply ProvableHilbert.sconj_subset hsub;

lemma of_provable (hA : ⊢ʰ[NR;𝔸] A) : X ⊢ʰ[NR;𝔸] A := by
  exact weakening (show ∅ ⊆ X by simp) $ iff_empty_derivable.mp hA;

lemma orElim (hAB : X ⊢ʰ[NR;𝔸] A ⋎ B) (hAC : X ⊢ʰ[NR;𝔸] A 🡒 C) (hBC : X ⊢ʰ[NR;𝔸] B 🡒 C) : X ⊢ʰ[NR;𝔸] C := ctxOrElimRule hAB hAC hBC

lemma lem_elim (hA : X ⊢ʰ[NR;𝔸] A 🡒 B) (hNA : X ⊢ʰ[NR;𝔸] ∼A 🡒 B) : X ⊢ʰ[NR;𝔸] B := by
  apply orElim (of_provable lem) hA hNA;

end NR.FinitelyDerivableHilbert

end Modal

end
