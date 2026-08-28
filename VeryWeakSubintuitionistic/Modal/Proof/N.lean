module

public import VeryWeakSubintuitionistic.Modal.Proof.Basic

@[expose] public section

namespace Modal

variable {α : Type*}

namespace N

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

notation:50 "⊢ʰ![N;" 𝔸 "] " A:51 => Modal.N.ProofHilbert 𝔸 A

namespace ProofHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C : Formula α}

def af {A B} : ⊢ʰ![N;𝔸] A → ⊢ʰ![N;𝔸] (B 🡒 A) := λ h => mdp implyK h

def impId : ⊢ʰ![N;𝔸] (A 🡒 A) := by
  haveI : ⊢ʰ![N;𝔸] ((A 🡒 (A 🡒 A) 🡒 A) 🡒 (A 🡒 A 🡒 A) 🡒 (A 🡒 A)) := implyS;
  haveI : ⊢ʰ![N;𝔸] ((A 🡒 A 🡒 A) 🡒 (A 🡒 A)) := mdp this implyK;
  haveI : ⊢ʰ![N;𝔸] (A 🡒 A) := mdp this implyK;
  exact this;

noncomputable def ofSubsetAxm (hsub : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ![N;𝔸₁] A) → ⊢ʰ![N;𝔸₂] A := λ h => by
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

end ProofHilbert


abbrev ProvableHilbert (𝔸 : Axioms α) (A : Formula α) : Prop := Nonempty (⊢ʰ![N;𝔸] A)

end N

end Modal

notation:50 "⊢ʰ[N;" 𝔸 "] " A:51 => Modal.N.ProvableHilbert 𝔸 A
notation:50 "⊬ʰ[N;" 𝔸 "] " A:51 => ¬(Modal.N.ProvableHilbert 𝔸 A)

namespace Modal

namespace N.ProvableHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ 𝔸 → ⊢ʰ[N;𝔸] A := λ h => ⟨ProofHilbert.axm h⟩
@[simp, grind .] lemma implyK : ⊢ʰ[N;𝔸] A 🡒 B 🡒 A := ⟨ProofHilbert.implyK⟩
@[simp, grind .] lemma implyS : ⊢ʰ[N;𝔸] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofHilbert.implyS⟩
@[simp, grind .] lemma efq : ⊢ʰ[N;𝔸] ⊥ 🡒 A := ⟨ProofHilbert.efq⟩
@[simp, grind .] lemma dne : ⊢ʰ[N;𝔸] ∼∼A 🡒 A := ⟨ProofHilbert.dne⟩
@[simp, grind .] lemma andElimL : ⊢ʰ[N;𝔸] (A ⋏ B) 🡒 A := ⟨ProofHilbert.andElimL⟩
@[simp, grind .] lemma andElimR : ⊢ʰ[N;𝔸] (A ⋏ B) 🡒 B := ⟨ProofHilbert.andElimR⟩
@[simp, grind .] lemma andIntro : ⊢ʰ[N;𝔸] A 🡒 B 🡒 (A ⋏ B) := ⟨ProofHilbert.andIntro⟩
@[simp, grind .] lemma impId : ⊢ʰ[N;𝔸] A 🡒 A := ⟨ProofHilbert.impId⟩
@[simp, grind .] lemma orElim : ⊢ʰ[N;𝔸] A ⋎ B 🡒 (A 🡒 C) 🡒 (B 🡒 C) 🡒 C := ⟨ProofHilbert.orElim⟩

@[grind =>] lemma mdp : (⊢ʰ[N;𝔸] A 🡒 B) → (⊢ʰ[N;𝔸] A) → ⊢ʰ[N;𝔸] B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[grind =>] lemma mdp₂ (hABC : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C) (hA : ⊢ʰ[N;𝔸] A) (hB : ⊢ʰ[N;𝔸] B) : ⊢ʰ[N;𝔸] C := mdp (mdp hABC hA) hB
@[grind =>] lemma mdp₃ (hABCD : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C 🡒 D) (hA : ⊢ʰ[N;𝔸] A) (hB : ⊢ʰ[N;𝔸] B) (hC : ⊢ʰ[N;𝔸] C) : ⊢ʰ[N;𝔸] D := mdp (mdp₂ hABCD hA hB) hC

@[grind <=] lemma af : (⊢ʰ[N;𝔸] A) → ⊢ʰ[N;𝔸] B 🡒 A := λ ⟨h⟩ => ⟨ProofHilbert.af h⟩
@[grind <=] lemma nec : (⊢ʰ[N;𝔸] A) → ⊢ʰ[N;𝔸] □A := λ ⟨h⟩ => ⟨ProofHilbert.nec h⟩
@[grind .] lemma lem : ⊢ʰ[N;𝔸] A ⋎ ∼A := by simp;

lemma andElimLRule (hAB : ⊢ʰ[N;𝔸] A ⋏ B) : ⊢ʰ[N;𝔸] A := mdp andElimL hAB
lemma andElimRRule (hAB : ⊢ʰ[N;𝔸] A ⋏ B) : ⊢ʰ[N;𝔸] B := mdp andElimR hAB
lemma andIntroRule (hA : ⊢ʰ[N;𝔸] A) (hB : ⊢ʰ[N;𝔸] B) : ⊢ʰ[N;𝔸] A ⋏ B := mdp₂ andIntro hA hB

lemma orElimRule (hAB : ⊢ʰ[N;𝔸] A ⋎ B) (hAC : ⊢ʰ[N;𝔸] A 🡒 C) (hBC : ⊢ʰ[N;𝔸] B 🡒 C) : ⊢ʰ[N;𝔸] C := mdp₃ orElim hAB hAC hBC

@[simp, grind .] lemma verum : ⊢ʰ[N;𝔸] (⊤ : Formula α) := by simp;

lemma ofSubsetAxm (h : 𝔸₁ ⊆ 𝔸₂) : (⊢ʰ[N;𝔸₁] A) → ⊢ʰ[N;𝔸₂] A := λ ⟨h₁⟩ => ⟨ProofHilbert.ofSubsetAxm h h₁⟩

@[grind <=] lemma efqRule (hA : ⊢ʰ[N;𝔸] ⊥) : ⊢ʰ[N;𝔸] A := mdp efq hA

@[grind =>]
lemma consistent_of_unprovable (h : ⊬ʰ[N;𝔸] A) : ⊬ʰ[N;𝔸] ⊥ := by
  contrapose! h;
  apply efqRule h;


@[grind =>] lemma dneRule (hA : ⊢ʰ[N;𝔸] ∼∼A) : ⊢ʰ[N;𝔸] A := mdp dne hA

lemma ctx_mdp {B} (hCAB : ⊢ʰ[N;𝔸] C 🡒 A 🡒 B) (hCA : ⊢ʰ[N;𝔸] C 🡒 A) : ⊢ʰ[N;𝔸] C 🡒 B := mdp₂ implyS hCAB hCA
lemma ctx_mdp₂ (hABCD : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C 🡒 D) (hABC : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C) : ⊢ʰ[N;𝔸] A 🡒 B 🡒 D := ctx_mdp (ctx_mdp (af implyS) hABCD) hABC

lemma impTransRule (hAB : ⊢ʰ[N;𝔸] A 🡒 B) (hBC : ⊢ʰ[N;𝔸] B 🡒 C) : ⊢ʰ[N;𝔸] A 🡒 C := by
  have : ⊢ʰ[N;𝔸] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := implyS;
  have : ⊢ʰ[N;𝔸] (A 🡒 B) 🡒 (A 🡒 C) := mdp implyS $ mdp₂ implyS (af $ af $ hBC) hAB;
  exact mdp this hAB;

lemma imp₃Swap (hABC : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C) : ⊢ʰ[N;𝔸] B 🡒 A 🡒 C := by
  apply ctx_mdp₂;
  . apply af hABC;
  . apply implyK;

lemma impTrans' : ⊢ʰ[N;𝔸] (B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := impTransRule (imp₃Swap (af impId)) implyS

lemma impTrans : ⊢ʰ[N;𝔸] (A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C) := by
  apply imp₃Swap impTrans';


lemma lconjElim {X : List _} (hA : A ∈ X) : ⊢ʰ[N;𝔸] ⋀X 🡒 A := by
  match X with
  | [] => contradiction;
  | [B] => grind;
  | B :: C :: X =>
    simp only [List.mem_cons] at hA;
    rcases hA with (rfl | rfl | hX);
    . simp;
    . apply impTransRule;
      . exact andElimR;
      . exact lconjElim (by grind);
    . apply impTransRule;
      . exact andElimR;
      . exact lconjElim (by grind);
lemma lconjElimRule {X : List _} (hA : A ∈ X) (hAB : ⊢ʰ[N;𝔸] ⋀X) : ⊢ʰ[N;𝔸] A := mdp (lconjElim hA) hAB

lemma fconjElim {X : Finset _} (hA : A ∈ X) : ⊢ʰ[N;𝔸] ⋀X 🡒 A := lconjElim (X := X.toList) (by simpa)
lemma fconjElimRule {X : Finset _} (hA : A ∈ X) (hAB : ⊢ʰ[N;𝔸] ⋀X) : ⊢ʰ[N;𝔸] A := mdp (fconjElim hA) hAB

lemma lconjIntro {X : List _} (hA : ∀ A ∈ X, ⊢ʰ[N;𝔸] A) : ⊢ʰ[N;𝔸] ⋀X := by
  match X with
  | [] => simp;
  | [A] => grind;
  | A :: B :: X =>
    simp only [List.mem_cons] at hA ⊢;
    apply andIntroRule;
    . apply hA;
      grind;
    . apply lconjIntro;
      grind;
lemma fconjIntro {X : Finset _} (hA : ∀ A ∈ X, ⊢ʰ[N;𝔸] A) : ⊢ʰ[N;𝔸] ⋀X := lconjIntro (X := X.toList) (by simpa)

lemma ctx_af {B} (hCA : ⊢ʰ[N;𝔸] C 🡒 A) : ⊢ʰ[N;𝔸] C 🡒 B 🡒 A := impTransRule hCA implyK

lemma ctx_impTransRule (hAB : ⊢ʰ[N;𝔸] C 🡒 A 🡒 B) (hBC : ⊢ʰ[N;𝔸] C 🡒 B 🡒 D) : ⊢ʰ[N;𝔸] C 🡒 A 🡒 D := ctx_mdp (impTransRule hAB $ impTrans) hBC

lemma ctxAndIntroRule (hA : ⊢ʰ[N;𝔸] C 🡒 A) (hB : ⊢ʰ[N;𝔸] C 🡒 B) : ⊢ʰ[N;𝔸] C 🡒 (A ⋏ B) := by
  exact ctx_mdp (impTransRule hA $ andIntro) hB;

lemma ctxOrElimRule (hAB : ⊢ʰ[N;𝔸] C 🡒 A ⋎ B) (hAC : ⊢ʰ[N;𝔸] C 🡒 A 🡒 D) (hBC : ⊢ʰ[N;𝔸] C 🡒 B 🡒 D) : ⊢ʰ[N;𝔸] C 🡒 D :=
  ctx_mdp (ctx_mdp (impTransRule hAB orElim) hAC) hBC

lemma ctxLconjIntroRule {X : List _} (hA : ∀ A ∈ X, ⊢ʰ[N;𝔸] C 🡒 A) : ⊢ʰ[N;𝔸] C 🡒 ⋀X := by
  match X with
  | [] => apply af; simp;
  | [A] => grind;
  | A :: B :: Y =>
    apply ctxAndIntroRule;
    . apply hA; grind;
    . apply ctxLconjIntroRule; grind;

lemma ctxFconjIntroRule {X : Finset _} (hA : ∀ A ∈ X, ⊢ʰ[N;𝔸] C 🡒 A) : ⊢ʰ[N;𝔸] C 🡒 ⋀X := ctxLconjIntroRule (X := X.toList) (by simpa)

lemma lconj_subset {X Y : List _} (hsub : X ⊆ Y) : ⊢ʰ[N;𝔸] ⋀Y 🡒 ⋀X := by
  apply ctxLconjIntroRule;
  intro A hA;
  apply lconjElim;
  apply hsub hA

lemma sconj_subset {X Y : Finset _} (hsub : X ⊆ Y) : ⊢ʰ[N;𝔸] ⋀Y 🡒 ⋀X := lconj_subset (X := X.toList) (Y := Y.toList) $ by
  grind [Finset.mem_toList];

lemma uncurry {A B C} (h : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C) : ⊢ʰ[N;𝔸] (A ⋏ B) 🡒 C := ctx_mdp (impTransRule andElimL h) andElimR

lemma curry {A B C} (h : ⊢ʰ[N;𝔸] (A ⋏ B) 🡒 C) : ⊢ʰ[N;𝔸] A 🡒 B 🡒 C := by
  have h₁ : ⊢ʰ[N;𝔸] A 🡒 B 🡒 (A ⋏ B) := andIntro;
  have h₂ : ⊢ʰ[N;𝔸] A 🡒 (A ⋏ B 🡒 C) := af h;
  exact ctx_impTransRule h₁ h₂;

@[induction_eliminator]
protected lemma rec
  {motive  : (A : Formula α) → (⊢ʰ[N;𝔸] A) → Prop}
  (axm     : ∀ {A}, (h : A ∈ 𝔸) → motive A (axm h))
  (mdp     : ∀ {A B}, {hAB : ⊢ʰ[N;𝔸] A 🡒 B} → {hA : ⊢ʰ[N;𝔸] A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (nec     : ∀ {A}, {hA : ⊢ʰ[N;𝔸] A} → (motive A hA) → (motive (□A) (nec hA)))
  (implyK  : ∀ {A B}, (motive (A 🡒 B 🡒 A) implyK))
  (implyS  : ∀ {A B C}, (motive ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)) implyS))
  (efq     : ∀ {A}, (motive (⊥ 🡒 A) efq))
  (dne     : ∀ {A}, (motive (∼∼A 🡒 A) dne))
  (andElimL : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (andIntro : ∀ {A B}, (motive (A 🡒 B 🡒 (A ⋏ B)) andIntro))
  (orElim   : ∀ {A B C}, (motive (A ⋎ B 🡒 (A 🡒 C) 🡒 (B 🡒 C) 🡒 C) orElim))
  : ∀ {A}, (d : ⊢ʰ[N;𝔸] A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end N.ProvableHilbert


def N.FinitelyDerivableHilbert (𝔸 : Axioms α) (X : Finset (Formula α)) (A : Formula α) := ⊢ʰ[N;𝔸] ⋀X 🡒 A

end Modal

notation:50 X:51 " ⊢ʰ[N;" 𝔸 "] " A:51 => Modal.N.FinitelyDerivableHilbert 𝔸 X A

namespace Modal

namespace N.FinitelyDerivableHilbert

variable {𝔸 : Axioms α} {X : Finset (Formula α)} {A B C : Formula α}

open N.ProvableHilbert

lemma iff_empty_derivable : (⊢ʰ[N;𝔸] A) ↔ ((∅ : Finset (Formula α)) ⊢ʰ[N;𝔸] A) := by
  unfold FinitelyDerivableHilbert;
  constructor;
  . intro h;
    exact af $ h;
  . intro h;
    exact mdp h (by simp);

lemma to_ctx [DecidableEq α] : (X ⊢ʰ[N;𝔸] A 🡒 B) → ((insert A X) ⊢ʰ[N;𝔸] B) := by
  unfold FinitelyDerivableHilbert;
  intro h;
  apply impTransRule;
  . show ⊢ʰ[N;𝔸] ⋀insert A X 🡒 (⋀X ⋏ A);
    apply ctxAndIntroRule;
    . apply sconj_subset;
      grind;
    . apply fconjElim;
      grind;
  . exact uncurry h;

lemma from_ctx [DecidableEq α] : ((insert A X) ⊢ʰ[N;𝔸] B) → (X ⊢ʰ[N;𝔸] A 🡒 B) := by
  unfold FinitelyDerivableHilbert;
  intro h;
  apply curry;
  apply impTransRule;
  . show ⊢ʰ[N;𝔸] (⋀X ⋏ A) 🡒 ⋀(insert A X);
    apply ctxFconjIntroRule;
    intro C hC;
    simp only [Finset.mem_insert] at hC;
    rcases hC with (rfl | hC);
    . grind;
    . apply impTransRule;
      . exact andElimL;
      . exact fconjElim hC;
  . exact h;

lemma of_mem_ctx (hA : A ∈ X) : X ⊢ʰ[N;𝔸] A := by
  unfold FinitelyDerivableHilbert;
  apply ProvableHilbert.fconjElim hA;

lemma mdp (hAB : X ⊢ʰ[N;𝔸] A 🡒 B) (hA : X ⊢ʰ[N;𝔸] A) : X ⊢ʰ[N;𝔸] B := by
  unfold FinitelyDerivableHilbert at hAB hA ⊢;
  exact ProvableHilbert.ctx_mdp hAB hA;

lemma weakening (hsub : X ⊆ Y) (hX : X ⊢ʰ[N;𝔸] A) : Y ⊢ʰ[N;𝔸] A := by
  unfold FinitelyDerivableHilbert at hX ⊢;
  apply ProvableHilbert.impTransRule ?_ hX;
  apply ProvableHilbert.sconj_subset hsub;

lemma of_provable (hA : ⊢ʰ[N;𝔸] A) : X ⊢ʰ[N;𝔸] A := by
  exact weakening (show ∅ ⊆ X by simp) $ iff_empty_derivable.mp hA;

lemma orElim (hAB : X ⊢ʰ[N;𝔸] A ⋎ B) (hAC : X ⊢ʰ[N;𝔸] A 🡒 C) (hBC : X ⊢ʰ[N;𝔸] B 🡒 C) : X ⊢ʰ[N;𝔸] C := ctxOrElimRule hAB hAC hBC

lemma lem_elim (hA : X ⊢ʰ[N;𝔸] A 🡒 B) (hNA : X ⊢ʰ[N;𝔸] ∼A 🡒 B) : X ⊢ʰ[N;𝔸] B := by
  apply orElim (of_provable lem) hA hNA;

end N.FinitelyDerivableHilbert


namespace N.ProvableHilbert

open N.FinitelyDerivableHilbert

variable [DecidableEq α] {𝔸 : Axioms α} {A B C D : Formula α}

lemma www (h : ⊢ʰ[N;𝔸] B 🡒 A) : ⊢ʰ[N;𝔸] (A 🡒 C) 🡒 B 🡒 C := by
  apply iff_empty_derivable.mpr;
  apply from_ctx;
  apply from_ctx;
  apply FinitelyDerivableHilbert.mdp;
  . show ({B, A 🡒 C} : Finset (Formula α)) ⊢ʰ[N;𝔸] A 🡒 C;
    apply of_mem_ctx (by grind);
  . apply FinitelyDerivableHilbert.mdp;
    . show ({B, A 🡒 C} : Finset (Formula α)) ⊢ʰ[N;𝔸] B 🡒 A;
      apply of_provable h;
    . apply of_mem_ctx (by grind);

@[simp, grind .]
lemma dni : ⊢ʰ[N;𝔸] A 🡒 ∼∼A := by
  apply iff_empty_derivable.mpr;
  apply from_ctx;
  apply from_ctx;
  apply FinitelyDerivableHilbert.mdp;
  . show ({∼A, A} : Finset (Formula α)) ⊢ʰ[N;𝔸] ∼A;
    apply of_mem_ctx (by grind);
  . show ({∼A, A} : Finset (Formula α)) ⊢ʰ[N;𝔸] A;
    apply of_mem_ctx (by grind);

lemma ctx_nc (hCA : ⊢ʰ[N;𝔸] C 🡒 A) : ⊢ʰ[N;𝔸] C 🡒 (∼A 🡒 D) := by
  apply iff_empty_derivable.mpr;
  apply from_ctx;
  apply from_ctx;
  replace hCA : ({∼A, C} : Finset (Formula α)) ⊢ʰ[N;𝔸] A  := weakening (by grind) $ to_ctx $ iff_empty_derivable.mp hCA;
  have : ({∼A, C} : Finset (Formula α)) ⊢ʰ[N;𝔸] ∼A := of_mem_ctx (by grind);
  have : ({∼A, C} : Finset (Formula α)) ⊢ʰ[N;𝔸] ⊥ := .mdp this hCA;
  have : ({∼A, C} : Finset (Formula α)) ⊢ʰ[N;𝔸] D := .mdp (of_provable (by simp)) this;
  exact this;

lemma ctx_nc2 (hCA : ⊢ʰ[N;𝔸] C 🡒 ∼A) : ⊢ʰ[N;𝔸] C 🡒 (A 🡒 D) := by
  apply impTransRule $ ctx_nc (A := ∼A) (D := D) hCA;
  apply www dni;


end N.ProvableHilbert


end Modal

end
