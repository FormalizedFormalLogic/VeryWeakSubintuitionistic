module

public import VeryWeakSubintuitionistic.Modal.Proof.Basic

@[expose] public section

namespace Modal

variable {α : Type*}

inductive ProofN (Λ : Axioms α) : Formula α → Type _
| axm {A}        : A ∈ Λ → ProofN Λ A
| implyK {A B}   : ProofN Λ $ A 🡒 B 🡒 A
| implyS {A B C} : ProofN Λ $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| efq {A}            : ProofN Λ $ ⊥ 🡒 A
| dne {A}            : ProofN Λ $ ∼∼A 🡒 A
| andElimL {A B} : ProofN Λ $ (A ⋏ B) 🡒 A
| andElimR {A B} : ProofN Λ $ (A ⋏ B) 🡒 B
| andIntro {A B} : ProofN Λ $ A 🡒 B 🡒 (A ⋏ B)
| mdp {A B}      : ProofN Λ (A 🡒 B) → ProofN Λ A → ProofN Λ B
| nec {A}        : ProofN Λ A → ProofN Λ (□A)
infix:25 " ⊢ᴺ! " => ProofN

namespace ProofN

variable {Λ Λ₁ Λ₂ : Axioms α} {A B C : Formula α}

def af {A B} : Λ ⊢ᴺ! A → Λ ⊢ᴺ! (B 🡒 A) := λ h => mdp implyK h

def impId : Λ ⊢ᴺ! A 🡒 A := by
  haveI : Λ ⊢ᴺ! (A 🡒 (A 🡒 A) 🡒 A) 🡒 (A 🡒 A 🡒 A) 🡒 (A 🡒 A) := implyS;
  haveI : Λ ⊢ᴺ! (A 🡒 A 🡒 A) 🡒 (A 🡒 A) := mdp this implyK;
  haveI : Λ ⊢ᴺ! A 🡒 A := mdp this implyK;
  exact this;

noncomputable def ofSubsetAxm (hsub : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ᴺ! A → Λ₂ ⊢ᴺ! A := λ h => by
  induction h with
  | axm h₁ => exact axm (hsub h₁)
  | implyK => exact implyK
  | implyS => exact implyS
  | efq => exact efq
  | dne => exact dne
  | andElimL => exact andElimL
  | andElimR => exact andElimR
  | andIntro => exact andIntro
  | mdp _ _ ihAB ihA => exact mdp ihAB ihA
  | nec _ ihA => exact nec ihA

end ProofN



abbrev ProvableN (Λ : Axioms α) (A : Formula α) : Prop := Nonempty (Λ ⊢ᴺ! A)
infix:25 " ⊢ᴺ " => ProvableN

abbrev UnprovableN (Λ : Axioms α) (A : Formula α) : Prop := ¬(Λ ⊢ᴺ A)
infix:25 " ⊬ᴺ " => UnprovableN

namespace ProvableN

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>] lemma axm : A ∈ Λ → Λ ⊢ᴺ A := λ h => ⟨ProofN.axm h⟩
@[simp, grind .] lemma implyK : Λ ⊢ᴺ A 🡒 B 🡒 A := ⟨ProofN.implyK⟩
@[simp, grind .] lemma implyS : Λ ⊢ᴺ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofN.implyS⟩
@[simp, grind .] lemma efq : Λ ⊢ᴺ ⊥ 🡒 A := ⟨ProofN.efq⟩
@[simp, grind .] lemma dne : Λ ⊢ᴺ ∼∼A 🡒 A := ⟨ProofN.dne⟩
@[simp, grind .] lemma andElimL : Λ ⊢ᴺ (A ⋏ B) 🡒 A := ⟨ProofN.andElimL⟩
@[simp, grind .] lemma andElimR : Λ ⊢ᴺ (A ⋏ B) 🡒 B := ⟨ProofN.andElimR⟩
@[simp, grind .] lemma andIntro : Λ ⊢ᴺ A 🡒 B 🡒 (A ⋏ B) := ⟨ProofN.andIntro⟩
@[simp, grind .] lemma impId : Λ ⊢ᴺ A 🡒 A := ⟨ProofN.impId⟩
@[grind =>] lemma mdp : Λ ⊢ᴺ A 🡒 B → Λ ⊢ᴺ A → Λ ⊢ᴺ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofN.mdp h₁ h₂⟩
@[grind <=] lemma af : Λ ⊢ᴺ A → Λ ⊢ᴺ B 🡒 A := λ ⟨h⟩ => ⟨ProofN.af h⟩
@[grind <=] lemma nec : Λ ⊢ᴺ A → Λ ⊢ᴺ □A := λ ⟨h⟩ => ⟨ProofN.nec h⟩
@[grind .] lemma lem : Λ ⊢ᴺ A ⋎ ∼A := by simp;

lemma andElimLRule (hAB : Λ ⊢ᴺ A ⋏ B) : Λ ⊢ᴺ A := mdp andElimL hAB
lemma andElimRRule (hAB : Λ ⊢ᴺ A ⋏ B) : Λ ⊢ᴺ B := mdp andElimR hAB
lemma andIntroRule (hA : Λ ⊢ᴺ A) (hB : Λ ⊢ᴺ B) : Λ ⊢ᴺ A ⋏ B := mdp (mdp andIntro hA) hB

@[simp, grind .] lemma verum : Λ ⊢ᴺ ⊤ := by simp;

lemma ofSubsetAxm (h : Λ₁ ⊆ Λ₂) : Λ₁ ⊢ᴺ A → Λ₂ ⊢ᴺ A := λ ⟨h₁⟩ => ⟨ProofN.ofSubsetAxm h h₁⟩

@[grind <=] lemma efqRule (hA : Λ ⊢ᴺ ⊥) : Λ ⊢ᴺ A := mdp efq hA

@[grind =>]
lemma consistent_of_unprovable (h : Λ ⊬ᴺ A) : Λ ⊬ᴺ ⊥ := by
  contrapose! h;
  apply efqRule h;


@[grind =>] lemma dneRule (hA : Λ ⊢ᴺ ∼∼A) : Λ ⊢ᴺ A := mdp dne hA

lemma impTransRule (hAB : Λ ⊢ᴺ A 🡒 B) (hBC : Λ ⊢ᴺ B 🡒 C) : Λ ⊢ᴺ A 🡒 C := by

  sorry;

lemma lconjElim {X : List _} (hA : A ∈ X) : Λ ⊢ᴺ ⋀X 🡒 A := by
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
lemma lconjElimRule {X : List _} (hA : A ∈ X) (hAB : Λ ⊢ᴺ ⋀X) : Λ ⊢ᴺ A := mdp (lconjElim hA) hAB

lemma fconjElim {X : Finset _} (hA : A ∈ X) : Λ ⊢ᴺ ⋀X 🡒 A := lconjElim (X := X.toList) (by simpa)
lemma fconjElimRule {X : Finset _} (hA : A ∈ X) (hAB : Λ ⊢ᴺ ⋀X) : Λ ⊢ᴺ A := mdp (fconjElim hA) hAB

lemma lconjIntro {X : List _} (hA : ∀ A ∈ X, Λ ⊢ᴺ A) : Λ ⊢ᴺ ⋀X := by
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
lemma fconjIntro {X : Finset _} (hA : ∀ A ∈ X, Λ ⊢ᴺ A) : Λ ⊢ᴺ ⋀X := lconjIntro (X := X.toList) (by simpa)

lemma ctx_mdp {B} (hCAB : Λ ⊢ᴺ C 🡒 A 🡒 B) (hCA : Λ ⊢ᴺ C 🡒 A) : Λ ⊢ᴺ C 🡒 B := mdp (mdp implyS hCAB) hCA

lemma ctx_af {B} (hCA : Λ ⊢ᴺ C 🡒 A) : Λ ⊢ᴺ C 🡒 B 🡒 A := impTransRule hCA implyK

lemma ctxAndIntroRule (hA : Λ ⊢ᴺ C 🡒 A) (hB : Λ ⊢ᴺ C 🡒 B) : Λ ⊢ᴺ C 🡒 (A ⋏ B) := by
  exact ctx_mdp (impTransRule hA $ andIntro) hB;

lemma ctxLconjIntroRule {X : List _} (hA : ∀ A ∈ X, Λ ⊢ᴺ C 🡒 A) : Λ ⊢ᴺ C 🡒 ⋀X := by
  match X with
  | [] => apply af; simp;
  | [A] => grind;
  | A :: B :: Y =>
    apply ctxAndIntroRule;
    . apply hA; grind;
    . apply ctxLconjIntroRule; grind;

lemma ctxFconjIntroRule {X : Finset _} (hA : ∀ A ∈ X, Λ ⊢ᴺ C 🡒 A) : Λ ⊢ᴺ C 🡒 ⋀X := ctxLconjIntroRule (X := X.toList) (by simpa)

lemma lconj_subset {X Y : List _} (hsub : X ⊆ Y) : Λ ⊢ᴺ ⋀Y 🡒 ⋀X := by
  apply ctxLconjIntroRule;
  intro A hA;
  apply lconjElim;
  apply hsub hA

lemma sconj_subset {X Y : Finset _} (hsub : X ⊆ Y) : Λ ⊢ᴺ ⋀Y 🡒 ⋀X := lconj_subset (X := X.toList) (Y := Y.toList) $ by
  grind [Finset.mem_toList];

lemma uncurry {A B} (h : Λ ⊢ᴺ A 🡒 B 🡒 C) : Λ ⊢ᴺ (A ⋏ B) 🡒 C := by
  sorry;

lemma curry {A B} (h : Λ ⊢ᴺ (A ⋏ B) 🡒 C) : Λ ⊢ᴺ A 🡒 B 🡒 C := by

  sorry;

@[induction_eliminator]
protected lemma rec
  {motive  : (A : Formula α) → (Λ ⊢ᴺ A) → Prop}
  (axm     : ∀ {A}, (h : A ∈ Λ) → motive A (axm h))
  (mdp     : ∀ {A B}, {hAB : Λ ⊢ᴺ A 🡒 B} → {hA : Λ ⊢ᴺ A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (nec     : ∀ {A}, {hA : Λ ⊢ᴺ A} → (motive A hA) → (motive (□A) (nec hA)))
  (implyK  : ∀ {A B}, (motive (A 🡒 B 🡒 A) implyK))
  (implyS  : ∀ {A B C}, (motive ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)) implyS))
  (efq     : ∀ {A}, (motive (⊥ 🡒 A) efq))
  (dne     : ∀ {A}, (motive (∼∼A 🡒 A) dne))
  (andElimL : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (andIntro : ∀ {A B}, (motive (A 🡒 B 🡒 (A ⋏ B)) andIntro))
  : ∀ {A}, (d : Λ ⊢ᴺ A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end ProvableN


def FinitelyDerivableN (Λ : Axioms α) (X : Finset (Formula α)) (A : Formula α) := Λ ⊢ᴺ ⋀X 🡒 A
notation:25 X " ⊢ᴺ[" Λ "] " A => FinitelyDerivableN Λ X A


namespace FinitelyDerivableN

variable [DecidableEq α]
variable {Λ : Axioms α} {X : Finset (Formula α)} {A B C : Formula α}

open ProvableN

omit [DecidableEq α] in
lemma iff_empty_derivable : (Λ ⊢ᴺ A) ↔ (∅ ⊢ᴺ[Λ] A)  := by
  unfold FinitelyDerivableN;
  constructor;
  . intro h;
    exact af $ h;
  . intro h;
    exact mdp h (by simp);

lemma to_ctx : (X ⊢ᴺ[Λ] A 🡒 B) → ((insert A X) ⊢ᴺ[Λ] B) := by
  unfold FinitelyDerivableN;
  intro h;
  apply impTransRule;
  . show Λ ⊢ᴺ ⋀insert A X 🡒 (⋀X ⋏ A);
    apply ctxAndIntroRule;
    . apply sconj_subset;
      grind;
    . apply fconjElim;
      grind;
  . exact uncurry h;

lemma from_ctx : ((insert A X) ⊢ᴺ[Λ] B) → (X ⊢ᴺ[Λ] A 🡒 B) := by
  unfold FinitelyDerivableN;
  intro h;
  apply curry;
  apply impTransRule;
  . show Λ ⊢ᴺ (⋀X ⋏ A) 🡒 ⋀(insert A X);
    apply ctxFconjIntroRule;
    intro C hC;
    simp only [Finset.mem_insert] at hC;
    rcases hC with (rfl | hC);
    . grind;
    . apply impTransRule;
      . exact andElimL;
      . exact fconjElim hC;
  . exact h;

omit [DecidableEq α] in
lemma of_mem_ctx (hA : A ∈ X) : X ⊢ᴺ[Λ] A := by
  unfold FinitelyDerivableN;
  apply ProvableN.fconjElim hA;

omit [DecidableEq α] in
lemma mdp (hAB : X ⊢ᴺ[Λ] A 🡒 B) (hA : X ⊢ᴺ[Λ] A) : X ⊢ᴺ[Λ] B := by
  unfold FinitelyDerivableN at hAB hA ⊢;
  exact ProvableN.ctx_mdp hAB hA;

omit [DecidableEq α] in
lemma weakening (hsub : X ⊆ Y) (hX : X ⊢ᴺ[Λ] A) : Y ⊢ᴺ[Λ] A := by
  unfold FinitelyDerivableN at hX ⊢;
  apply ProvableN.impTransRule ?_ hX;
  apply ProvableN.sconj_subset hsub;

omit [DecidableEq α] in
lemma of_provable (hA : Λ ⊢ᴺ A) : X ⊢ᴺ[Λ] A := by
  exact weakening (show ∅ ⊆ X by simp) $ iff_empty_derivable.mp hA;

lemma orElim (hAB : X ⊢ᴺ[Λ] A ⋎ B) (hA : X ⊢ᴺ[Λ] A 🡒 C) (hB : X ⊢ᴺ[Λ] B 🡒 C) : X ⊢ᴺ[Λ] C := by
  sorry;

lemma lem_elim (hA : X ⊢ᴺ[Λ] A 🡒 B) (hNA : X ⊢ᴺ[Λ] ∼A 🡒 B) : X ⊢ᴺ[Λ] B := by
  apply orElim (of_provable lem) hA hNA;

end FinitelyDerivableN


namespace ProvableN

open FinitelyDerivableN

variable [DecidableEq α] {Λ : Axioms α} {A B C D : Formula α}

lemma www (h : Λ ⊢ᴺ B 🡒 A) : Λ ⊢ᴺ (A 🡒 C) 🡒 B 🡒 C := by
  apply iff_empty_derivable.mpr;
  apply from_ctx;
  apply from_ctx;
  apply FinitelyDerivableN.mdp;
  . show {B, A 🡒 C} ⊢ᴺ[Λ] A 🡒 C;
    apply of_mem_ctx (by grind);
  . apply FinitelyDerivableN.mdp;
    . show {B, A 🡒 C} ⊢ᴺ[Λ] B 🡒 A;
      apply of_provable h;
    . apply of_mem_ctx (by grind);

@[simp, grind .]
lemma dni : Λ ⊢ᴺ A 🡒 ∼∼A := by
  apply iff_empty_derivable.mpr;
  apply from_ctx;
  apply from_ctx;
  apply FinitelyDerivableN.mdp;
  . show {∼A, A} ⊢ᴺ[Λ] ∼A;
    apply of_mem_ctx (by grind);
  . show {∼A, A} ⊢ᴺ[Λ] A;
    apply of_mem_ctx (by grind);

lemma ctx_nc (hCA : Λ ⊢ᴺ C 🡒 A) : Λ ⊢ᴺ C 🡒 (∼A 🡒 D) := by
  apply iff_empty_derivable.mpr;
  apply from_ctx;
  apply from_ctx;
  replace hCA : {∼A, C} ⊢ᴺ[Λ] A  := weakening (by grind) $ to_ctx $ iff_empty_derivable.mp hCA;
  have : {∼A, C} ⊢ᴺ[Λ] ∼A := of_mem_ctx (by grind);
  have : {∼A, C} ⊢ᴺ[Λ] ⊥ := .mdp this hCA;
  have : {∼A, C} ⊢ᴺ[Λ] D := .mdp (of_provable (by simp)) this;
  exact this;

lemma ctx_nc2 (hCA : Λ ⊢ᴺ C 🡒 ∼A) : Λ ⊢ᴺ C 🡒 (A 🡒 D) := by
  apply impTransRule $ ctx_nc (A := ∼A) (D := D) hCA;
  apply www dni;


end ProvableN


end Modal

end
