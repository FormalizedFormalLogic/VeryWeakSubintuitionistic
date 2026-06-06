module

public import VeryWeakSubintuitionistic.Propositional.Proof.VFR.Basic
public import VeryWeakSubintuitionistic.Propositional.Kripke.Basic
public import VeryWeakSubintuitionistic.Propositional.FMT.Basic

@[expose] public section

structure ProofSystem (α : Type*) where
  proof : Formula α → Type*

namespace ProofSystem

infix:75 " ⊢! " => proof

abbrev Provable (S : ProofSystem α) (A : Formula α) := Nonempty (S ⊢! A)
infix:75 " ⊢ " => Provable

variable {S : ProofSystem α}

class ModusPonens (S : ProofSystem α) where
  mdp {A B} : S ⊢ (A 🡒 B) → S ⊢ A → S ⊢ B
export ModusPonens (mdp)
attribute [grind =>] ModusPonens.mdp

@[grind =>]
lemma mdp₂ [S.ModusPonens] : S ⊢ (A 🡒 B 🡒 C) → S ⊢ A → S ⊢ B → S ⊢ C := λ hABC hA hB => mdp (mdp hABC hA) hB


class AFortiori (S : ProofSystem α) where
  af {A B} : S ⊢ A → S ⊢ B 🡒 A
export AFortiori (af)
attribute [grind <=] AFortiori.af

class Verum (S : ProofSystem α) where
  verum : S ⊢ ⊤
export Verum (verum)
attribute [grind .] Verum.verum


class ImplicationIdentity (S : ProofSystem α) where
  impId {A} : S ⊢ A 🡒 A


class OrIntroAxiom (S : ProofSystem α) where
  axOrIntroL {A B} : S ⊢ A 🡒 (A ⋎ B)
  axOrIntroR {A B} : S ⊢ B 🡒 (A ⋎ B)
attribute [grind .] OrIntroAxiom.axOrIntroL OrIntroAxiom.axOrIntroR

class OrIntro (S : ProofSystem α) where
  orIntroL {A B} : S ⊢ A → S ⊢ A ⋎ B
  orIntroR {A B} : S ⊢ B → S ⊢ A ⋎ B
attribute [grind <=] OrIntro.orIntroL OrIntro.orIntroR

instance [S.ModusPonens] [S.OrIntroAxiom] : S.OrIntro where
  orIntroL := mdp OrIntroAxiom.axOrIntroL
  orIntroR := mdp OrIntroAxiom.axOrIntroR


class AndIntroAxiom (S : ProofSystem α) where
  axAndIntro {A B} : S ⊢ A 🡒 B 🡒 (A ⋏ B)
attribute [grind .] AndIntroAxiom.axAndIntro

class AndIntro (S : ProofSystem α) where
  andIntro {A B} : S ⊢ A → S ⊢ B → S ⊢ A ⋏ B
attribute [grind <=] AndIntro.andIntro

class ContextualAndIntro (S : ProofSystem α) where
  ctxAndIntro {A B C} : S ⊢ (A 🡒 B) → S ⊢ (A 🡒 C) → S ⊢ A 🡒 (B ⋏ C)

instance [S.ModusPonens] [S.AndIntroAxiom] : S.AndIntro where
  andIntro := λ hA hB => mdp₂ AndIntroAxiom.axAndIntro hA hB

instance [S.ModusPonens] [S.AFortiori] [S.ContextualAndIntro] [S.Verum] : S.AndIntro where
  andIntro := λ hA hB => mdp (ContextualAndIntro.ctxAndIntro (af hA) (af hB)) verum

class Explosive (S : ProofSystem α) where
  explosive {A} : S ⊢ ⊥ → S ⊢ A

class Disjunctive (S : ProofSystem α) where
  disjunctive {A B} : (S ⊢ A ⋎ B) → (S ⊢ A) ∨ (S ⊢ B)

end ProofSystem



abbrev VFRProofSystem (Λ : Axioms α) : ProofSystem α := ⟨λ A => Λ ⊢ᴿ! A⟩

namespace VFRProofSystem

open ProvableVFR

instance : (VFRProofSystem Λ).ModusPonens where
  mdp := λ ⟨hAB⟩ ⟨hA⟩ => ⟨.mdp hAB hA⟩

instance : (VFRProofSystem Λ).OrIntroAxiom where
  axOrIntroL := ⟨.orIntroL⟩
  axOrIntroR := ⟨.orIntroR⟩

instance : (VFRProofSystem Λ).ContextualAndIntro where
  ctxAndIntro := λ ⟨hAB⟩ ⟨hAC⟩ => ⟨.ruleC hAB hAC⟩

instance : (VFRProofSystem Λ).AFortiori where
  af := λ ⟨hA⟩ => ⟨.af hA⟩

instance : (VFRProofSystem Λ).Verum where
  verum := ⟨.verum⟩

@[induction_eliminator]
protected lemma rec_provable
  {motive          : (A : Formula α) → ((VFRProofSystem Λ) ⊢ A) → Prop}
  (axm             : ∀ {A}, (h : A ∈ Λ) → motive A (axm h))
  (mdp             : ∀ {A B}, {hAB : (VFRProofSystem Λ) ⊢ A 🡒 B} → {hA : (VFRProofSystem Λ) ⊢ A} → (motive (A 🡒 B) hAB) → (motive A hA) → (motive B (mdp hAB hA)))
  (af              : ∀ {A B}, {hA : (VFRProofSystem Λ) ⊢ A} → (motive A hA) → (motive (B 🡒 A) (af hA)))
  (ruleC           : ∀ {A B C}, {hAB : (VFRProofSystem Λ) ⊢ A 🡒 B} → {hAC : (VFRProofSystem Λ) ⊢ A 🡒 C} → (motive (A 🡒 B) hAB) → (motive (A 🡒 C) hAC) → (motive (A 🡒 (B ⋏ C)) (ruleC hAB hAC)))
  (ruleD           : ∀ {A B C}, {hAC : (VFRProofSystem Λ) ⊢ A 🡒 C} → {hBC : (VFRProofSystem Λ) ⊢ B 🡒 C} → (motive (A 🡒 C) hAC) → (motive (B 🡒 C) hBC) → (motive ((A ⋎ B) 🡒 C) (ruleD hAC hBC)))
  (ruleI           : ∀ {A B C}, {hAB : (VFRProofSystem Λ) ⊢ A 🡒 B} → {hBC : (VFRProofSystem Λ) ⊢ B 🡒 C} → (motive (A 🡒 B) hAB) → (motive (B 🡒 C) hBC) → (motive (A 🡒 C) (ruleI hAB hBC)))
  (ros             : ∀ {A B}, {hA : (VFRProofSystem Λ) ⊢ ∼A} → {hB : (VFRProofSystem Λ) ⊢ B} → (motive (∼A) hA) → (motive B hB) → (motive (∼(B 🡒 A)) (ros hA hB)))
  (distributeAndOr : ∀ {A B C : Formula α}, (motive ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) distributeAndOr))
  (impId           : ∀ {A}, (motive (A 🡒 A) impId))
  (andElimL        : ∀ {A B}, (motive ((A ⋏ B) 🡒 A) andElimL))
  (andElimR        : ∀ {A B}, (motive ((A ⋏ B) 🡒 B) andElimR))
  (orIntroL        : ∀ {A B}, (motive (A 🡒 (A ⋎ B)) orIntroL))
  (orIntroR        : ∀ {A B}, (motive (B 🡒 (A ⋎ B)) orIntroR))
  (efq             : ∀ {A}, (motive (⊥ 🡒 A) efq))
  : ∀ {A}, (d : (VFRProofSystem Λ) ⊢ A) → motive A d := by rintro A ⟨d⟩; induction d <;> grind;

end VFRProofSystem



namespace ProofSystem

@[grind]
def Slashable (S : ProofSystem α) : Formula α → Prop
  | #a => S ⊢ #a
  | ⊥ => False
  | A ⋎ B => Slashable S A ∨ Slashable S B
  | A ⋏ B => Slashable S A ∧ Slashable S B
  | A 🡒 B => (S ⊢ A 🡒 B) ∧ (Slashable S A → Slashable S B)
infix:25 " ∕ " => Slashable

variable {S : ProofSystem α} {A B C : Formula α}


@[grind =>]
lemma Slashable.mdp : S ∕ (A 🡒 B) → S ∕ A → S ∕ B := by grind;

@[grind .]
lemma provable_of_slashable [S.AndIntro] [S.OrIntro] : (S ∕ A) → (S ⊢ A) := by induction A with grind;

lemma disjunctive_of_iff_slashable_provable (h : ∀ {A}, S ∕ A ↔ S ⊢ A) : S.Disjunctive := ⟨by grind⟩

end ProofSystem


namespace VFRProofSystem

variable {S : ProofSystem α} {A B C : Formula α}

@[grind .]
lemma slashable_of_provable : ((VFRProofSystem ∅) ⊢ A) → ((VFRProofSystem ∅) ∕ A) := by rintro h; induction h with grind;

theorem disjunctive : (VFRProofSystem (α := α) ∅).Disjunctive := by
  apply ProofSystem.disjunctive_of_iff_slashable_provable;
  intro A;
  constructor;
  . exact ProofSystem.provable_of_slashable;
  . exact slashable_of_provable;

end VFRProofSystem

end section
