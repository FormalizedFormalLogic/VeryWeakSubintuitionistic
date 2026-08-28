module

public import VeryWeakSubintuitionistic.Propositional.Proof.VF
public import VeryWeakSubintuitionistic.Propositional.Kripke.Basic
public import VeryWeakSubintuitionistic.Propositional.FMT.Basic

@[expose] public section

@[grind]
def Slashable (𝔸 : Axioms α) : Formula α → Prop
  | #a => ⊢ʰ[VF;𝔸] #a
  | ⊥ => False
  | A ⋎ B => Slashable 𝔸 A ∨ Slashable 𝔸 B
  | A ⋏ B => Slashable 𝔸 A ∧ Slashable 𝔸 B
  | A 🡒 B => (⊢ʰ[VF;𝔸] A 🡒 B) ∧ (Slashable 𝔸 A → Slashable 𝔸 B)
infix:25 " ∕ " => Slashable

namespace Slashable

variable {𝔸 : Axioms α} {A B C : Formula α}

@[grind =>]
lemma mdp : 𝔸 ∕ (A 🡒 B) → 𝔸 ∕ A → 𝔸 ∕ B := by grind;

end Slashable


variable {𝔸 : Axioms α} {A B C : Formula α}

lemma provableVF_of_slashable : (𝔸 ∕ A) → (⊢ʰ[VF;𝔸] A) := by induction A <;> grind;

lemma disjunctive_of_iff_slashable_provable (h : ∀ {A}, 𝔸 ∕ A ↔ ⊢ʰ[VF;𝔸] A) : VF.Disjunctive 𝔸 := by
  constructor;
  grind;


namespace Formula

def IsClosedNegativeAxiom : Formula α → Prop
  | ∼A => A.Closed ∧ (⊢ʰ[Int;∅] ∼A)
  | _ => False

@[grind =]
lemma iff_isCNA : A.IsClosedNegativeAxiom ↔ (∃ B, A = ∼B ∧ B.Closed ∧ (⊢ʰ[Int;∅] ∼B)) := by
  match A with
  | #a | ⊥ | A ⋎ B | A ⋏ B => simp [IsClosedNegativeAxiom]
  | A 🡒 B => dsimp [IsClosedNegativeAxiom]; grind;

@[grind →]
lemma isClosed_of_isCNA {A : Formula α} : A.IsClosedNegativeAxiom → A.Closed := by grind;

end Formula



lemma provableInt_Int_of_provableVF_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : ⊢ʰ[VF;𝔸] A → ⊢ʰ[Int;∅] A := by
  intro h;
  induction h with
  | axm h => have := Fact.out (p := ∀ A ∈ 𝔸, A.IsClosedNegativeAxiom) _ h; grind;
  | _ => grind

instance consistency_VF_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : VF.Consistent 𝔸 := by
  constructor;
  by_contra hC;
  apply consistency_of_Int $ provableInt_Int_of_provableVF_CNAExtension hC;

lemma slashable_of_provableVF_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : (⊢ʰ[VF;𝔸] A) → (𝔸 ∕ A) := by
  intro h;
  induction h with
  | @axm B hB =>
    have := Fact.out (p := ∀ A ∈ 𝔸, A.IsClosedNegativeAxiom) _ hB;
    obtain ⟨C, rfl, hC₁, hC₂⟩ := Formula.iff_isCNA.mp this;
    constructor;
    . exact VF.ProvableHilbert.axm hB;
    . intro h;
      have : ⊢ʰ[Int;∅] C := provableInt_Int_of_provableVF_CNAExtension $ provableVF_of_slashable h;
      exact consistency_of_Int $ Int.ProvableHilbert.mdp hC₂ this;
  | _ => grind;

instance disjunctive_VF_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : VF.Disjunctive 𝔸 := by
  apply disjunctive_of_iff_slashable_provable;
  intro A;
  constructor;
  . exact provableVF_of_slashable;
  . exact slashable_of_provableVF_CNAExtension;
