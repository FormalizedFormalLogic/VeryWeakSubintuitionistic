module

public import VeryWeakSubintuitionistic.Propositional.Proof.VF
public import VeryWeakSubintuitionistic.Propositional.Kripke.Basic
public import VeryWeakSubintuitionistic.Propositional.FMT.Basic

@[expose] public section

@[grind]
def Slashable (Λ : Axioms α) : Formula α → Prop
  | #a => Λ ⊢ⱽ #a
  | ⊥ => False
  | A ⋎ B => Slashable Λ A ∨ Slashable Λ B
  | A ⋏ B => Slashable Λ A ∧ Slashable Λ B
  | A 🡒 B => (Λ ⊢ⱽ A 🡒 B) ∧ (Slashable Λ A → Slashable Λ B)
infix:25 " ∕ " => Slashable

namespace Slashable

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>]
lemma mdp : Λ ∕ (A 🡒 B) → Λ ∕ A → Λ ∕ B := by grind;

end Slashable


variable {Λ : Axioms α} {A B C : Formula α}

lemma provableVF_of_slashable : (Λ ∕ A) → (Λ ⊢ⱽ A) := by induction A <;> grind;

lemma disjunctive_of_iff_slashable_provable (h : ∀ {A}, Λ ∕ A ↔ Λ ⊢ⱽ A) : Λ.DisjunctiveVF := by
  constructor;
  grind;


namespace Formula

def IsClosedNegativeAxiom : Formula α → Prop
  | ∼A => A.Closed ∧ (∅ ⊢ᴵ ∼A)
  | _ => False

@[grind =]
lemma iff_isCNA : A.IsClosedNegativeAxiom ↔ (∃ B, A = ∼B ∧ B.Closed ∧ (∅ ⊢ᴵ ∼B)) := by
  match A with
  | #a | ⊥ | A ⋎ B | A ⋏ B => simp [IsClosedNegativeAxiom]
  | A 🡒 B => dsimp [IsClosedNegativeAxiom]; grind;

end Formula



lemma provableInt_Int_of_provableVF_CNAExtension [Fact (∀ A ∈ Λ, A.IsClosedNegativeAxiom)] : Λ ⊢ⱽ A → ∅ ⊢ᴵ A := by
  intro h;
  induction h with
  | axm h => have := Fact.out (p := ∀ A ∈ Λ, A.IsClosedNegativeAxiom) _ h; grind;
  | _ => grind

instance consistency_VF_CNAExtension [Fact (∀ A ∈ Λ, A.IsClosedNegativeAxiom)] : Λ.ConsistentVF := by
  constructor;
  by_contra hC;
  apply consistency_of_Int $ provableInt_Int_of_provableVF_CNAExtension hC;

lemma slashable_of_provableVF_CNAExtension [Fact (∀ A ∈ Λ, A.IsClosedNegativeAxiom)] : (Λ ⊢ⱽ A) → (Λ ∕ A) := by
  intro h;
  induction h with
  | @axm B hB =>
    have := Fact.out (p := ∀ A ∈ Λ, A.IsClosedNegativeAxiom) _ hB;
    obtain ⟨C, rfl, hC₁, hC₂⟩ := Formula.iff_isCNA.mp this;
    constructor;
    . exact ProvableVF.axm hB;
    . intro h;
      have : ∅ ⊢ᴵ C := provableInt_Int_of_provableVF_CNAExtension $ provableVF_of_slashable h;
      exact consistency_of_Int $ ProvableInt.mdp hC₂ this;
  | _ => grind;

instance disjunctive_VF_CNAExtension [Fact (∀ A ∈ Λ, A.IsClosedNegativeAxiom)] : Λ.DisjunctiveVF := by
  apply disjunctive_of_iff_slashable_provable;
  intro A;
  constructor;
  . exact provableVF_of_slashable;
  . exact slashable_of_provableVF_CNAExtension;
