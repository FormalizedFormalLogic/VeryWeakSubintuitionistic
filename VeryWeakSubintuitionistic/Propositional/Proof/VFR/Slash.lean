module

public import VeryWeakSubintuitionistic.Propositional.Proof.VFR.Basic
public import VeryWeakSubintuitionistic.Propositional.Slash

@[expose] public section

variable {α : Type*}

namespace Int.ProvableHilbert

variable {𝔸 : Axioms α} {A B : Formula α}

@[grind <=]
lemma ros : (⊢ʰ[Int;𝔸] ∼A) → (⊢ʰ[Int;𝔸] B) → ⊢ʰ[Int;𝔸] ∼(B 🡒 A) := by
  intro hA hB;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have h₁ : ({B 🡒 A} : Set (Formula α)) ⊢ʰ[Int;𝔸] B 🡒 A := DeducibleHilbert.ofContext (by simp);
  have h₂ : ({B 🡒 A} : Set (Formula α)) ⊢ʰ[Int;𝔸] A := DeducibleHilbert.mdp h₁ (DeducibleHilbert.ofProvable hB);
  exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable hA) h₂;

end Int.ProvableHilbert


namespace VFR

@[grind]
def Slashable (𝔸 : Axioms α) : Formula α → Prop
  | #a => ⊢ʰ[VFR;𝔸] #a
  | ⊥ => False
  | A ⋎ B => Slashable 𝔸 A ∨ Slashable 𝔸 B
  | A ⋏ B => Slashable 𝔸 A ∧ Slashable 𝔸 B
  | A 🡒 B => (⊢ʰ[VFR;𝔸] A 🡒 B) ∧ (Slashable 𝔸 A → Slashable 𝔸 B)

end VFR

notation:25 𝔸:26 " ∕[VFR] " A:26 => VFR.Slashable 𝔸 A

namespace VFR

namespace Slashable

variable {𝔸 : Axioms α} {A B C : Formula α}

@[grind =>]
lemma mdp : (𝔸 ∕[VFR] (A 🡒 B)) → (𝔸 ∕[VFR] A) → 𝔸 ∕[VFR] B := by grind;

end Slashable


variable {𝔸 : Axioms α} {A B C : Formula α}

lemma provable_of_slashable : (𝔸 ∕[VFR] A) → (⊢ʰ[VFR;𝔸] A) := by induction A <;> grind;

lemma disjunctive_of_iff_slashable_provable (h : ∀ {A}, 𝔸 ∕[VFR] A ↔ ⊢ʰ[VFR;𝔸] A) : VFR.Disjunctive 𝔸 := by
  constructor;
  grind;


lemma provableInt_of_provable_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : (⊢ʰ[VFR;𝔸] A) → ⊢ʰ[Int;∅] A := by
  intro h;
  induction h with
  | axm h => have := Fact.out (p := ∀ A ∈ 𝔸, A.IsClosedNegativeAxiom) _ h; grind;
  | ros ihA ihB => exact Int.ProvableHilbert.ros ihA ihB;
  | _ => grind

instance consistency_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : VFR.Consistent 𝔸 := by
  constructor;
  by_contra hC;
  apply consistency_of_Int $ provableInt_of_provable_CNAExtension hC;

lemma slashable_of_provable_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : (⊢ʰ[VFR;𝔸] A) → (𝔸 ∕[VFR] A) := by
  intro h;
  induction h with
  | @axm B hB =>
    have := Fact.out (p := ∀ A ∈ 𝔸, A.IsClosedNegativeAxiom) _ hB;
    obtain ⟨C, rfl, hC₁, hC₂⟩ := Formula.iff_isCNA.mp this;
    constructor;
    . exact VFR.ProvableHilbert.axm hB;
    . intro h;
      have : ⊢ʰ[Int;∅] C := provableInt_of_provable_CNAExtension $ provable_of_slashable h;
      exact consistency_of_Int $ Int.ProvableHilbert.mdp hC₂ this;
  | @ros C D _ _ ihC ihD =>
    replace ihC : (⊢ʰ[VFR;𝔸] ∼C) ∧ ((𝔸 ∕[VFR] C) → False) := ihC;
    show (⊢ʰ[VFR;𝔸] ∼(D 🡒 C)) ∧ ((𝔸 ∕[VFR] (D 🡒 C)) → False);
    refine ⟨ProvableHilbert.ros ihC.1 (provable_of_slashable ihD), ?_⟩;
    rintro ⟨-, h⟩;
    exact ihC.2 (h ihD);
  | _ => grind;

instance disjunctive_CNAExtension [Fact (∀ A ∈ 𝔸, A.IsClosedNegativeAxiom)] : VFR.Disjunctive 𝔸 := by
  apply disjunctive_of_iff_slashable_provable;
  intro A;
  constructor;
  . exact provable_of_slashable;
  . exact slashable_of_provable_CNAExtension;

end VFR

end section
