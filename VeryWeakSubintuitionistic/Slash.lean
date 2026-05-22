module

public import VeryWeakSubintuitionistic.Proof

@[expose] public section

@[grind]
def Slashable (Λ : Axioms α) : Formula α → Prop
  | #a => Λ ⊢ #a
  | ⊥ => False
  | A ⋎ B => Slashable Λ A ∨ Slashable Λ B
  | A ⋏ B => Slashable Λ A ∧ Slashable Λ B
  | A 🡒 B => (Λ ⊢ A 🡒 B) ∧ (Slashable Λ A → Slashable Λ B)
infix:25 " ∕ " => Slashable

namespace Slashable

variable {Λ : Axioms α} {A B C : Formula α}

@[grind =>]
lemma mdp : Λ ∕ (A 🡒 B) → Λ ∕ A → Λ ∕ B := by grind;

end Slashable


variable {Λ : Axioms α} {A B C : Formula α}

lemma provable_of_slashable : (Λ ∕ A) → (Λ ⊢ A) := by induction A <;> grind;

instance disjunctive_of_iff_slashable_provable (h : ∀ {A}, Λ ∕ A ↔ Λ ⊢ A) : Λ.Disjunctive := by
  constructor;
  grind;

/-
lemma iff_slashable_provable_of_CNA (H : ∀ A ∈ Λ, A.IsCNA) : (Λ ∕ A) ↔ (Λ ⊢ A) := by
  constructor;
  . exact provable_of_slashable;
  . intro h;
    induction h with
    | @axm A h =>
      obtain ⟨B, rfl, _, _⟩ := Formula.of_isCNA $ H _ h;
      constructor;
      . exact Provable.axm h;
      . intro hB;
        have : Λ ⊢ ⊥ := .mdp (.axm h) (provable_of_slashable hB);
        sorry;
    | _ => grind;

lemma disjunctive_of_CNA (H : ∀ A ∈ Λ, A.IsCNA) : (Λ ⊢ (A ⋎ B)) → (Λ ⊢ A) ∨ (Λ ⊢ B) := by
  intro h;
  rcases iff_slashable_provable_of_CNA H |>.mpr h with h | h;
  . left; exact iff_slashable_provable_of_CNA H |>.mp h;
  . right; exact iff_slashable_provable_of_CNA H |>.mp h;
-/


namespace Formula

def IsCNA (Λ : Axioms α) : Formula α → Prop
  | ∼A => A.Closed ∧ (Λ ⊢ A)
  | _ => False

end Formula
