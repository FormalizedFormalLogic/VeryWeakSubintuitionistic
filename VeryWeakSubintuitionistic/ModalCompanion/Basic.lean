module

public import VeryWeakSubintuitionistic.Modal.FMT.Completeness
public import VeryWeakSubintuitionistic.Propositional.FMT.Completeness

@[expose] public section

namespace ModalCompanion

variable {α : Type*}

@[grind]
def corsi : Formula α → Modal.Formula α
  | #a    => #a
  | ⊥     => ⊥
  | A ⋏ B => (corsi A) ⋏ (corsi B)
  | A ⋎ B => (corsi A) ⋎ (corsi B)
  | A 🡒 B => □((corsi A) 🡒 (corsi B))

/-- Corsi translation is injective. -/
lemma corsi_injective : Function.Injective (corsi : Formula α → _) := by
  intro A
  induction A with
  | atom a => intro B h; cases B <;> simp_all [corsi]
  | bot => intro B h; cases B <;> simp_all [corsi]
  | and A₁ A₂ ihA ihB =>
    intro B h
    cases B <;> simp_all [corsi]
    grind
  | or A₁ A₂ ihA ihB =>
    intro B h
    cases B <;> simp_all [corsi]
    grind
  | imp A₁ A₂ ihA ihB =>
    intro B h
    cases B <;> simp_all [corsi]
    grind

/-! ## Lemma 6.8 (`prop_to_modal_FMT`) -/

section PropToModal

variable {κ : Type*} (M_P : FMTSemantics.Model κ α)

/-- Frame for the modal FMT model constructed from a propositional FMT model.

The paper says: define `R^M_B`
* if `B = (Cᶜ 🡒 Dᶜ)` for some propositional `C, D`, by `xR^M_B y ⟺ xR^P_{C🡒D} y`;
* otherwise `R^M_B` is the always-true relation.

In Lean's modal FMT semantics, `□A` is forced through the relation indexed by
`□A` itself (not by `A`), so we read the paper's condition as: if
`B = □(corsi C 🡒 corsi D)`, use `R^P_{C 🡒 D}`. We express this by a
universal quantifier; injectivity of `corsi` guarantees the witness `(C, D)`
is unique. -/
def propToModalFrame : Modal.FMT.Frame κ α where
  Rel' B X Y := ∀ C D : Formula α,
    B = □((corsi C) 🡒 (corsi D)) → M_P.Rel' (C 🡒 D) X Y
  root' := M_P.root'

/-- The modal FMT model derived from a propositional FMT model. -/
def propToModalModel : Modal.FMT.Model κ α where
  toFrame := propToModalFrame M_P
  Val a x := M_P.Val a x

/-- Lemma 6.8 (truth lemma). For every propositional formula `A` and every
world `x`, `M^P, x ⊩ A` iff `M^M, x ⊩ corsi A`. -/
theorem propToModal_truthlemma :
    ∀ (A : Formula α) (x : (propToModalModel M_P).World),
      FMTSemantics.Forces (M := M_P) x A
        ↔ Modal.FMT.Forced (M := propToModalModel M_P) x (corsi A) := by
  intro A
  induction A with
  | atom a => intro x; rfl
  | bot => intro x; rfl
  | and A B ihA ihB =>
    intro x
    -- `M^P, x ⊩ A ⋏ B ↔ M^P, x ⊩ A ∧ M^P, x ⊩ B` (propositional `⋏` is conjunction).
    -- `M^M, x ⊩ corsi A ⋏ corsi B = ∼(corsi A 🡒 ∼corsi B)`
    --   `= ¬(x ⊩ corsi A → ¬ x ⊩ corsi B)`. Classically equiv to `∧`.
    have hA := ihA x
    have hB := ihB x
    show (FMTSemantics.Forces (M := M_P) x A ∧ FMTSemantics.Forces (M := M_P) x B) ↔ _
    show _ ↔ ¬ (Modal.FMT.Forced (M := propToModalModel M_P) x (corsi A)
            → ¬ Modal.FMT.Forced (M := propToModalModel M_P) x (corsi B))
    tauto
  | or A B ihA ihB =>
    intro x
    -- `M^P, x ⊩ A ⋎ B ↔ M^P, x ⊩ A ∨ M^P, x ⊩ B`.
    -- `M^M, x ⊩ corsi A ⋎ corsi B = ∼corsi A 🡒 corsi B`
    --   `= ¬ x ⊩ corsi A → x ⊩ corsi B`. Classically equiv to `∨`.
    have hA := ihA x
    have hB := ihB x
    show (FMTSemantics.Forces (M := M_P) x A ∨ FMTSemantics.Forces (M := M_P) x B) ↔ _
    show _ ↔ (¬ Modal.FMT.Forced (M := propToModalModel M_P) x (corsi A)
            → Modal.FMT.Forced (M := propToModalModel M_P) x (corsi B))
    tauto
  | imp A B ihA ihB =>
    intro x
    -- `M^P, x ⊩ A 🡒 B  =  ∀ y, x R^P_{A🡒B} y → (y ⊩ A → y ⊩ B)`.
    -- `M^M, x ⊩ corsi (A 🡒 B) = M^M, x ⊩ □(corsi A 🡒 corsi B)`
    --   `= ∀ y, x R^M_{□(corsi A 🡒 corsi B)} y → (y ⊩ corsi A → y ⊩ corsi B)`.
    constructor
    · intro h y hRM hAc
      -- `hRM : (propToModalModel M_P).Rel' (□(corsi A 🡒 corsi B)) x y`.
      --       Applying it with `C := A`, `D := B` yields `R^P_{A 🡒 B} x y`.
      have hRP : M_P.Rel' (A 🡒 B) x y := hRM A B rfl
      exact (ihB y).mp <| h y hRP <| (ihA y).mpr hAc
    · intro h y hRP hA
      -- Need `R^M_{□(corsi A 🡒 corsi B)} x y`. By corsi injectivity, the only
      -- witness in the universal quantifier is `(A, B)`, giving `R^P_{A 🡒 B}`.
      have hRM : (propToModalModel M_P).Rel' (□((corsi A) 🡒 (corsi B))) x y := by
        intro C D heq
        have h₁ : corsi A = corsi C ∧ corsi B = corsi D := by
          simp at heq; exact heq
        obtain ⟨hAC, hBD⟩ := h₁
        cases corsi_injective hAC
        cases corsi_injective hBD
        exact hRP
      exact (ihB y).mpr <| h y hRM <| (ihA y).mp hA

end PropToModal

end ModalCompanion



end
