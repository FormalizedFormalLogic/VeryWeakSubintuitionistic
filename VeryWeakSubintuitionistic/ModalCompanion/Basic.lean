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


section PropToModal

variable {κ : Type*} (M_P : FMTSemantics.Model κ α)

def propToModalFrame : Modal.FMT.Frame κ α where
  Rel' B X Y := ∀ C D : Formula α,
    B = □((corsi C) 🡒 (corsi D)) → M_P.Rel' (C 🡒 D) X Y
  root' := M_P.root'

def propToModalModel : Modal.FMT.Model κ α where
  toFrame := propToModalFrame M_P
  Val a x := M_P.Val a x

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
    have hA := ihA x
    have hB := ihB x
    show (FMTSemantics.Forces (M := M_P) x A ∧ FMTSemantics.Forces (M := M_P) x B) ↔ _
    show _ ↔ ¬ (Modal.FMT.Forced (M := propToModalModel M_P) x (corsi A)
            → ¬ Modal.FMT.Forced (M := propToModalModel M_P) x (corsi B))
    tauto
  | or A B ihA ihB =>
    intro x
    have hA := ihA x
    have hB := ihB x
    show (FMTSemantics.Forces (M := M_P) x A ∨ FMTSemantics.Forces (M := M_P) x B) ↔ _
    show _ ↔ (¬ Modal.FMT.Forced (M := propToModalModel M_P) x (corsi A)
            → Modal.FMT.Forced (M := propToModalModel M_P) x (corsi B))
    tauto
  | imp A B ihA ihB =>
    intro x
    constructor
    · intro h y hRM hAc
      have hRP : M_P.Rel' (A 🡒 B) x y := hRM A B rfl
      exact (ihB y).mp <| h y hRP <| (ihA y).mpr hAc
    · intro h y hRP hA
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


section ModalToProp

variable {κ : Type*} (M_M : Modal.FMT.Model κ α)

abbrev ModalToPropWorld (κ : Type*) := Option κ

def modalToPropRel :
    Formula α → ModalToPropWorld κ → ModalToPropWorld κ → Prop
  | _,        none,      _         => True
  | _,        some _,    none      => False
  | (C 🡒 D), some xK,   some yK   => M_M.Rel' (□((corsi C) 🡒 (corsi D))) xK yK
  | _,        some _,    some _    => True

def modalToPropFrame : FMTSemantics.Frame (ModalToPropWorld κ) α where
  Rel' := modalToPropRel M_M
  root' := none
  root_rooted' := by intros; exact trivial

def modalToPropModel : FMTSemantics.Model (ModalToPropWorld κ) α where
  toFrame := modalToPropFrame M_M
  Val a x :=
    match x with
    | none   => True
    | some k => M_M.Val a k

theorem modalToProp_truthlemma :
    ∀ (A : Formula α) (x : κ),
      Modal.FMT.Forced (M := M_M) x (corsi A)
        ↔ FMTSemantics.Forces (M := modalToPropModel M_M) (some x) A := by
  intro A
  induction A with
  | atom a => intro x; rfl
  | bot => intro x; rfl
  | and A B ihA ihB =>
    intro x
    have hA := ihA x
    have hB := ihB x
    show ¬ (Modal.FMT.Forced (M := M_M) x (corsi A)
          → ¬ Modal.FMT.Forced (M := M_M) x (corsi B)) ↔ _
    show _ ↔ (FMTSemantics.Forces (M := modalToPropModel M_M) (some x) A
            ∧ FMTSemantics.Forces (M := modalToPropModel M_M) (some x) B)
    tauto
  | or A B ihA ihB =>
    intro x
    have hA := ihA x
    have hB := ihB x
    show (¬ Modal.FMT.Forced (M := M_M) x (corsi A)
          → Modal.FMT.Forced (M := M_M) x (corsi B)) ↔ _
    show _ ↔ (FMTSemantics.Forces (M := modalToPropModel M_M) (some x) A
            ∨ FMTSemantics.Forces (M := modalToPropModel M_M) (some x) B)
    tauto
  | imp A B ihA ihB =>
    intro x
    constructor
    · intro h y hRP hAp
      match y, hRP, hAp with
      | some yK, hRP, hAp =>
        have hRM : M_M.Rel' (□((corsi A) 🡒 (corsi B))) x yK := hRP
        have hAc : Modal.FMT.Forced (M := M_M) yK (corsi A) := (ihA yK).mpr hAp
        exact (ihB yK).mp (h yK hRM hAc)
      | none, hRP, _ =>
        exact (hRP : False).elim
    · intro h y hRM hAc
      have hRP : modalToPropRel M_M (A 🡒 B) (some x) (some y) := hRM
      have hAp : FMTSemantics.Forces (M := modalToPropModel M_M) (some y) A :=
        (ihA y).mp hAc
      exact (ihB y).mpr (h (some y) hRP hAp)

end ModalToProp

end ModalCompanion

end
