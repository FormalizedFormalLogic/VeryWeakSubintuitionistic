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


/-! ## Lemma 6.9 (`modal_to_prop_FMT`) -/

section ModalToProp

variable {κ : Type*} (M_M : Modal.FMT.Model κ α)

/-- Carrier of the propositional model derived from a modal model:
the original `κ` extended by a fresh root, encoded as `none`. -/
abbrev ModalToPropWorld (κ : Type*) := Option κ

/-- The propositional accessibility from a modal model:
* the root `none` reaches every world (this gives the rooted condition);
* no world reaches the root;
* between two non-root worlds, `R^P_{C 🡒 D}` agrees with
  `R^M_{□(corsi C 🡒 corsi D)}`;
* for any non-implication index, two non-root worlds are always related. -/
def modalToPropRel :
    Formula α → ModalToPropWorld κ → ModalToPropWorld κ → Prop
  | _,        none,      _         => True
  | _,        some _,    none      => False
  | (C 🡒 D), some xK,   some yK   => M_M.Rel' (□((corsi C) 🡒 (corsi D))) xK yK
  | _,        some _,    some _    => True

/-- Frame for the propositional FMT model derived from a modal one. -/
def modalToPropFrame : FMTSemantics.Frame (ModalToPropWorld κ) α where
  Rel' := modalToPropRel M_M
  root' := none
  root_rooted' := by intros; exact trivial

/-- Propositional FMT model derived from a modal one. -/
def modalToPropModel : FMTSemantics.Model (ModalToPropWorld κ) α where
  toFrame := modalToPropFrame M_M
  Val a x :=
    match x with
    | none   => True
    | some k => M_M.Val a k

/-- Lemma 6.9 (truth lemma). For every propositional formula `A` and every
world `x : κ` of the original modal model (i.e. not the new root),
`M^M, x ⊩ corsi A` iff `M^P, some x ⊩ A`. -/
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
    · -- `(⇒)`: `x ⊩ □(corsi A 🡒 corsi B)` in `M^M` → `some x ⊩ (A 🡒 B)` in `M^P`.
      intro h y hRP hAp
      match y, hRP, hAp with
      | some yK, hRP, hAp =>
        -- `hRP : modalToPropRel M_M (A 🡒 B) (some x) (some yK)` reduces to
        --       `M_M.Rel' (□(corsi A 🡒 corsi B)) x yK`.
        have hRM : M_M.Rel' (□((corsi A) 🡒 (corsi B))) x yK := hRP
        have hAc : Modal.FMT.Forced (M := M_M) yK (corsi A) := (ihA yK).mpr hAp
        exact (ihB yK).mp (h yK hRM hAc)
      | none, hRP, _ =>
        -- `hRP : modalToPropRel M_M (A 🡒 B) (some x) none = False`.
        exact (hRP : False).elim
    · -- `(⇐)`: `some x ⊩ (A 🡒 B)` in `M^P` → `x ⊩ □(corsi A 🡒 corsi B)` in `M^M`.
      intro h y hRM hAc
      have hRP : modalToPropRel M_M (A 🡒 B) (some x) (some y) := hRM
      have hAp : FMTSemantics.Forces (M := modalToPropModel M_M) (some y) A :=
        (ihA y).mp hAc
      exact (ihB y).mpr (h (some y) hRP hAp)

end ModalToProp

end ModalCompanion



end
