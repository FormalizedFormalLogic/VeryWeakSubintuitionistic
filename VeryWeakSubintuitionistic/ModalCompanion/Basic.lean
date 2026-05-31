module

public import VeryWeakSubintuitionistic.Modal.FMT.Completeness
public import VeryWeakSubintuitionistic.Propositional.FMT.Completeness

@[expose] public section

variable {α : Type u}

namespace Formula

@[grind]
def corsi : Formula α → Modal.Formula α
  | #a    => #a
  | ⊥     => ⊥
  | A ⋏ B => (corsi A) ⋏ (corsi B)
  | A ⋎ B => (corsi A) ⋎ (corsi B)
  | A 🡒 B => □((corsi A) 🡒 (corsi B))

lemma corsi_injective : Function.Injective (corsi (α := α)) := by
  intro A;
  induction A with
  | atom a => intro B _; cases B <;> grind [corsi];
  | bot => intro B _; cases B <;> grind;
  | and A₁ A₂ ihA ihB => intro B _; cases B <;> grind;
  | or A₁ A₂ ihA ihB => intro B _; cases B <;> grind [corsi];
  | imp A₁ A₂ ihA ihB => intro B _; cases B <;> grind [corsi];

end Formula


section PropToModal

variable {κ : Type*} {A : Formula α}
variable {PM : FMTSemantics.Model κ α}

def propToModalModel (PM : FMTSemantics.Model κ α) : Modal.FMT.Model κ α where
  Rel' B X Y := ∀ C D, B = □((C.corsi) 🡒 (D.corsi)) → PM.Rel (C 🡒 D) X Y
  Val a x := PM.Val a x
  root' := PM.root'

theorem propToModal_truthlemma {x : PM.World} :
  FMTSemantics.Forces (M := PM) x A ↔ Modal.FMT.Forced (M := propToModalModel PM) x A.corsi := by
  induction A generalizing x with
  | atom a => rfl;
  | imp A B ihA ihB =>
    constructor;
    · intro h y hRM hAc;
      have hRP : PM.Rel (A 🡒 B) x y := hRM A B rfl;
      exact ihB.mp <| h y hRP <| ihA.mpr hAc;
    · intro h y hRP hA;
      have hRM : (propToModalModel PM).Rel (□((A.corsi) 🡒 (B.corsi))) x y := by
        intro C D heq;
        obtain ⟨hAC, hBD⟩ : A.corsi = C.corsi ∧ B.corsi = D.corsi := by grind;
        cases Formula.corsi_injective hAC;
        cases Formula.corsi_injective hBD;
        exact hRP;
      exact ihB.mpr <| h y hRM <| ihA.mp hA;
  | _ => grind;

end PropToModal


section ModalToProp

variable {κ : Type*} {MM : Modal.FMT.Model κ α} {A : Formula α}

def modalToPropModel (MM : Modal.FMT.Model κ α) : FMTSemantics.Model (κ ⊕ Unit) α where
  Rel' A x y :=
    match A, x, y with
    | _,        .inr (),  _         => True
    | (C 🡒 D),  .inl xK,  .inl yK   => MM.Rel (□((C.corsi) 🡒 (D.corsi))) xK yK
    | _,        .inl _,   .inr ()   => False
    | _,        .inl _,   .inl _    => True
  root' := .inr ()
  root_rooted' := by tauto;
  Val a x :=
    match x with
    | .inl k  => MM.Val a k
    | .inr () => True

theorem modalToProp_truthlemma {x : MM.World} :
  Modal.FMT.Forced (M := MM) x (A.corsi) ↔ FMTSemantics.Forces (M := modalToPropModel MM) (.inl x) A := by
  induction A generalizing x with
  | imp A B ihA ihB =>
    constructor;
    · intro h y hRP hAp;
      match y with
      | .inl y =>
        have hRM : MM.Rel (□((A.corsi) 🡒 (B.corsi))) x y := hRP;
        have hAc : Modal.FMT.Forced (M := MM) y (A.corsi) := (ihA).mpr hAp;
        exact ihB.mp (h y hRM hAc);
      | .inr () =>
        contradiction;
    · intro h y hRM hAc;
      have hRP : (modalToPropModel MM).Rel (A 🡒 B) (.inl x) (.inl y) := hRM;
      have hAp : FMTSemantics.Forces (M := modalToPropModel MM) (.inl y) A :=
        (ihA).mp hAc;
      exact (ihB).mpr (h (.inl y) hRP hAp);
  | atom a => rfl;
  | _ => grind;

/-- Claim 6.1 in Lemma 6.10 -/
lemma modalToProp_root_validates_of_forces (A_closed : A.Closed) :
  FMTSemantics.Forces (M := modalToPropModel MM) (.inr ()) A → Modal.FMT.ModelValid MM (A.corsi) := by
  induction A with
  | imp C D _ _ =>
    intro h y;
    show ∀ z, y ≺[□((C.corsi) 🡒 (D.corsi))] z → (z ⊩ C.corsi → z ⊩ D.corsi);
    intro z _ hCm;
    have hCp : FMTSemantics.Forces (M := modalToPropModel MM) (.inl z) C :=
      (modalToProp_truthlemma).mp hCm;
    have hRP : (modalToPropModel MM).Rel (C 🡒 D) (.inr ()) (.inl z) := trivial;
    exact (modalToProp_truthlemma).mpr (h (.inl z) hRP hCp);
  | _ => grind;

/-- Lemma 6.10 -/
theorem modalToProp_notForces_closed_of_neg
  (A_closed : A.Closed) (h : MM ⊨ (∼(A.corsi))) {x : (modalToPropModel MM).World} :
  FMTSemantics.NotForces x A := by
  match x with
  | .inl k =>
    apply modalToProp_truthlemma.not.mp;
    apply h;
  | .inr () =>
    by_contra hC;
    have : MM.root ⊩ A.corsi  := modalToProp_root_validates_of_forces ‹_› hC MM.root;
    have : MM.root ⊩ ∼A.corsi := h MM.root;
    grind;

end ModalToProp



namespace Formula

@[grind]
def IsNegation : Formula α → Prop
  | ∼_ => True
  | _ => False

instance : DecidablePred (IsNegation : Formula α → Prop) := by
  intro A;
  match A with
  | ∼_ => exact isTrue trivial
  | #_ | ⊥ | _ ⋏ _ | _ ⋎ _
  | _ 🡒 #_ | _ 🡒 (_ ⋏ _) | _ 🡒 (_ 🡒 _)  | _ 🡒 (_ ⋎ _)
    => exact isFalse (by grind);

end Formula


variable {α : Type u} [DecidableEq α]

namespace Formula

def cases_neg {P : Formula α → Prop}
  (falsum : P (⊥ : Formula α))
  (atom : ∀ a, P (#a))
  (and : ∀ A B, P (A ⋏ B))
  (or : ∀ A B, P (A ⋎ B))
  (imp : ∀ A B, B ≠ (⊥ : Formula α) → P (A 🡒 B))
  (neg : ∀ A, P (∼A))
  : ∀ A, P A := by
  intro A;
  match A with
  | ⊥ | #_ | _ ⋏ _ | _ ⋎ _
  | _ 🡒 ⊥ | _ 🡒 #_
  | _ 🡒 (_ ⋏ _) | _ 🡒 (_ ⋎ _) | _ 🡒 (_ 🡒 _)
    => grind;

omit [DecidableEq α] in
@[grind →]
lemma isClosed_of_isCNA {A : Formula α} : A.IsClosedNegativeAxiom → A.Closed := by grind;

end Formula

namespace Axioms

def star (Λ : Axioms α) := Λ.filterMap (λ A => match A with | ∼B => some (∼(B.corsi)) | _  => none) $ by
  intro B C;
  cases B using Formula.cases_neg <;> cases C using Formula.cases_neg;
  case neg.neg => grind [Formula.corsi_injective]
  all_goals grind;

variable {Λ : Axioms α}

omit [DecidableEq α] in
lemma mem_star_of_mem_neg {B : Formula α} (hB : ∼B ∈ Λ) : ∼(B.corsi) ∈ star Λ := by
  apply Finset.mem_filterMap _ |>.mpr;
  use ∼B;

end Axioms



theorem modal_companion
  {Λ : Axioms α} (hX : ∀ B ∈ Λ, B.IsClosedNegativeAxiom)
  [Fact ((Λ.star) ⊬ᴺ ⊥)] [Axioms.DisjunctiveVF Λ]
  : (Λ ⊢ⱽ A) ↔ ((Λ.star) ⊢ᴺ A.corsi) := by
  have : Fact (∀ B ∈ Λ, B.IsClosedNegativeAxiom) := ⟨hX⟩;
  constructor;
  · intro h;
    apply Modal.FMT.finite_model_property;
    intro κ _ MM hValid x;
    apply (modalToProp_truthlemma).mpr;
    apply FMTSemantics.soundness_model h (modalToPropModel MM);
    intro B hB;
    obtain ⟨C, rfl, hCClosed, _⟩ := Formula.iff_isCNA.mp (hX B hB);
    intro y z Ryz hzC;
    have hValC : ∀ y, ¬ Modal.FMT.Forced (M := MM) y (C.corsi) := by
      intro y';
      have hMem : ∼(C.corsi) ∈ Λ.star := Axioms.mem_star_of_mem_neg hB;
      exact hValid _ hMem y';
    exact modalToProp_notForces_closed_of_neg hCClosed hValC hzC;
  · contrapose;
    intro h;
    replace h := FMTSemantics.result_frame (Λ := Λ) (by grind) |>.not.out 0 1 |>.mp h;
    push Not at h;
    obtain ⟨_, PF, hPF, h⟩ := h;
    obtain ⟨PV, x, hx⟩ := FMTSemantics.iff_notFrameValid_exists_model_world.mp h;
    apply Modal.FMT.result_model.not.out 0 1 |>.mpr;
    push Not;
    use ‹_›, propToModalModel ⟨PF, PV⟩;
    constructor;
    . intro B hB;
      obtain ⟨C, hC₁, hC₂⟩ := Finset.mem_filterMap _ |>.mp hB;
      split at hC₂;
      . simp only [Option.some.injEq] at hC₂;
        subst hC₂;
        rename_i C;
        obtain ⟨D, _, _, _⟩ := Formula.iff_isCNA.mp $ hX (∼C) ‹_›;
        intro y;
        apply Modal.FMT.forces_not.mpr;
        apply propToModal_truthlemma.not.mp;
        exact FMTSemantics.iff_FrameForces_Forces_of_closed (by grind) |>.not.mp
          $ FMTSemantics.iff_FrameValid_neg_of_closed (by grind) |>.mp (hPF _ hC₁) y;
      . contradiction;
    . replace hx := propToModal_truthlemma.not.mp hx;
      apply Modal.FMT.iff_Valid_exists_world_not_Forces.mpr;
      use x;

end
