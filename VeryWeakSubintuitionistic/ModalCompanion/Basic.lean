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
  intro A;
  induction A with
  | atom a => intro B _; cases B <;> grind [corsi];
  | bot => intro B _; cases B <;> grind [corsi];
  | and A₁ A₂ ihA ihB => intro B _; cases B <;> grind [corsi];
  | or A₁ A₂ ihA ihB => intro B _; cases B <;> grind [corsi];
  | imp A₁ A₂ ihA ihB => intro B _; cases B <;> grind [corsi];


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
    intro x;
    have hA := ihA x;
    have hB := ihB x;
    grind;
  | or A B ihA ihB =>
    intro x;
    have hA := ihA x;
    have hB := ihB x;
    grind;
  | imp A B ihA ihB =>
    intro x;
    constructor;
    · intro h y hRM hAc;
      have hRP : M_P.Rel' (A 🡒 B) x y := hRM A B rfl;
      exact (ihB y).mp <| h y hRP <| (ihA y).mpr hAc;
    · intro h y hRP hA;
      have hRM : (propToModalModel M_P).Rel' (□((corsi A) 🡒 (corsi B))) x y := by
        intro C D heq;
        obtain ⟨hAC, hBD⟩ : corsi A = corsi C ∧ corsi B = corsi D := by grind;
        cases corsi_injective hAC;
        cases corsi_injective hBD;
        exact hRP;
      exact (ihB y).mpr <| h y hRM <| (ihA y).mp hA;

end PropToModal


section ModalToProp

variable {κ : Type*} (M_M : Modal.FMT.Model κ α)

abbrev ModalToPropWorld (κ : Type*) := κ ⊕ Unit

def modalToPropRel :
    Formula α → ModalToPropWorld κ → ModalToPropWorld κ → Prop
  | _,        .inr (),  _         => True
  | _,        .inl _,   .inr ()   => False
  | (C 🡒 D), .inl xK,  .inl yK   => M_M.Rel' (□((corsi C) 🡒 (corsi D))) xK yK
  | _,        .inl _,   .inl _    => True

def modalToPropFrame : FMTSemantics.Frame (ModalToPropWorld κ) α where
  Rel' := modalToPropRel M_M
  root' := .inr ()
  root_rooted' := by intros; exact trivial

def modalToPropModel : FMTSemantics.Model (ModalToPropWorld κ) α where
  toFrame := modalToPropFrame M_M
  Val a x :=
    match x with
    | .inr () => True
    | .inl k  => M_M.Val a k

theorem modalToProp_truthlemma :
    ∀ (A : Formula α) (x : κ),
      Modal.FMT.Forced (M := M_M) x (corsi A)
        ↔ FMTSemantics.Forces (M := modalToPropModel M_M) (.inl x) A := by
  intro A;
  induction A with
  | atom a => intro x; rfl;
  | bot => intro x; rfl;
  | and A B ihA ihB =>
    intro x;
    have hA := ihA x;
    have hB := ihB x;
    grind;
  | or A B ihA ihB =>
    intro x;
    have hA := ihA x;
    have hB := ihB x;
    grind;
  | imp A B ihA ihB =>
    intro x;
    constructor;
    · intro h y hRP hAp;
      match y, hRP, hAp with
      | .inl yK, hRP, hAp =>
        have hRM : M_M.Rel' (□((corsi A) 🡒 (corsi B))) x yK := hRP;
        have hAc : Modal.FMT.Forced (M := M_M) yK (corsi A) := (ihA yK).mpr hAp;
        exact (ihB yK).mp (h yK hRM hAc);
      | .inr (), hRP, _ =>
        exact (hRP : False).elim;
    · intro h y hRM hAc;
      have hRP : modalToPropRel M_M (A 🡒 B) (.inl x) (.inl y) := hRM;
      have hAp : FMTSemantics.Forces (M := modalToPropModel M_M) (.inl y) A :=
        (ihA y).mp hAc;
      exact (ihB y).mpr (h (.inl y) hRP hAp);

private lemma modalToProp_root_validates_of_forces :
    ∀ (C : Formula α), C.Closed →
      FMTSemantics.Forces (M := modalToPropModel M_M) (.inr ()) C →
      ∀ y : κ, Modal.FMT.Forced (M := M_M) y (corsi C) := by
  intro C;
  induction C with
  | atom a => intro hC; exact hC.elim;
  | bot => intro _ h; exact h.elim;
  | and C D ihC ihD =>
    intro hC h y;
    obtain ⟨hCC, hDC⟩ := hC;
    obtain ⟨hCv, hDv⟩ := h;
    have hCm := ihC hCC hCv y;
    have hDm := ihD hDC hDv y;
    grind;
  | or C D ihC ihD =>
    intro hC h y;
    obtain ⟨hCC, hDC⟩ := hC;
    rcases h with hCv | hDv;
    · have hCm := ihC hCC hCv y;
      grind;
    · have hDm := ihD hDC hDv y;
      grind;
  | imp C D _ _ =>
    intro _ h y;
    show ∀ z, y ≺[□((corsi C) 🡒 (corsi D))] z → (z ⊩ corsi C → z ⊩ corsi D);
    intro z _ hCm;
    have hCp : FMTSemantics.Forces (M := modalToPropModel M_M) (.inl z) C :=
      (modalToProp_truthlemma M_M C z).mp hCm;
    have hRP : modalToPropRel M_M (C 🡒 D) (.inr ()) (.inl z) := trivial;
    exact (modalToProp_truthlemma M_M D z).mpr (h (.inl z) hRP hCp);

theorem modalToProp_notForces_closed_of_neg
    {C : Formula α} (hC : C.Closed)
    (hVal : ∀ y : κ, ¬ Modal.FMT.Forced (M := M_M) y (corsi C)) :
    ∀ x : (modalToPropModel M_M).World,
      ¬ FMTSemantics.Forces (M := modalToPropModel M_M) x C := by
  intro x hX
  match x, hX with
  | .inl k, hX => exact hVal k ((modalToProp_truthlemma M_M C k).mpr hX)
  | .inr (), hX =>
    exact hVal M_M.root'
      (modalToProp_root_validates_of_forces M_M C hC hX M_M.root')

end ModalToProp


def starAxiom : Formula α → Modal.Formula α
  | A 🡒 ⊥ => ∼(corsi A)
  | A     => corsi A

@[simp] lemma starAxiom_neg (A : Formula α) : starAxiom (∼A) = ∼(corsi A) := rfl

private lemma closed_of_CNA {B : Formula α} (h : B.IsClosedNegativeAxiom) : B.Closed := by
  obtain ⟨C, rfl, hCClosed, _⟩ := Formula.iff_isCNA.mp h;
  exact ⟨hCClosed, trivial⟩;

section ModalCompanionThm

variable [DecidableEq α]

def starAxioms (X : Axioms α) : Modal.Axioms α := X.image starAxiom

theorem modal_companion
    {X : Axioms α} (hX : ∀ B ∈ X, B.IsClosedNegativeAxiom)
    [Fact ((starAxioms X) ⊬ᴺ ⊥)]
    (A : Formula α) :
    (X ⊢ⱽ A) ↔ ((starAxioms X) ⊢ᴺ corsi A) := by
  haveI : Fact (∀ B ∈ X, B.IsClosedNegativeAxiom) := ⟨hX⟩;
  constructor;
  · intro h;
    apply Modal.FMT.finite_model_property;
    intro κ _ M_M hValid x;
    apply (modalToProp_truthlemma M_M A x).mpr;
    apply FMTSemantics.soundness_model h (modalToPropModel M_M) ?_;
    intro B hB;
    obtain ⟨C, rfl, hCClosed, _⟩ := Formula.iff_isCNA.mp (hX B hB);
    intro x' y _ hCY;
    have hValC : ∀ y, ¬ Modal.FMT.Forced (M := M_M) y (corsi C) := by
      intro y';
      have hMem : ∼(corsi C) ∈ starAxioms X := by
        simp only [starAxioms, Finset.mem_image];
        exact ⟨∼C, hB, rfl⟩;
      exact hValid _ hMem y';
    exact modalToProp_notForces_closed_of_neg M_M hCClosed hValC y hCY;
  · intro h;
    apply FMTSemantics.finite_frame_property (fun B hB => closed_of_CNA (hX B hB));
    intro κ _ F hF V x;
    apply (propToModal_truthlemma ⟨F, V⟩ A x).mpr;
    apply Modal.FMT.soundness_model h (propToModalModel ⟨F, V⟩) ?_ x;
    intro B hB;
    obtain ⟨B', hB'X, rfl⟩ := Finset.mem_image.mp hB;
    obtain ⟨C, rfl, hCClosed, _⟩ := Formula.iff_isCNA.mp (hX B' hB'X);
    intro y hYC;
    have hPC : FMTSemantics.Forces (M := ⟨F, V⟩) y C :=
      (propToModal_truthlemma ⟨F, V⟩ C y).mpr hYC;
    have hFC : F ⊨ ∼C := hF (∼C) hB'X;
    have hNF : ∀ x : F.World, ¬ FMTSemantics.FrameForces x C :=
      (FMTSemantics.iff_FrameValid_neg_of_closed hCClosed).mp hFC;
    exact hNF y ((FMTSemantics.iff_FrameForces_Forces_of_closed hCClosed).mpr hPC);

end ModalCompanionThm

end ModalCompanion

end
