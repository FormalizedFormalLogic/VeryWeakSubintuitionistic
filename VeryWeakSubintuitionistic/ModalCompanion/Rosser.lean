module

public import VeryWeakSubintuitionistic.ModalCompanion.Basic
public import VeryWeakSubintuitionistic.Modal.FMT.Ros
public import VeryWeakSubintuitionistic.Propositional.FMT.Ros

@[expose] public section

variable {α : Type u}

section PropToModal

variable {κ : Type*} {PM : FMTSemantics.Model κ α}

lemma propToModalModel_serial [PM.Rosser] : (propToModalModel PM).Serial := by
  constructor;
  intro x A;
  by_cases hA : ∃ C D : Formula α, A = (C.corsi) 🡒 (D.corsi);
  . obtain ⟨C, D, rfl⟩ := hA;
    obtain ⟨y, Rxy⟩ := FMTSemantics.Frame.ros (F := PM.toFrame) x C D;
    use y;
    intro C' D' heq;
    obtain ⟨hC, hD⟩ : C.corsi = C'.corsi ∧ D.corsi = D'.corsi := by grind;
    cases Formula.corsi_injective hC;
    cases Formula.corsi_injective hD;
    exact Rxy;
  . use x;
    intro C D heq;
    exact absurd ⟨C, D, by grind⟩ hA;

end PropToModal


section ModalToProp

variable {κ : Type*} {MM : Modal.FMT.Model κ α}

lemma modalToPropModel_rosser [MM.Serial] : (modalToPropModel MM).Rosser := by
  constructor;
  intro x A B;
  match x with
  | .inr () => exact ⟨.inr (), trivial⟩;
  | .inl x =>
    obtain ⟨y, Rxy⟩ := Modal.FMT.Frame.serial (F := MM.toFrame) x ((A.corsi) 🡒 (B.corsi));
    exact ⟨.inl y, Rxy⟩;

end ModalToProp


section

variable [DecidableEq α] {𝔸 : Axioms α} {A : Formula α}

lemma provableNR_star_of_provableVFR
  [Fact (∀ B ∈ 𝔸, B.IsClosedNegativeAxiom)]
  : (⊢ʰ[VFR;𝔸] A) → (⊢ʰ[NR;𝔸.star] A.corsi) := by
  have hCNA : ∀ B ∈ 𝔸, B.IsClosedNegativeAxiom := Fact.out;
  intro h;
  apply Modal.FMT.finite_model_property_ros;
  intro κ _ MM hSer hValid x;
  haveI := hSer;
  haveI := modalToPropModel_rosser (MM := MM);
  apply (modalToProp_truthlemma).mpr;
  apply FMTSemantics.soundness_model_ros ?_ h;
  intro B hB;
  obtain ⟨C, rfl, hCClosed, _⟩ := Formula.iff_isCNA.mp (hCNA B hB);
  intro y z Ryz hzC;
  have hValC : ∀ y, ¬ Modal.FMT.Forced (M := MM) y (C.corsi) := by
    intro y';
    have hMem : ∼(C.corsi) ∈ 𝔸.star := Axioms.mem_star_of_mem_neg hB;
    exact hValid _ hMem y';
  exact modalToProp_notForces_closed_of_neg hCClosed hValC hzC;

lemma provableNR_star_repeatNeg_of_provableNR_star {N : Finset ℕ}
  : ⊢ʰ[NR;𝔸.star] A.corsi → ⊢ʰ[NR;𝔸.star ∪ N.image (λ n => ∼□(∼^[2 * n]⊥))] A.corsi := by
  apply Modal.NR.ProvableHilbert.ofSubsetAxm;
  grind;

lemma provableVFR_of_provableNR_star
  [Fact (∀ B ∈ 𝔸, B.IsClosedNegativeAxiom)]
  : (⊢ʰ[NR;𝔸.star] A.corsi) → ⊢ʰ[VFR;𝔸] A := by
  have hCNA : ∀ B ∈ 𝔸, B.IsClosedNegativeAxiom := Fact.out;
  contrapose;
  intro h;
  replace h := FMTSemantics.result_frame_ros (𝔸 := 𝔸) (by grind) |>.not.out 0 1 |>.mp h;
  push Not at h;
  obtain ⟨κ, PF, hRos, hPF, h⟩ := h;
  obtain ⟨PV, x, hx⟩ := FMTSemantics.iff_notFrameValid_exists_model_world.mp h;
  haveI : FMTSemantics.Frame.Rosser ((⟨PF, PV⟩ : FMTSemantics.Model κ α).toFrame) := hRos;
  apply Modal.FMT.result_model_ros.not.out 0 1 |>.mpr;
  push Not;
  refine ⟨κ, propToModalModel ⟨PF, PV⟩, propToModalModel_serial, ?_, ?_⟩;
  . intro B hB;
    obtain ⟨C, hC₁, hC₂⟩ := Finset.mem_filterMap _ |>.mp hB;
    split at hC₂;
    . simp only [Option.some.injEq] at hC₂;
      subst hC₂;
      rename_i C;
      obtain ⟨D, _, _, _⟩ := Formula.iff_isCNA.mp $ hCNA (∼C) ‹_›;
      intro y;
      apply Modal.FMT.forces_not.mpr;
      apply propToModal_truthlemma.not.mp;
      exact FMTSemantics.iff_FrameForces_Forces_of_closed (by grind) |>.not.mp
        $ FMTSemantics.iff_FrameValid_neg_of_closed (by grind) |>.mp (hPF _ hC₁) y;
    . contradiction;
  . replace hx := propToModal_truthlemma.not.mp hx;
    apply Modal.FMT.iff_Valid_exists_world_not_Forces.mpr;
    use x;

lemma provableVFR_of_provableNR_star_repeatNeg
  {N : Finset ℕ}
  [Fact (∀ B ∈ 𝔸, B.IsClosedNegativeAxiom)]
  : (⊢ʰ[NR;𝔸.star ∪ N.image (λ n => ∼□(∼^[2 * n]⊥))] A.corsi) → ⊢ʰ[VFR;𝔸] A := by
  have hCNA : ∀ B ∈ 𝔸, B.IsClosedNegativeAxiom := Fact.out;
  contrapose;
  intro h;
  replace h := FMTSemantics.result_frame_ros (𝔸 := 𝔸) (by grind) |>.not.out 0 1 |>.mp h;
  push Not at h;
  obtain ⟨κ, PF, hRos, hPF, h⟩ := h;
  obtain ⟨PV, x, hx⟩ := FMTSemantics.iff_notFrameValid_exists_model_world.mp h;
  haveI : FMTSemantics.Frame.Rosser ((⟨PF, PV⟩ : FMTSemantics.Model κ α).toFrame) := hRos;
  apply Modal.FMT.result_model_ros.not.out 0 1 |>.mpr;
  push Not;
  refine ⟨κ, propToModalModel ⟨PF, PV⟩, propToModalModel_serial, ?_, ?_⟩;
  . intro B hB;
    simp only [Finset.mem_union, Finset.mem_image] at hB;
    rcases hB with (hB | ⟨n, hN, rfl⟩);
    . obtain ⟨C, hC₁, hC₂⟩ := Finset.mem_filterMap _ |>.mp hB;
      split at hC₂;
      . simp only [Option.some.injEq] at hC₂;
        subst hC₂;
        rename_i C;
        obtain ⟨D, _, _, _⟩ := Formula.iff_isCNA.mp $ hCNA (∼C) ‹_›;
        intro y;
        apply Modal.FMT.forces_not.mpr;
        apply propToModal_truthlemma.not.mp;
        exact FMTSemantics.iff_FrameForces_Forces_of_closed (by grind) |>.not.mp
          $ FMTSemantics.iff_FrameValid_neg_of_closed (by grind) |>.mp (hPF _ hC₁) y;
      . contradiction;
    . intro y;
      apply Modal.FMT.notForces_box.mpr;
      use y;
      constructor;
      . intro C D;
        grind;
      . grind;
  . replace hx := propToModal_truthlemma.not.mp hx;
    apply Modal.FMT.iff_Valid_exists_world_not_Forces.mpr;
    use x;

theorem modal_companion_ros [Fact (∀ B ∈ 𝔸, B.IsClosedNegativeAxiom)]
  : (⊢ʰ[VFR;𝔸] A) ↔ (⊢ʰ[NR;𝔸.star] A.corsi) :=
  ⟨provableNR_star_of_provableVFR, provableVFR_of_provableNR_star⟩

theorem modal_companion_VFR : (⊢ʰ[VFR;∅] A) ↔ (⊢ʰ[NR;∅] A.corsi) := by
  have : Fact (∀ B ∈ (∅ : Axioms α), B.IsClosedNegativeAxiom) := ⟨by grind⟩;
  simpa [Axioms.star] using modal_companion_ros (𝔸 := ∅) (A := A);

end

end
