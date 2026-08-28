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

end
