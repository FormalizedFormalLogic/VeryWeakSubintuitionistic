module

public import VeryWeakSubintuitionistic.Modal.FMT.Completeness
public import VeryWeakSubintuitionistic.Modal.Proof.NR

@[expose] public section

namespace Modal

variable {α : Type u}

namespace FMT

section Soundness

variable {κ : Type*} {F : Frame κ α} {M : Model κ α} {𝔸 : Axioms α} {A B C : Formula α}

namespace Frame

class Serial (F : Frame κ α) : Prop where
  serial : ∀ (x : F.World) (A : Formula α), ∃ y : F.World, x ≺[□A] y
export Serial (serial)

end Frame

@[grind <=]
lemma frameValid_ros [F.Serial] (hA : F ⊨ ∼A) : F ⊨ ∼□A := by
  intro V x hbox;
  obtain ⟨y, Rxy⟩ := Frame.serial x A;
  exact hA V y $ hbox y Rxy;

@[grind <=]
lemma modelValid_ros [M.Serial] (hA : M ⊨ ∼A) : M ⊨ ∼□A := by
  intro x hbox;
  obtain ⟨y, Rxy⟩ := Frame.serial (F := M.toFrame) x A;
  exact hA y $ hbox y Rxy;

theorem soundness_frame_ros [F.Serial] (h𝔸 : ∀ B ∈ 𝔸, F ⊨ B) : (⊢ʰ[NR;𝔸] A) → F ⊨ A := by
  intro h; induction h <;> grind;

theorem soundness_model_ros [M.Serial] (h𝔸 : ∀ B ∈ 𝔸, M ⊨ B) : (⊢ʰ[NR;𝔸] A) → M ⊨ A := by
  intro h; induction h <;> grind;

@[simp, grind .]
theorem consistency_of_NR : (⊬ʰ[NR;∅] (⊥ : Formula α)) := by
  by_contra! h;
  let F : Frame (Fin 1) α := ⟨λ _ _ _ => True, 0⟩;
  haveI : F.Serial := ⟨λ x _ => ⟨x, trivial⟩⟩;
  exact frameInvalid_bot $ soundness_frame_ros (F := F) (by grind) h;

end Soundness

end FMT

end Modal

end
