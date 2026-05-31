module

public import VeryWeakSubintuitionistic.Modal.Proof.N

@[expose] public section

namespace Modal.FMT

structure Frame (κ : Type*) (α : Type*) where
  Rel' : Formula α → κ → κ → Prop
  root' : κ

namespace Frame

variable {κ α : Type*} {F : Frame κ α}

abbrev World (_ : Frame κ α) := κ
abbrev Rel {F : Frame κ α} (A : Formula α) (x y : F.World) := F.Rel' A x y
notation:45 x:90 " ≺[" φ "] " y:90 => Frame.Rel φ x y

abbrev root : F.World := F.root'

end Frame


structure Model (κ : Type*) (α : Type*) extends Frame κ α where
  Val : α → (toFrame.World) → Prop

namespace Model

instance : CoeFun (Model κ α) (λ M => α → M.World → Prop) := ⟨fun m => m.Val⟩

end Model


variable {κ α : Type*} {M : Model κ α} {A B C : Formula α}

@[grind]
def Forced {M : Model κ α} (x : M.World) : Formula α → Prop
  | #a     => M a x
  | ⊥      => False
  | A 🡒 B  => Forced x A → Forced x B
  | □A     => ∀ y, x ≺[□A] y → Forced y A
infix:45 " ⊩ " => Forced

abbrev NotForced {M : Model κ α} (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForced

lemma forces_and : x ⊩ A ⋏ B ↔ (x ⊩ A ∧ x ⊩ B) := by grind;
lemma forces_or : x ⊩ A ⋎ B ↔ (x ⊩ A ∨ x ⊩ B) := by grind;
lemma forces_top : x ⊩ ⊤ := by grind;
lemma forces_not : x ⊩ ∼A ↔ (x ⊮ A) := by grind;

attribute [simp, grind .] forces_top
attribute [grind =] forces_and forces_or forces_not

lemma notForces_box : (x ⊮ □A) ↔ (∃ y, x ≺[□A] y ∧ y ⊮ A) := by grind;

@[grind]
def ModelValid (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:45 " ⊨ " => ModelValid

@[grind]
abbrev ModelInvalid (M : Model κ α) (A : Formula α) : Prop := ¬(M ⊨ A)
infix:45 " ⊭ " => ModelInvalid

lemma iff_Valid_exists_world_not_Forces {M : Model κ α} : (M ⊭ A) ↔ (∃ x : M.World, x ⊮ A) := by
  simp only [ModelInvalid, ModelValid, not_forall, NotForced];


@[grind]
def FrameValid (F : Frame κ α) (A : Formula α) : Prop := ∀ V, ModelValid ⟨F, V⟩ A
infix:45 " ⊨ " => FrameValid

abbrev FrameInvalid (F : Frame κ α) (A : Formula α) : Prop := ¬(F ⊨ A)
infix:45 " ⊭ " => FrameInvalid

lemma iff_frameInvalid_exists_model_world {F : Frame κ α} : (F ⊭ A) ↔ (∃ V, ∃ x : (⟨F, V⟩ : Model κ α).World, x ⊮ A) := by grind;


section Soundness

variable {κ α : Type*} {F : Frame κ α} {M : Model κ α} {A B C : Formula α}

@[grind .] lemma frameValid_implyK : F ⊨ A 🡒 B 🡒 A := by grind;
@[grind .] lemma frameValid_implyS : F ⊨ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := by grind;
@[grind .] lemma frameValid_efq : F ⊨ ⊥ 🡒 A := by grind;
@[grind .] lemma frameValid_dne : F ⊨ ∼∼A 🡒 A := by grind;
@[grind .] lemma frameValid_andElimL : F ⊨ (A ⋏ B) 🡒 A := by grind;
@[grind .] lemma frameValid_andElimR : F ⊨ (A ⋏ B) 🡒 B := by grind;

@[grind =>] lemma frameValid_mdp (hAB : F ⊨ A 🡒 B) (hA : F ⊨ A) : F ⊨ B := by intro V x; exact hAB V x $ hA V x;
@[grind <=] lemma frameValid_nec (hA : F ⊨ A) : F ⊨ □A := by intro V x y Rxy; exact hA V y;

@[grind =>] lemma modelValid_mdp (hAB : M ⊨ A 🡒 B) (hA : M ⊨ A) : M ⊨ B := by intro x; exact hAB x $ hA x;
@[grind <=] lemma modelValid_nec (hA : M ⊨ A) : M ⊨ □A := by intro x y Rxy; exact hA y;


theorem soundness_frame : (Λ ⊢ᴺ A) → (∀ {κ}, ∀ F : Frame κ α, (∀ B ∈ Λ, F ⊨ B) → F ⊨ A) := by
  intro h _ F hΛ; induction h <;> grind;

theorem soundness_model : (Λ ⊢ᴺ A) → (∀ {κ}, ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A) := by
  intro h _ M hM; induction h <;> grind;


@[grind .]
lemma frameInvalid_bot : F ⊭ ⊥ := by
  intro h;
  exact @h (λ _ _ => True) F.root;

@[simp, grind .]
theorem consistency_of_N : (∅ ⊬ᴺ (⊥ : Formula α)) := by
  by_contra!;
  let F : Frame (Fin 1) α := ⟨λ _ _ _ => True, 0⟩;
  exact frameInvalid_bot $ soundness_frame this F (by grind);

end Soundness

end FMT

end Modal

end
