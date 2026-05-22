module

public import VeryWeakSubintuitionistic.Proof.Int

@[expose] public section

namespace KripkeSemantics

structure Frame (κ : Type*) where
  Rel' : κ → κ → Prop
  root' : κ

namespace Frame

variable {κ α : Type*} {F : Frame κ}

abbrev World (_ : Frame κ) := κ
abbrev Rel {F : Frame κ} (x y : F.World) := F.Rel' x y
infix:45 " ≺ " => Rel

abbrev root : F.World := F.root'

end Frame


structure Model (κ : Type*) (α : Type*) extends Frame κ where
  Val : α → (toFrame.World) → Prop

namespace Model

variable {κ α : Type*} {M : Model κ α}

instance : CoeFun (Model κ α) (λ M => α → M.World → Prop) := ⟨fun m => m.Val⟩

end Model


variable {κ α : Type*} {M : Model κ α} {x y : M.World}
         {A B C : Formula α}

@[grind]
def Forces {M : Model κ α} (x : M.World) : Formula α → Prop
  | #a     => M a x
  | ⊥      => False
  | A ⋏ B   => Forces x A ∧ Forces x B
  | A ⋎ B  => Forces x A ∨ Forces x B
  | A 🡒 B => ∀ y, x ≺ y → (Forces y A → Forces y B)
infix:45 " ⊩ " => Forces

abbrev NotForces {M : Model κ α} (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces

lemma iff_not_Forces_imp : (x ⊮ A 🡒 B) ↔ (∃ y, x ≺ y ∧ (y ⊩ A ∧ y ⊮ B)) := by
  simp [NotForces, Forces];


@[grind] def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:45 " ⊨ " => Validates

@[grind] abbrev NotValidates (M : Model κ α) (A : Formula α) : Prop := ¬(M ⊨ A)
infix:45 " ⊭ " => NotValidates

lemma iff_valid_exists_world_not_Forces {M : Model κ α} {A : Formula α} : (M ⊭ A) ↔ (∃ x : M.World, x ⊮ A) := by
  simp only [NotValidates, Validates, not_forall, NotForces];


@[grind] def FrameValid (F : Frame κ) (A : Formula α) : Prop := ∀ V, Validates ⟨F, V⟩ A
infix:45 " ⊨ " => FrameValid

abbrev NotFrameValid (F : Frame κ) (A : Formula α) : Prop := ¬(F ⊨ A)
infix:45 " ⊭ " => NotFrameValid

lemma iff_notFramevalid_exists_model_world {F : Frame κ} {A : Formula α} : (F ⊭ A) ↔ (∃ V, ∃ x : (⟨F, V⟩ : Model κ α).World, x ⊮ A) := by
  simp only [NotFrameValid, FrameValid, Validates, not_forall, NotForces];


class Model.Int (M : Model κ α) where
  Rel_refl : ∀ {x : M.World}, x ≺ x
  Rel_trans : ∀ {x y z : M.World}, x ≺ y → y ≺ z → x ≺ z
  Val_mono : ∀ {a : α} {x y : M.World}, M a x → x ≺ y → M a y

namespace Model

export Model.Int (Rel_refl Rel_trans Val_mono)

attribute [simp, grind .] Rel_refl
attribute [grind =>] Val_mono

end Model


section Soundness

variable {κ α : Type*}
         {M : Model κ α} {x y : M.World}
         {A B C : Formula α}

@[grind =>]
lemma formula_persistency {M : Model κ α} [M.Int] {x y : M.World} : x ⊩ A → x ≺ y → y ⊩ A := by
  intro h Rxy;
  induction A generalizing y with
  | imp A B ihA ihB =>
    intro z Ryz hyA;
    have Rxz : x ≺ z := M.Rel_trans Rxy Ryz;
    grind;
  | _ => grind;

@[grind .] lemma valid_andElimL : M ⊨ (A ⋏ B) 🡒 A := by grind;
@[grind .] lemma valid_andElimR : M ⊨ (A ⋏ B) 🡒 B := by grind;
@[grind .] lemma valid_orIntroL : M ⊨ A 🡒 (A ⋎ B) := by grind;
@[grind .] lemma valid_orIntroR : M ⊨ B 🡒 (A ⋎ B) := by grind;

@[grind .] lemma valid_implyK [M.Int] : M ⊨ A 🡒 B 🡒 A := by grind;

@[grind .]
lemma valid_implyS [M.Int] : M ⊨ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := by
  intro x y Rxy hyABC z Ryz hzAB w Rzw hwA;
  apply hyABC w ?_ hwA w;
  . exact M.Rel_refl;
  . exact @hzAB w Rzw hwA;
  . exact M.Rel_trans Ryz Rzw;

@[grind .] lemma valid_andIntro [M.Int] : M ⊨ (A 🡒 B 🡒 (A ⋏ B)) := by grind;
@[grind .] lemma valid_orElim [M.Int] : M ⊨ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := by grind;
@[grind .] lemma valid_efq [M.Int] : M ⊨ ⊥ 🡒 A := by grind;
@[grind =>] lemma valid_mdp [M.Int] (hAB : M ⊨ A 🡒 B) (hA : M ⊨ A) : M ⊨ B := by intro x; exact hAB x x (by simp) (hA x);

theorem soundness : (Λ ⊢ᴵ A) → (∀ {κ}, ∀ M : Model κ α, [M.Int] → (∀ φ ∈ Λ, M ⊨ φ) → M ⊨ A) := by intro h; induction h <;> grind;

end Soundness

end KripkeSemantics


@[simp, grind .]
theorem consistency_of_Int : (∅ ⊬ᴵ (⊥ : Formula α)) := by
  by_contra! hC;
  let M : KripkeSemantics.Model (Fin 1) α := {
    Rel' := λ _ _ => True,
    root' := 1,
    Val := λ _ _ => True
  };
  have : M.Int := {
    Rel_refl := by grind,
    Rel_trans := by grind,
    Val_mono := by grind
  };
  exact KripkeSemantics.soundness hC M (by grind) M.root;

end
