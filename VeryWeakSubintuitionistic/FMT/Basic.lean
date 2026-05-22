module

public import VeryWeakSubintuitionistic.Proof.VF

@[expose] public section

structure FMTFrame (κ : Type*) (α : Type*) where
  Rel' : Formula α → κ → κ → Prop
  root' : κ
  root_rooted' : ∀ {A x}, Rel' A root' x

namespace FMTFrame

variable {κ α : Type*} {F : FMTFrame κ α}

abbrev World (_ : FMTFrame κ α) := κ
abbrev Rel {F : FMTFrame κ α} (A : Formula α) (x y : F.World) := F.Rel' A x y
notation:45 x:90 " ≺[" φ "] " y:90 => FMTFrame.Rel φ x y

abbrev root : F.World := F.root'
@[grind .] lemma root_rooted : ∀ {A x}, F.root ≺[A] x := F.root_rooted'

end FMTFrame


structure FMTModel (κ : Type*) (α : Type*) extends FMTFrame κ α where
  Val : α → (toFMTFrame.World) → Prop

namespace FMTModel

instance : CoeFun (FMTModel κ α) (λ M => α → M.World → Prop) := ⟨fun m => m.Val⟩

end FMTModel


variable {κ α : Type*} {M : FMTModel κ α} {A B C : Formula α}

@[grind]
def Forces {M : FMTModel κ α} (x : M.World) : Formula α → Prop
  | #a     => M a x
  | ⊥      => False
  | A ⋏ B   => Forces x A ∧ Forces x B
  | A ⋎ B  => Forces x A ∨ Forces x B
  | A 🡒 B => ∀ y, x ≺[A 🡒 B] y → (Forces y A → Forces y B)
infix:45 " ⊩ " => Forces

abbrev NotForces {M : FMTModel κ α} (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces

lemma iff_not_Forces_imp : (x ⊮ A 🡒 B) ↔ (∃ y, x ≺[A 🡒 B] y ∧ (y ⊩ A ∧ y ⊮ B)) := by
  simp [NotForces, Forces];


@[grind] def Validates (M : FMTModel κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:45 " ⊨ " => Validates

@[grind] abbrev NotValidates (M : FMTModel κ α) (A : Formula α) : Prop := ¬(M ⊨ A)
infix:45 " ⊭ " => NotValidates

lemma iff_Valid_exists_world_not_Forces {M : FMTModel κ α} {A : Formula α} : (M ⊭ A) ↔ (∃ x : M.World, x ⊮ A) := by
  simp only [NotValidates, Validates, not_forall, NotForces];


@[grind] def FMTFrameValid (F : FMTFrame κ α) (A : Formula α) : Prop := ∀ V, Validates ⟨F, V⟩ A
infix:45 " ⊨ " => FMTFrameValid

abbrev NotFMTFrameValid (F : FMTFrame κ α) (A : Formula α) : Prop := ¬(F ⊨ A)
infix:45 " ⊭ " => NotFMTFrameValid

lemma iff_notFMTFrameValid_exists_model_world {F : FMTFrame κ α} {A : Formula α} : (F ⊭ A) ↔ (∃ V, ∃ x : (⟨F, V⟩ : FMTModel κ α).World, x ⊮ A) := by
  simp only [NotFMTFrameValid, FMTFrameValid, Validates, not_forall, NotForces];


section Soundness

variable {κ α : Type*} {M : FMTModel κ α} {A B C : Formula α}

@[grind .] lemma valid_andElimL : M ⊨ (A ⋏ B) 🡒 A := by grind;
@[grind .] lemma valid_andElimR : M ⊨ (A ⋏ B) 🡒 B := by grind;
@[grind .] lemma valid_orIntroL : M ⊨ A 🡒 (A ⋎ B) := by grind;
@[grind .] lemma valid_orIntroR : M ⊨ B 🡒 (A ⋎ B) := by grind;
@[grind .] lemma valid_distributeAndOr : M ⊨ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by grind;
@[grind .] lemma valid_impId : M ⊨ A 🡒 A := by grind;
@[grind .] lemma valid_efq : M ⊨ ⊥ 🡒 A := by grind;

@[grind <=]
lemma valid_ruleI (hAB : M ⊨ A 🡒 B) (hBC : M ⊨ B 🡒 C) : M ⊨ A 🡒 C := by
  intro x y Rxy hya;
  exact hBC M.root y (by grind) $ hAB M.root y (by grind) hya;

@[grind <=]
lemma valid_ruleC (hAB : M ⊨ A 🡒 B) (hAC : M ⊨ A 🡒 C) : M ⊨ A 🡒 (B ⋏ C) := by
  intro x y Rxy hya;
  have := hAB M.root y (by grind) hya;
  have := hAC M.root y (by grind) hya;
  grind;

@[grind <=]
lemma valid_ruleD (hAC : M ⊨ A 🡒 C) (hBC : M ⊨ B 🡒 C) : M ⊨ (A ⋎ B) 🡒 C := by
  rintro x y Rxy (h | h);
  . exact hAC M.root y (by grind) h;
  . exact hBC M.root y (by grind) h;

@[grind =>]
lemma valid_mdp (hAB : M ⊨ A 🡒 B) (hA : M ⊨ A) : M ⊨ B := by
  intro x;
  exact hAB _ x (show M.root ≺[A 🡒 B] x by grind) (by grind);

@[grind <=]
lemma valid_af (hA : M ⊨ A) : M ⊨ B 🡒 A := by grind;

theorem soundness : (Λ ⊢ⱽ A) → (∀ {κ}, ∀ M : FMTModel κ α, (∀ φ ∈ Λ, M ⊨ φ) → M ⊨ A) := by
  intro h _ M hΛ; induction h <;> grind;


@[grind .]
theorem consistency_of_VF : (∅ ⊬ (⊥ : Formula α)) := by
  by_contra!;
  let M : FMTModel (Fin 1) α := {
    Rel' := λ _ _ _ => True,
    root' := 1,
    root_rooted' := by grind;
    Val := λ _ _ => True
  };
  have : (1 : M.World) ⊩ ⊥ := soundness this M (by grind) _;
  contradiction;

@[grind .]
theorem consistency_VF : (∅ ⊬ (⊥ : Formula α)) := by
  by_contra!;
  let M : FMTModel (Fin 1) α := {
    Rel' := λ _ _ _ => True,
    root' := 1,
    root_rooted' := by grind;
    Val := λ _ _ => True
  };
  have : (1 : M.World) ⊩ ⊥ := soundness this M (by grind) _;
  contradiction;

example : (∅ ⊬ (⊤ 🡒 (#0 ⋏ #1) 🡘 (⊤ 🡒 (#1 ⋏ #0)))) := by
  by_contra!;
  let M : FMTModel (Fin 3) ℕ := {
    Rel' := λ A x y =>
      match A with
      | (⊤ 🡒 (#0 ⋏ #1)) => x ≠ 1
      | (⊤ 🡒 (#1 ⋏ #0)) => x ≤ y
      | _ => True
    ,
    root' := 0,
    root_rooted' := by grind;
    Val := λ a x =>
      match a with
      | 0 => x = 2
      | _ => False
  };
  have : (0 : M.World) ⊩ (⊤ 🡒 (#0 ⋏ #1) 🡘 (⊤ 🡒 (#1 ⋏ #0))) := soundness this M (by grind) 0;
  have : (2 : M.World) ⊩ #1 := @this.1 1 (by grind) (by grind) 2 (by grind) (by grind) |>.1;
  contradiction;

end Soundness


section

@[grind]
def FMTFrameForces {F : FMTFrame κ α} (x : F.World) (A : Formula α) (A_closed : A.Closed := by grind) : Prop :=
  match A with
  | ⊥ => False
  | A ⋏ B => FMTFrameForces x A ∧ FMTFrameForces x B
  | A ⋎ B => FMTFrameForces x A ∨ FMTFrameForces x B
  | A 🡒 B => ∀ {y}, F.Rel (A 🡒 B) x y → (FMTFrameForces y A → FMTFrameForces y B)

variable {F : FMTFrame κ α}

@[grind =_]
lemma iff_FMTFrameForces_Forces_of_closed {F : FMTFrame κ α} {x : F.World} {V} {A} (A_closed : A.Closed) : FMTFrameForces x A ↔ (Forces (M := ⟨F, V⟩) x A) := by
  induction A generalizing x <;> grind;

lemma iff_Forces_CNA (A_closed : A.Closed) : FMTFrameValid F (∼A) ↔ ∀ x : F.World, ¬(FMTFrameForces x A) := by
  constructor;
  . intro h x;
    by_contra!
    exact h (λ _ _ => True) F.root x (by grind) $ iff_FMTFrameForces_Forces_of_closed (by grind) |>.mp this;
  . intro h V x;
    grind;

@[grind =_]
lemma iff_closed_not_and : F ⊨ ∼(A ⋎ B) ↔ (FMTFrameValid F (∼A) ∧ FMTFrameValid F (∼B)) := by grind;

lemma iff_closed_not_imp (A_closed : A.Closed) (B_closed : B.Closed) : F ⊨ ∼(A 🡒 B) ↔ (∀ x : F.World, ∃ y : F.World, x ≺[A 🡒 B] y ∧ (FMTFrameForces y A ∧ ¬FMTFrameForces y B)) := by
  apply Iff.trans (iff_Forces_CNA (A := A 🡒 B) (by grind));
  simp [FMTFrameForces];

lemma iff_closed_dn (A_closed : A.Closed) : F ⊨ ∼∼A ↔ (∀ x : F.World, ∃ y : F.World, x ≺[∼A] y ∧ (FMTFrameForces y A)) := by
  apply Iff.trans (iff_closed_not_imp (A := A) (B := ⊥) (by grind) (by grind));
  simp [FMTFrameForces];

end
