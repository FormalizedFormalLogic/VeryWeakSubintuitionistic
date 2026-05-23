module

public import VeryWeakSubintuitionistic.Proof.VF

@[expose] public section

namespace FMTSemantics

structure Frame (κ : Type*) (α : Type*) where
  Rel' : Formula α → κ → κ → Prop
  root' : κ
  root_rooted' : ∀ {A x}, Rel' A root' x

namespace Frame

variable {κ α : Type*} {F : Frame κ α}

abbrev World (_ : Frame κ α) := κ
abbrev Rel {F : Frame κ α} (A : Formula α) (x y : F.World) := F.Rel' A x y
notation:45 x:90 " ≺[" φ "] " y:90 => Frame.Rel φ x y

abbrev root : F.World := F.root'
@[grind .] lemma root_rooted : ∀ {A x}, F.root ≺[A] x := F.root_rooted'

end Frame


structure Model (κ : Type*) (α : Type*) extends Frame κ α where
  Val : α → (toFrame.World) → Prop

namespace Model

instance : CoeFun (Model κ α) (λ M => α → M.World → Prop) := ⟨fun m => m.Val⟩

end Model


variable {κ α : Type*} {M : Model κ α} {A B C : Formula α}

@[grind]
def Forces {M : Model κ α} (x : M.World) : Formula α → Prop
  | #a     => M a x
  | ⊥      => False
  | A ⋏ B   => Forces x A ∧ Forces x B
  | A ⋎ B  => Forces x A ∨ Forces x B
  | A 🡒 B => ∀ y, x ≺[A 🡒 B] y → (Forces y A → Forces y B)
infix:45 " ⊩ " => Forces

abbrev NotForces {M : Model κ α} (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces

lemma iff_not_Forces_imp : (x ⊮ A 🡒 B) ↔ (∃ y, x ≺[A 🡒 B] y ∧ (y ⊩ A ∧ y ⊮ B)) := by
  simp [NotForces, Forces];

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by intro y; simp;


@[grind] def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:45 " ⊨ " => Validates

@[grind] abbrev NotValidates (M : Model κ α) (A : Formula α) : Prop := ¬(M ⊨ A)
infix:45 " ⊭ " => NotValidates

lemma iff_Valid_exists_world_not_Forces {M : Model κ α} {A : Formula α} : (M ⊭ A) ↔ (∃ x : M.World, x ⊮ A) := by
  simp only [NotValidates, Validates, not_forall, NotForces];


@[grind] def FrameValid (F : Frame κ α) (A : Formula α) : Prop := ∀ V, Validates ⟨F, V⟩ A
infix:45 " ⊨ " => FrameValid

abbrev NotFrameValid (F : Frame κ α) (A : Formula α) : Prop := ¬(F ⊨ A)
infix:45 " ⊭ " => NotFrameValid

lemma iff_notFrameValid_exists_model_world {F : Frame κ α} {A : Formula α} : (F ⊭ A) ↔ (∃ V, ∃ x : (⟨F, V⟩ : Model κ α).World, x ⊮ A) := by
  simp only [NotFrameValid, FrameValid, Validates, not_forall, NotForces];


section Soundness

variable {κ α : Type*} {F : Frame κ α} {M : Model κ α} {A B C : Formula α}

@[grind .] lemma frameValid_andElimL : F ⊨ (A ⋏ B) 🡒 A := by grind;
@[grind .] lemma frameValid_andElimR : F ⊨ (A ⋏ B) 🡒 B := by grind;
@[grind .] lemma frameValid_orIntroL : F ⊨ A 🡒 (A ⋎ B) := by grind;
@[grind .] lemma frameValid_orIntroR : F ⊨ B 🡒 (A ⋎ B) := by grind;
@[grind .] lemma frameValid_distributeAndOr : F ⊨ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by grind;
@[grind .] lemma frameValid_impId : F ⊨ A 🡒 A := by grind;
@[grind .] lemma frameValid_efq : F ⊨ ⊥ 🡒 A := by grind;

@[simp, grind .]
lemma not_frameValid_bot : F ⊭ ⊥ := by
  intro h;
  have := @h (λ _ _ => True) F.root;
  contradiction;


@[grind <=]
lemma frameValid_ruleI (hAB : F ⊨ A 🡒 B) (hBC : F ⊨ B 🡒 C) : F ⊨ A 🡒 C := by
  intro V x y Rxy hya;
  exact hBC V F.root y (by grind) $ hAB V F.root y (by grind) hya;

@[grind <=]
lemma frameValid_ruleC (hAB : F ⊨ A 🡒 B) (hAC : F ⊨ A 🡒 C) : F ⊨ A 🡒 (B ⋏ C) := by
  intro V x y Rxy hya;
  have := hAB V F.root y (by grind) hya;
  have := hAC V F.root y (by grind) hya;
  grind;

@[grind <=]
lemma frameValid_ruleD (hAC : F ⊨ A 🡒 C) (hBC : F ⊨ B 🡒 C) : F ⊨ (A ⋎ B) 🡒 C := by
  rintro V x y Rxy (h | h);
  . exact hAC V F.root y (by grind) h;
  . exact hBC V F.root y (by grind) h;

@[grind =>]
lemma frameValid_mdp (hAB : F ⊨ A 🡒 B) (hA : F ⊨ A) : F ⊨ B := by
  intro V x;
  exact hAB V F.root x (show F.root ≺[A 🡒 B] x by grind) (by grind);

@[grind <=]
lemma frameValid_af (hA : F ⊨ A) : F ⊨ B 🡒 A := by grind;

theorem soundness_frame : (Λ ⊢ⱽ A) → (∀ {κ}, ∀ F : Frame κ α, (∀ B ∈ Λ, F ⊨ B) → F ⊨ A) := by
  intro h _ F hΛ; induction h <;> grind;



@[grind <=]
lemma modelValid_ruleI (hAB : M ⊨ A 🡒 B) (hBC : M ⊨ B 🡒 C) : M ⊨ A 🡒 C := by
  intro x y Rxy hya;
  exact hBC M.root y (by grind) $ hAB M.root y (by grind) hya;

@[grind <=]
lemma modelValid_ruleC (hAB : M ⊨ A 🡒 B) (hAC : M ⊨ A 🡒 C) : M ⊨ A 🡒 (B ⋏ C) := by
  intro x y Rxy hya;
  have := hAB M.root y (by grind) hya;
  have := hAC M.root y (by grind) hya;
  grind;

@[grind <=]
lemma modelValid_ruleD (hAC : M ⊨ A 🡒 C) (hBC : M ⊨ B 🡒 C) : M ⊨ (A ⋎ B) 🡒 C := by
  rintro x y Rxy (h | h);
  . exact hAC M.root y (by grind) h;
  . exact hBC M.root y (by grind) h;

@[grind =>]
lemma modelValid_mdp (hAB : M ⊨ A 🡒 B) (hA : M ⊨ A) : M ⊨ B := by
  intro x;
  exact hAB M.root x (show M.root ≺[A 🡒 B] x by grind) (by grind);

@[grind <=]
lemma modelValid_af (hA : M ⊨ A) : M ⊨ B 🡒 A := by grind;

theorem soundness_model : (Λ ⊢ⱽ A) → (∀ {κ}, ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A) := by
  intro h _ M hM; induction h <;> grind;



@[simp, grind .]
theorem consistency_of_VF : (∅ ⊬ (⊥ : Formula α)) := by
  by_contra!;
  let F : Frame (Fin 1) α := {
    Rel' := λ _ _ _ => True,
    root' := 1,
    root_rooted' := by grind;
  };
  simpa using soundness_frame this F (by grind);

example : (∅ ⊬ (⊤ 🡒 (#0 ⋏ #1) 🡘 (⊤ 🡒 (#1 ⋏ #0)))) := by
  by_contra!;
  let M : Model (Fin 3) ℕ := {
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
  have : (0 : M.World) ⊩ (⊤ 🡒 (#0 ⋏ #1) 🡘 (⊤ 🡒 (#1 ⋏ #0))) := soundness_model this M (by grind) 0;
  have : (2 : M.World) ⊩ #1 := @this.1 1 (by grind) (by grind) 2 (by grind) (by grind) |>.1;
  contradiction;

end Soundness


section

@[grind]
def FrameForces {F : Frame κ α} (x : F.World) (A : Formula α) (A_closed : A.Closed := by grind) : Prop :=
  match A with
  | ⊥ => False
  | A ⋏ B => FrameForces x A ∧ FrameForces x B
  | A ⋎ B => FrameForces x A ∨ FrameForces x B
  | A 🡒 B => ∀ {y}, F.Rel (A 🡒 B) x y → (FrameForces y A → FrameForces y B)

variable {F : Frame κ α}

@[simp, grind .]
lemma frameForces_top : FrameForces x (⊤ : Formula α) := by grind;

@[grind =_]
lemma iff_FrameForces_Forces_of_closed {F : Frame κ α} {x : F.World} {V} {A} (A_closed : A.Closed) : FrameForces x A ↔ (Forces (M := ⟨F, V⟩) x A) := by
  induction A generalizing x <;> grind;

lemma iff_forces_of_closed {x : F.World} (A_closed : A.Closed) : (Forces (M := ⟨F, V⟩) x A) ↔ (Forces (M := ⟨F, V'⟩) x A) := by
  simp [←iff_FrameForces_Forces_of_closed A_closed];

lemma iff_FrameValid_ModelValid_of_closed {M : Model κ α} (A_closed : A.Closed) : (M.toFrame ⊨ A) ↔ (M ⊨ A) := by
  constructor;
  . intro h x;
    apply h;
  . intro h V x;
    exact iff_forces_of_closed A_closed |>.mpr (@h x);

lemma iff_FrameValid_neg_of_closed (A_closed : A.Closed) : F ⊨ (∼A) ↔ ∀ x : F.World, ¬(FrameForces x A) := by
  constructor;
  . intro h x;
    by_contra!
    exact h (λ _ _ => True) F.root x (by grind) $ iff_FrameForces_Forces_of_closed (by grind) |>.mp this;
  . intro h V x;
    grind;

@[grind =_]
lemma iff_frameValid_not_or : F ⊨ ∼(A ⋎ B) ↔ (F ⊨ ∼A ∧ F ⊨ ∼B) := by grind;

lemma iff_frameValid_closed_imp (A_closed : A.Closed) (B_closed : B.Closed)
  : F ⊨ ∼(A 🡒 B) ↔ (∀ x : F.World, ∃ y : F.World, x ≺[A 🡒 B] y ∧ (FrameForces y A ∧ ¬FrameForces y B)) := by
  apply Iff.trans (iff_FrameValid_neg_of_closed (A := A 🡒 B) (by grind));
  simp [FrameForces];

lemma iff_frameValid_closed_dn (A_closed : A.Closed) : F ⊨ ∼∼A ↔ (∀ x : F.World, ∃ y : F.World, x ≺[∼A] y ∧ (FrameForces y A)) := by
  apply Iff.trans (iff_frameValid_closed_imp (A := A) (B := ⊥) (by grind) (by grind));
  simp [FrameForces];

end

end FMTSemantics
