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


namespace NR.ProvableHilbert

variable {𝔸 : Axioms α} {A C : Formula α}

lemma bot_of_provable_provable_complement (hA : ⊢ʰ[NR;𝔸] A) (hCA : ⊢ʰ[NR;𝔸] A.complement) : ⊢ʰ[NR;𝔸] ⊥ := by
  match A with
  | ∼_ => exact mdp hA hCA;
  | ⊥ | #_  | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact mdp hCA hA;

lemma ctx_bot_of_provable_provable_complement (hA : ⊢ʰ[NR;𝔸] C 🡒 A) (hCA : ⊢ʰ[NR;𝔸] C 🡒 A.complement) : ⊢ʰ[NR;𝔸] C 🡒 ⊥ := by
  match A with
  | ∼_ => exact ctx_mdp hA hCA;
  | ⊥ | #_  | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact ctx_mdp hCA hA;

lemma complementDneRule (h : ⊢ʰ[NR;𝔸] ∼A.complement) : ⊢ʰ[NR;𝔸] A := by
  match A with
  | ∼A => exact h;
  | ⊥ | #_ | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact dneRule h;

end NR.ProvableHilbert


namespace NR.FinitelyDerivableHilbert

variable {𝔸 : Axioms α} {X : Finset (Formula α)} {A C : Formula α}

lemma complement_lem_elim (hA : X ⊢ʰ[NR;𝔸] A 🡒 C) (hB : X ⊢ʰ[NR;𝔸] A.complement 🡒 C) : X ⊢ʰ[NR;𝔸] C := by
  match A with
  | ∼_ => exact NR.FinitelyDerivableHilbert.lem_elim hB hA;
  | ⊥ | #_ | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
    => exact NR.FinitelyDerivableHilbert.lem_elim hA hB;

end NR.FinitelyDerivableHilbert


namespace FMT

variable [DecidableEq α] {𝔸 : Axioms α} {A B C : Formula α}

namespace ScopeSet

variable {X : ScopeSet 𝔸 A}

def ConsistentNR (X : ScopeSet 𝔸 A) := ⊬ʰ[NR;𝔸] ∼⋀(X.image (·.1))

lemma iff_inconsistentNR {X : ScopeSet 𝔸 A} : ¬ConsistentNR X ↔ ⊢ʰ[NR;𝔸] ∼⋀(X.image (·.1)) := by
  dsimp [ConsistentNR];
  tauto;

lemma either_consistentNR_of_consistentNR (hX : ConsistentNR X) (B : ScopeOf 𝔸 A)
  : ConsistentNR (insert B X) ∨ ConsistentNR (insert B.complement X) := by
  contrapose! hX;
  obtain ⟨h₁, h₂⟩ := hX;
  let Y := X.image (·.1);
  have h₁ : Y ⊢ʰ[NR;𝔸] B.1 🡒 ⊥ := NR.FinitelyDerivableHilbert.from_ctx $ (show (insert B X).image (·.1) = (insert B.1 Y) by simp [Y]) ▸ iff_inconsistentNR.mp h₁;
  have h₂ : Y ⊢ʰ[NR;𝔸] B.complement.1 🡒 ⊥ := NR.FinitelyDerivableHilbert.from_ctx $ (show (insert B.complement X).image (·.1) = (insert B.complement.1 Y) by simp [Y]) ▸ iff_inconsistentNR.mp h₂;
  apply iff_inconsistentNR.mpr;
  exact NR.FinitelyDerivableHilbert.complement_lem_elim h₁ h₂;

end ScopeSet


structure MaximalConsistentScopeSetNR (𝔸 : Axioms α) (A : Formula α) where
  carrier : ScopeSet 𝔸 A
  consistent : carrier.ConsistentNR
  maximal : carrier.Maximal

namespace MaximalConsistentScopeSetNR

attribute [simp, grind .] MaximalConsistentScopeSetNR.consistent MaximalConsistentScopeSetNR.maximal

variable {S : MaximalConsistentScopeSetNR 𝔸 A}

@[grind =]
lemma iff_mem_notMem_complement {B : ScopeOf 𝔸 A} : B ∈ S.1.1 ↔ B.complement ∉ S.1.1 := by
  constructor;
  . intro h hc;
    apply S.consistent;
    apply NR.ProvableHilbert.ctx_bot_of_provable_provable_complement (A := B) <;>
    . apply NR.ProvableHilbert.fconjElim;
      grind;
  . grind [S.maximal B];

@[grind =]
lemma iff_mem_complement_notMem {B : ScopeOf 𝔸 A} : B.complement ∈ S.1.1 ↔ B ∉ S.1.1 := by
  constructor;
  . intro h hc;
    apply S.consistent;
    apply NR.ProvableHilbert.ctx_bot_of_provable_provable_complement (A := B) <;>
    . apply NR.ProvableHilbert.fconjElim;
      grind;
  . grind [S.maximal B];

lemma iff_mem_provable {B : ScopeOf 𝔸 A} : B ∈ S.1.1 ↔ ⊢ʰ[NR;𝔸] ⋀(S.1.image (·.1)) 🡒 B := by
  constructor;
  . intro hB;
    apply NR.ProvableHilbert.fconjElim (by simpa);
  . intro hB;
    have : ⊬ʰ[NR;𝔸] ⋀(S.1.image (·.1)) 🡒 ⊥ := S.consistent;
    contrapose! this;
    apply NR.ProvableHilbert.ctx_bot_of_provable_provable_complement;
    . exact hB;
    . apply NR.ProvableHilbert.fconjElim;
      grind;

lemma mem_of_provable {B : ScopeOf 𝔸 A} : (⊢ʰ[NR;𝔸] B.1) → B ∈ S.1.1 := by
  intro hB;
  apply iff_mem_provable.mpr;
  apply NR.ProvableHilbert.af hB;

@[simp, grind .]
lemma not_mem_bot : ⟨(⊥ : Formula α), by grind⟩ ∉ S.1.1 := iff_mem_provable.not.mpr S.consistent

lemma mem_mdp (_ : B 🡒 C ∈ scope 𝔸 A) : ⟨B 🡒 C, by grind⟩ ∈ S.1.1 → ⟨B, by grind⟩ ∈ S.1.1 → ⟨C, by grind⟩ ∈ S.1.1 := by
  intro hBC hB;
  replace hBC := iff_mem_provable.mp hBC;
  replace hB := iff_mem_provable.mp hB;
  exact iff_mem_provable.mpr $ NR.ProvableHilbert.ctx_mdp hBC hB;

lemma mem_af (_ : C 🡒 B ∈ scope 𝔸 A) : ⟨B, by grind⟩ ∈ S.1.1 → ⟨C 🡒 B, by grind⟩ ∈ S.1.1 := by
  intro hB;
  replace hB := iff_mem_provable.mp hB;
  exact iff_mem_provable.mpr $ NR.ProvableHilbert.ctx_af hB;

open Classical in
lemma imp_t (_ : (B 🡒 C) ∈ scope 𝔸 A) : ⟨B 🡒 C, by grind⟩ ∈ S.1.1 ↔ (⟨B, by grind⟩ ∈ S.1.1 → (ScopeOf.complement ⟨C, by grind⟩) ∉ S.1.1) := by
  constructor;
  . intro hBC hB;
    apply iff_mem_notMem_complement.mp;
    exact mem_mdp (by grind) hBC hB;
  . intro h;
    replace h := not_or_of_imp h;
    rcases h with (hB | hC);
    . replace hB := iff_mem_complement_notMem.mpr hB;
      match B with
      | ∼_ =>
        apply iff_mem_provable.mpr;
        apply NR.ProvableHilbert.ctx_nc $ iff_mem_provable.mp hB;
      | ⊥ | #_ | □_
      | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
        =>
        apply iff_mem_provable.mpr;
        apply NR.ProvableHilbert.ctx_nc2 $ iff_mem_provable.mp hB;
    . apply mem_af ‹_›;
      exact iff_mem_notMem_complement.mpr hC;

instance : Finite (MaximalConsistentScopeSetNR 𝔸 A) :=
  Finite.of_injective (fun S : MaximalConsistentScopeSetNR 𝔸 A => S.carrier) <| by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl

namespace lindenbaum

open Classical

noncomputable def next (X : ScopeSet 𝔸 A) (B : ScopeOf 𝔸 A) : ScopeSet 𝔸 A :=
  if ScopeSet.ConsistentNR (insert B X) then (insert B X) else insert (⟨B.1.complement, by grind⟩) X

variable {S : ScopeSet 𝔸 A} {B : ScopeOf 𝔸 A}

lemma next_mem_self : B ∈ next S B ∨ B.complement ∈ next S B := by
  unfold next;
  grind;

lemma next_consistent (hS : S.ConsistentNR) : ScopeSet.ConsistentNR (next S B) := by
  unfold next;
  grind [ScopeSet.either_consistentNR_of_consistentNR hS B];

lemma next_subset : S ⊆ (next S B) := by
  unfold next;
  split <;> simp;


noncomputable def enum (S : ScopeSet 𝔸 A) : List (ScopeOf 𝔸 A) → ScopeSet 𝔸 A
  | [] => S
  | B :: X => next (enum S X) B

variable {X : List (ScopeOf 𝔸 A)}

lemma enum_consistent (hS : S.ConsistentNR) : ScopeSet.ConsistentNR (enum S X) := by
  induction X with
  | nil => exact hS
  | cons B X ih => exact next_consistent $ ih;

lemma enum_subset : S ⊆ (enum S X) := by
  induction X with
  | nil => trivial;
  | cons B X ih =>
    trans (enum S X);
    . exact ih;
    . exact next_subset;

lemma enum_of_mem (hB : B ∈ X) : B ∈ (enum S X) ∨ B.complement ∈ (enum S X) := by
  induction X with
  | nil => contradiction;
  | cons C X ih =>
    simp only [List.mem_cons] at hB;
    unfold enum;
    rcases hB with (rfl | hB);
    . exact next_mem_self;
    . grind [next_subset];

end lindenbaum

noncomputable def lindenbaum (S : ScopeSet 𝔸 A) (S_consis : S.ConsistentNR) : MaximalConsistentScopeSetNR 𝔸 A where
  carrier := lindenbaum.enum S (Finset.univ.toList)
  consistent := lindenbaum.enum_consistent S_consis
  maximal := by
    intro B;
    apply lindenbaum.enum_of_mem;
    simp;

variable {S : ScopeSet 𝔸 A}

@[simp, grind .]
lemma lindenbaum_subset : S ⊆ (lindenbaum S S_consis).1 := lindenbaum.enum_subset

end MaximalConsistentScopeSetNR


noncomputable def countermodelRos (𝔸 : Axioms α) (A : Formula α) [Fact (⊬ʰ[NR;𝔸] ⊥)] : Model (MaximalConsistentScopeSetNR 𝔸 A) α where
  Rel' B S T :=
    match B with
    | □C => (_ : □C ∈ scope 𝔸 A) → ⟨□C, by grind⟩ ∈ S.1.1 → ⟨C, by grind⟩ ∈ T.1.1
    | _  => True
  Val a S := (_ : #a ∈ scope 𝔸 A) → ⟨#a, by grind⟩ ∈ S.1.1
  root' := MaximalConsistentScopeSetNR.lindenbaum ∅ $ by
    suffices ⊬ʰ[NR;𝔸] ⊥ by
      contrapose! this;
      replace : ⊢ʰ[NR;𝔸] ∼∼⊥ := by simpa using ScopeSet.iff_inconsistentNR.mp this;
      exact NR.ProvableHilbert.dneRule $ this;
    apply Fact.elim inferInstance;

variable [Fact (⊬ʰ[NR;𝔸] ⊥)]

open MaximalConsistentScopeSetNR in
instance : (countermodelRos 𝔸 A).Serial := by
  constructor;
  intro S C;
  by_cases hC : ∃ h : □C ∈ scope 𝔸 A, ⟨□C, h⟩ ∈ S.1.1;
  . obtain ⟨hC, hCS⟩ := hC;
    use lindenbaum {⟨C, by grind⟩} $ by
      suffices ⊬ʰ[NR;𝔸] ∼C by simpa [ScopeSet.ConsistentNR];
      intro h;
      apply S.consistent;
      apply NR.ProvableHilbert.ctx_bot_of_provable_provable_complement (A := □C);
      . exact iff_mem_provable.mp hCS;
      . exact NR.ProvableHilbert.af $ NR.ProvableHilbert.ros h;
    intro _ _;
    apply lindenbaum_subset;
    simp;
  . use S;
    intro h hmem;
    exact absurd ⟨h, hmem⟩ hC;

lemma countermodelRos.truthlemma {S : (countermodelRos 𝔸 A).World} (B : ScopeOf 𝔸 A) : B ∈ S.1.1 ↔ S ⊩ B := by
  obtain ⟨B, hB⟩ := B;
  induction B generalizing S with
  | bot => grind;
  | atom a => tauto;
  | imp B C ihB ihC =>
    replace ihB := @ihB S (by grind);
    replace ihC := @ihC S (by grind);
    constructor;
    . intro hBC hB;
      apply ihC.mp;
      replace hB := ihB.mpr hB;
      exact MaximalConsistentScopeSetNR.mem_mdp ‹_› hBC hB;
    . intro h;
      rcases imp_iff_not_or.mp h with hB | hC;
      . apply MaximalConsistentScopeSetNR.imp_t ‹_› |>.mpr;
        intro hB;
        replace hB := ihB.mp hB;
        contradiction;
      . exact MaximalConsistentScopeSetNR.mem_af ‹_› $ ihC.mpr hC;
  | box B ihB =>
    constructor
    · intro hbox T RST;
      exact ihB (by grind) |>.mp $ RST hB hbox;
    · contrapose!;
      intro h;
      apply notForces_box.mpr;
      use MaximalConsistentScopeSetNR.lindenbaum {⟨B.complement, by grind⟩} $ by
        suffices ⊬ʰ[NR;𝔸] ∼(B.complement) by simpa [ScopeSet.ConsistentNR];
        contrapose! h;
        apply MaximalConsistentScopeSetNR.iff_mem_provable.mpr;
        apply NR.ProvableHilbert.af;
        exact NR.ProvableHilbert.nec $ NR.ProvableHilbert.complementDneRule h;
      constructor;
      . tauto;
      . apply ihB (by grind) |>.not.mp;
        apply MaximalConsistentScopeSetNR.iff_mem_complement_notMem.mp;
        apply MaximalConsistentScopeSetNR.lindenbaum_subset;
        simp;

lemma countermodelRos.valid_axioms : ∀ B ∈ 𝔸, (countermodelRos 𝔸 A) ⊨ B := by
  intro B hB X;
  apply countermodelRos.truthlemma (B := ⟨B, by grind⟩) |>.mp;
  apply MaximalConsistentScopeSetNR.iff_mem_provable.mpr;
  exact NR.ProvableHilbert.af $ NR.ProvableHilbert.axm hB;

omit [Fact (⊬ʰ[NR;𝔸] ⊥)] in
open MaximalConsistentScopeSetNR in
theorem finite_model_property_ros : (∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, M.Serial → (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A) → ⊢ʰ[NR;𝔸] A := by
  contrapose;
  intro h;
  have : Fact (⊬ʰ[NR;𝔸] ⊥) := ⟨NR.ProvableHilbert.consistent_of_unprovable h⟩
  push Not;
  use (MaximalConsistentScopeSetNR 𝔸 A), inferInstance, countermodelRos 𝔸 A, inferInstance;
  constructor;
  . exact countermodelRos.valid_axioms;
  . apply iff_Valid_exists_world_not_Forces.mpr;
    use MaximalConsistentScopeSetNR.lindenbaum (𝔸 := 𝔸) (A := A) {⟨A.complement, by grind⟩} $ by
      suffices ⊬ʰ[NR;𝔸] ∼(A.complement) by simpa [ScopeSet.ConsistentNR]
      contrapose! h;
      exact NR.ProvableHilbert.complementDneRule h;
    apply countermodelRos.truthlemma (B := ⟨A, by grind⟩) |>.not.mp;
    apply iff_mem_complement_notMem.mp;
    apply lindenbaum_subset;
    simp;

omit [Fact (⊬ʰ[NR;𝔸] ⊥)] in
theorem result_model_ros : List.TFAE [
  ⊢ʰ[NR;𝔸] A,
  ∀ {κ : Type u}, ∀ M : Model κ α, M.Serial → (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, M.Serial → (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _ M hS hM; haveI := hS; exact soundness_model_ros hM h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_model_property_ros;
  tfae_finish;

theorem NR_completeness {A : Formula α} : List.TFAE [
  ⊢ʰ[NR;∅] A,
  ∀ {κ : Type u}, ∀ F : Frame κ α, F.Serial → F ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, F.Serial → F ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _ F hS; haveI := hS; exact soundness_frame_ros (by simp) h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := by
    intro h;
    apply finite_model_property_ros (𝔸 := ∅);
    intro κ _ M hS _;
    haveI := hS;
    exact h M.toFrame inferInstance M.Val;
  tfae_finish;

end FMT

end Modal

end
