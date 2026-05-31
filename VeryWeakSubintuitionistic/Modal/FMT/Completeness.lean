module

public import VeryWeakSubintuitionistic.Modal.FMT.Basic

@[expose] public section

namespace Modal

variable {α : Type u}

namespace Formula

def complement : Formula α → Formula α
  | ∼A => A
  | A => ∼A

@[simp] lemma complement_neg (A : Formula α) : (∼A).complement = A := rfl


@[grind]
def subfmls [DecidableEq α] : Formula α → Finset (Formula α)
  | #a => {#a}
  | ⊥  => {⊥}
  | A 🡒 B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
  | □A => insert (□A) A.subfmls

variable {A B C : Formula α} [DecidableEq α]

@[grind .] lemma mem_subfmls_self : A ∈ A.subfmls := by induction A <;> grind;
@[grind! =>] lemma mem_subfmls_of_mem_imp_subfmls : (B 🡒 C) ∈ A.subfmls → B ∈ A.subfmls ∧ C ∈ A.subfmls := by induction A <;> grind;
@[grind! =>] lemma mem_subfmls_of_mem_box_subfmls : (□B) ∈ A.subfmls → B ∈ A.subfmls := by induction A <;> grind;

@[grind! =>]
lemma mem_subfmls_trans : B ∈ A.subfmls → C ∈ B.subfmls → C ∈ A.subfmls := by induction A <;> grind;

lemma subfmls_subset_of_mem (hB : B ∈ A.subfmls) : B.subfmls ⊆ A.subfmls :=
  fun _ hC => mem_subfmls_trans hB hC

end Formula


namespace ProvableN

variable {Λ : Axioms α} {A : Formula α}

lemma bot_of_provable_provable_complement (hA : Λ ⊢ᴺ A) (hCA : Λ ⊢ᴺ A.complement) : Λ ⊢ᴺ ⊥ := by
  match A with
  | ∼_ => exact mdp hA hCA;
  | ⊥ | #_  | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact mdp hCA hA;

lemma ctx_bot_of_provable_provable_complement (hA : Λ ⊢ᴺ C 🡒 A) (hCA : Λ ⊢ᴺ C 🡒 A.complement) : Λ ⊢ᴺ C 🡒 ⊥ := by
  match A with
  | ∼_ => exact ctx_mdp hA hCA;
  | ⊥ | #_  | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact ctx_mdp hCA hA;

lemma complementDneRule (h :  Λ ⊢ᴺ ∼A.complement) : Λ ⊢ᴺ A := by
  match A with
  | ∼A => exact h;
  | ⊥ | #_ | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact dneRule h;

end ProvableN


namespace FinitelyDerivableN

variable [DecidableEq α] {Λ : Axioms α} {X : Finset (Formula α)} {A B C : Formula α}

lemma complement_lem_elim (hA : X ⊢ᴺ[Λ] A 🡒 C) (hB : X ⊢ᴺ[Λ] A.complement 🡒 C) : X ⊢ᴺ[Λ] C := by
  match A with
  | ∼_ => exact FinitelyDerivableN.lem_elim hB hA;
  | ⊥ | #_ | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
    => exact FinitelyDerivableN.lem_elim hA hB;

end FinitelyDerivableN


namespace FMT

variable [DecidableEq α] {Λ : Axioms α} {A B C : Formula α}

@[grind]
def scope.core (Λ : Axioms α) (A : Formula α) : Finset (Formula α) := insert (⊥) (A.subfmls ∪ Λ.biUnion (·.subfmls))

@[grind]
def scope (Λ : Axioms α) (A : Formula α) : Finset (Formula α) := (scope.core Λ A) ∪ (scope.core Λ A).image (∼·)

namespace scope

@[simp, grind =]
lemma mem_core_iff : B ∈ scope.core Λ A ↔ B = ⊥ ∨ B ∈ A.subfmls ∨ ∃ D ∈ Λ, B ∈ D.subfmls := by grind;

@[simp, grind .]
lemma core_subset_scope : core Λ A ⊆ scope Λ A := Finset.subset_union_left

@[simp, grind <=]
lemma neg_mem_of_mem_core {B} (hB : B ∈ core Λ A) : ∼B ∈ scope Λ A := by grind;

@[simp, grind <=]
lemma core_subfmls_closed (hB : B ∈ core Λ A) (hC : C ∈ B.subfmls) : C ∈ core Λ A := by grind;

@[simp, grind .]
lemma mem_bot : (⊥ : Formula α) ∈ scope Λ A := by grind;

@[simp, grind .]
lemma mem_self : A ∈ scope Λ A := by grind;

@[simp, grind <=]
lemma mem_axiom (hB : B ∈ Λ) : B ∈ scope Λ A := by grind;

@[grind <=]
lemma subfmls_closed (hB : B ∈ scope Λ A) (hC : C ∈ B.subfmls) : C ∈ scope Λ A := by grind;

@[grind <=]
lemma complement_closed (hB : B ∈ scope Λ A) : B.complement ∈ scope Λ A := by
  simp only [scope, Finset.mem_union] at hB;
  rcases hB with hB | hB
  · match B, hB with
    | ∼B, hB => show B ∈ scope Λ A; grind;
    | ⊥, hB | (□_), hB | (#_), hB
    | (_ 🡒 #_), hB | (_ 🡒 (_ 🡒 _)), hB | (_ 🡒 □_), hB
      => exact neg_mem_of_mem_core hB;
  · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB;
    show D ∈ scope Λ A;
    grind;

end scope


abbrev ScopeOf (Λ : Axioms α) (A : Formula α) := { B : Formula α // B ∈ scope Λ A }

abbrev ScopeOf.complement (B : ScopeOf Λ A) : ScopeOf Λ A := ⟨B.1.complement, by grind⟩

abbrev ScopeSet (Λ : Axioms α) (A : Formula α) := Finset (ScopeOf Λ A)

namespace ScopeSet

variable {Λ : Axioms α} {A B C : Formula α}

def Consistent (X : ScopeSet Λ A) := Λ ⊬ᴺ ∼⋀(X.image (·.1))

lemma iff_inconsistent {X : ScopeSet Λ A} : ¬Consistent X ↔ Λ ⊢ᴺ ∼⋀(X.image (·.1)) := by
  dsimp [Consistent];
  tauto;

variable {X : ScopeSet Λ A}

lemma either_consistent_of_consistent (hX : Consistent X) (B : ScopeOf Λ A)
  : Consistent (insert B X) ∨ Consistent (insert B.complement X)  := by
  contrapose! hX;
  obtain ⟨h₁, h₂⟩ := hX;
  let Y := X.image (·.1);
  have h₁ : Y ⊢ᴺ[Λ] B.1 🡒 ⊥ := FinitelyDerivableN.from_ctx $ (show (insert B X).image (·.1) = (insert B.1 Y) by simp [Y]) ▸ iff_inconsistent.mp h₁;
  have h₂ : Y ⊢ᴺ[Λ] B.complement.1 🡒 ⊥ := FinitelyDerivableN.from_ctx $ (show (insert B.complement X).image (·.1) = (insert B.complement.1 Y) by simp [Y]) ▸ iff_inconsistent.mp h₂;
  apply iff_inconsistent.mpr;
  exact FinitelyDerivableN.complement_lem_elim h₁ h₂;

def Maximal (X : ScopeSet Λ A) := ∀ B : ScopeOf Λ A, B ∈ X.1 ∨ B.complement ∈ X.1

variable (X : ScopeSet Λ A)

end ScopeSet


structure MaximalConsistentScopeSet (Λ : Axioms α) (A : Formula α) where
  carrier : ScopeSet Λ A
  consistent : carrier.Consistent
  maximal : carrier.Maximal

namespace MaximalConsistentScopeSet

attribute [simp, grind .] MaximalConsistentScopeSet.consistent MaximalConsistentScopeSet.maximal

variable {S : MaximalConsistentScopeSet Λ A} -- {B C : Formula α}

@[grind =]
lemma iff_mem_notMem_complement {B : ScopeOf Λ A} : B ∈ S.1.1 ↔ B.complement ∉ S.1.1 := by
  constructor;
  . intro h hc;
    apply S.consistent;
    apply ProvableN.ctx_bot_of_provable_provable_complement (A := B) <;>
    . apply ProvableN.fconjElim;
      grind;
  . grind [S.maximal B];

@[grind =]
lemma iff_mem_complement_notMem {B : ScopeOf Λ A} : B.complement ∈ S.1.1 ↔ B ∉ S.1.1 := by
  constructor;
  . intro h hc;
    apply S.consistent;
    apply ProvableN.ctx_bot_of_provable_provable_complement (A := B) <;>
    . apply ProvableN.fconjElim;
      grind;
  . grind [S.maximal B];

lemma iff_mem_provable {B : ScopeOf Λ A} : B ∈ S.1.1 ↔ Λ ⊢ᴺ ⋀(S.1.image (·.1)) 🡒 B := by
  constructor;
  . intro hB;
    apply ProvableN.fconjElim (by simpa);
  . intro hB;
    have : Λ ⊬ᴺ ⋀(S.1.image (·.1)) 🡒 ⊥ := S.consistent;
    contrapose! this;
    apply ProvableN.ctx_bot_of_provable_provable_complement;
    . exact hB;
    . apply ProvableN.fconjElim;
      grind;

lemma mem_of_provable {B : ScopeOf Λ A} : (Λ ⊢ᴺ B.1) → B ∈ S.1.1 := by
  intro hB;
  apply iff_mem_provable.mpr;
  apply ProvableN.af hB;

@[simp, grind .]
lemma not_mem_bot : ⟨(⊥ : Formula α), by grind⟩ ∉ S.1.1 := iff_mem_provable.not.mpr S.consistent

lemma mem_mdp (_ : B 🡒 C ∈ scope Λ A) : ⟨B 🡒 C, by grind⟩ ∈ S.1.1 → ⟨B, by grind⟩ ∈ S.1.1 → ⟨C, by grind⟩ ∈ S.1.1 := by
  intro hBC hB;
  replace hBC := iff_mem_provable.mp hBC;
  replace hB := iff_mem_provable.mp hB;
  exact iff_mem_provable.mpr $ ProvableN.ctx_mdp hBC hB;

lemma mem_af (_ : C 🡒 B ∈ scope Λ A) : ⟨B, by grind⟩ ∈ S.1.1 → ⟨C 🡒 B, by grind⟩ ∈ S.1.1 := by
  intro hB;
  replace hB := iff_mem_provable.mp hB;
  exact iff_mem_provable.mpr $ ProvableN.ctx_af hB;

open Classical in
lemma imp_t (_ : (B 🡒 C) ∈ scope Λ A) : ⟨B 🡒 C, by grind⟩ ∈ S.1.1 ↔ (⟨B, by grind⟩ ∈ S.1.1 → (ScopeOf.complement ⟨C, by grind⟩) ∉ S.1.1) := by
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
        apply ProvableN.ctx_nc $ iff_mem_provable.mp hB;
      | ⊥ | #_ | □_
      | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
        =>
        apply iff_mem_provable.mpr;
        apply ProvableN.ctx_nc2 $ iff_mem_provable.mp hB;
    . apply mem_af ‹_›;
      exact iff_mem_notMem_complement.mpr hC;

instance : Finite (MaximalConsistentScopeSet Λ A) :=
  Finite.of_injective (fun S : MaximalConsistentScopeSet Λ A => S.carrier) <| by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl

namespace lindenbaum

open Classical

noncomputable def next (X : ScopeSet Λ A) (B : ScopeOf Λ A) : ScopeSet Λ A :=
  if ScopeSet.Consistent (insert B X) then (insert B X) else insert (⟨B.1.complement, by grind⟩) X

variable {S : ScopeSet Λ A} {B : ScopeOf Λ A}

lemma next_mem_self : B ∈ next S B ∨ B.complement ∈ next S B := by
  unfold next;
  grind;

lemma next_consistent (hS : S.Consistent) : ScopeSet.Consistent (next S B) := by
  unfold next;
  grind [ScopeSet.either_consistent_of_consistent hS B];

lemma next_subset : S ⊆ (next S B) := by
  unfold next;
  split <;> simp;


noncomputable def enum (S : ScopeSet Λ A) : List (ScopeOf Λ A) → ScopeSet Λ A
  | [] => S
  | B :: X => next (enum S X) B

variable {X : List (ScopeOf Λ A)}

lemma enum_consistent (hS : S.Consistent) : ScopeSet.Consistent (enum S X) := by
  induction X with
  | nil => exact hS
  | cons B X ih =>  exact next_consistent $ ih;

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

noncomputable def lindenbaum (S : ScopeSet Λ A) (S_consis : S.Consistent) : MaximalConsistentScopeSet Λ A where
  carrier := lindenbaum.enum S (Finset.univ.toList)
  consistent := lindenbaum.enum_consistent S_consis
  maximal := by
    intro B;
    apply lindenbaum.enum_of_mem;
    simp;

variable {S : ScopeSet Λ A}

@[simp, grind .]
lemma lindenbaum_subset : S ⊆ (lindenbaum S S_consis).1 := lindenbaum.enum_subset

end MaximalConsistentScopeSet


noncomputable def countermodel (Λ : Axioms α) (A : Formula α) [Fact (Λ ⊬ᴺ ⊥)] : Model (MaximalConsistentScopeSet Λ A) α where
  Rel' B S T :=
    match B with
    | □C => (_ : □C ∈ scope Λ A) → ⟨□C, by grind⟩ ∈ S.1.1 → ⟨C, by grind⟩ ∈ T.1.1
    | _  => True
  Val a S := (_ : #a ∈ scope Λ A) → ⟨#a, by grind⟩ ∈ S.1.1
  root' := MaximalConsistentScopeSet.lindenbaum ∅ $ by
    suffices Λ ⊬ᴺ ⊥ by
      contrapose! this;
      replace : Λ ⊢ᴺ ∼∼⊥ := by simpa using ScopeSet.iff_inconsistent.mp this;
      exact ProvableN.dneRule $ this;
    apply Fact.elim inferInstance;

variable [Fact (Λ ⊬ᴺ ⊥)] in
lemma countermodel.truthlemma {S : (countermodel Λ A).World} (B : ScopeOf Λ A) : B ∈ S.1.1 ↔ S ⊩ B := by
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
      exact MaximalConsistentScopeSet.mem_mdp ‹_› hBC hB;
    . intro h;
      rcases imp_iff_not_or.mp h with hB | hC;
      . apply MaximalConsistentScopeSet.imp_t ‹_› |>.mpr;
        intro hB;
        replace hB := ihB.mp hB;
        contradiction;
      . exact MaximalConsistentScopeSet.mem_af ‹_› $ ihC.mpr hC;
  | box B ihB =>
    constructor
    · intro hbox T RST;
      exact ihB (by grind) |>.mp $ RST hB hbox;
    · contrapose!;
      intro h;
      apply notForces_box.mpr;
      use MaximalConsistentScopeSet.lindenbaum {⟨B.complement, by grind⟩} $ by
        suffices Λ ⊬ᴺ ∼(B.complement) by simpa [ScopeSet.Consistent];
        contrapose! h;
        apply MaximalConsistentScopeSet.iff_mem_provable.mpr;
        apply ProvableN.af;
        exact ProvableN.nec $ ProvableN.complementDneRule h;
      constructor;
      . tauto;
      . apply ihB (by grind) |>.not.mp;
        apply MaximalConsistentScopeSet.iff_mem_complement_notMem.mp;
        apply MaximalConsistentScopeSet.lindenbaum_subset;
        simp;

variable [Fact (Λ ⊬ᴺ ⊥)] in
lemma countermodel.valid_axioms : ∀ B ∈ Λ, (countermodel Λ A) ⊨ B := by
  intro B hB X;
  apply countermodel.truthlemma (B := ⟨B, by grind⟩) |>.mp;
  apply MaximalConsistentScopeSet.iff_mem_provable.mpr;
  exact ProvableN.af $ ProvableN.axm hB;

open MaximalConsistentScopeSet in
theorem finite_model_property : (∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A) → Λ ⊢ᴺ A := by
  contrapose;
  intro h;
  have : Fact (Λ ⊬ᴺ ⊥) := ⟨ProvableN.consistent_of_unprovable h⟩
  push Not;
  use (MaximalConsistentScopeSet Λ A), inferInstance, countermodel Λ A;
  constructor;
  . exact countermodel.valid_axioms;
  . apply iff_Valid_exists_world_not_Forces.mpr;
    use MaximalConsistentScopeSet.lindenbaum (Λ := Λ) (A := A) {⟨A.complement, by grind⟩} $ by
      suffices Λ ⊬ᴺ ∼(A.complement) by simpa [ScopeSet.Consistent]
      contrapose! h;
      exact ProvableN.complementDneRule h;
    apply countermodel.truthlemma (B := ⟨A, by grind⟩) |>.not.mp;
    apply iff_mem_complement_notMem.mp;
    apply lindenbaum_subset;
    simp;

theorem result_model : List.TFAE [
  Λ ⊢ᴺ A,
  ∀ {κ : Type u}, ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _; apply soundness_model h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_model_property
  tfae_finish;

end FMT



end Modal
