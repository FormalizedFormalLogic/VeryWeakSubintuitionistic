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


namespace N.ProvableHilbert

variable {𝔸 : Axioms α} {A : Formula α}

lemma bot_of_provable_provable_complement (hA : ⊢ʰ[N;𝔸] A) (hCA : ⊢ʰ[N;𝔸] A.complement) : ⊢ʰ[N;𝔸] ⊥ := by
  match A with
  | ∼_ => exact mdp hA hCA;
  | ⊥ | #_  | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact mdp hCA hA;

lemma ctx_bot_of_provable_provable_complement (hA : ⊢ʰ[N;𝔸] C 🡒 A) (hCA : ⊢ʰ[N;𝔸] C 🡒 A.complement) : ⊢ʰ[N;𝔸] C 🡒 ⊥ := by
  match A with
  | ∼_ => exact ctx_mdp hA hCA;
  | ⊥ | #_  | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact ctx_mdp hCA hA;

lemma complementDneRule (h :  ⊢ʰ[N;𝔸] ∼A.complement) : ⊢ʰ[N;𝔸] A := by
  match A with
  | ∼A => exact h;
  | ⊥ | #_ | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
  => exact dneRule h;

end N.ProvableHilbert


namespace N.FinitelyDerivableHilbert

variable {𝔸 : Axioms α} {X : Finset (Formula α)} {A B C : Formula α}

lemma complement_lem_elim (hA : X ⊢ʰ[N;𝔸] A 🡒 C) (hB : X ⊢ʰ[N;𝔸] A.complement 🡒 C) : X ⊢ʰ[N;𝔸] C := by
  match A with
  | ∼_ => exact N.FinitelyDerivableHilbert.lem_elim hB hA;
  | ⊥ | #_ | □_
  | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
    => exact N.FinitelyDerivableHilbert.lem_elim hA hB;

end N.FinitelyDerivableHilbert


namespace FMT

variable [DecidableEq α] {𝔸 : Axioms α} {A B C : Formula α}

@[grind]
def scope.core (𝔸 : Axioms α) (A : Formula α) : Finset (Formula α) := insert (⊥) (A.subfmls ∪ 𝔸.biUnion (·.subfmls))

@[grind]
def scope (𝔸 : Axioms α) (A : Formula α) : Finset (Formula α) := (scope.core 𝔸 A) ∪ (scope.core 𝔸 A).image (∼·)

namespace scope

@[simp, grind =]
lemma mem_core_iff : B ∈ scope.core 𝔸 A ↔ B = ⊥ ∨ B ∈ A.subfmls ∨ ∃ D ∈ 𝔸, B ∈ D.subfmls := by grind;

@[simp, grind .]
lemma core_subset_scope : core 𝔸 A ⊆ scope 𝔸 A := Finset.subset_union_left

@[simp, grind <=]
lemma neg_mem_of_mem_core {B} (hB : B ∈ core 𝔸 A) : ∼B ∈ scope 𝔸 A := by grind;

@[simp, grind <=]
lemma core_subfmls_closed (hB : B ∈ core 𝔸 A) (hC : C ∈ B.subfmls) : C ∈ core 𝔸 A := by grind;

@[simp, grind .]
lemma mem_bot : (⊥ : Formula α) ∈ scope 𝔸 A := by grind;

@[simp, grind .]
lemma mem_self : A ∈ scope 𝔸 A := by grind;

@[simp, grind <=]
lemma mem_axiom (hB : B ∈ 𝔸) : B ∈ scope 𝔸 A := by grind;

@[grind <=]
lemma subfmls_closed (hB : B ∈ scope 𝔸 A) (hC : C ∈ B.subfmls) : C ∈ scope 𝔸 A := by grind;

@[grind <=]
lemma complement_closed (hB : B ∈ scope 𝔸 A) : B.complement ∈ scope 𝔸 A := by
  simp only [scope, Finset.mem_union] at hB;
  rcases hB with hB | hB
  · match B, hB with
    | ∼B, hB => show B ∈ scope 𝔸 A; grind;
    | ⊥, hB | (□_), hB | (#_), hB
    | (_ 🡒 #_), hB | (_ 🡒 (_ 🡒 _)), hB | (_ 🡒 □_), hB
      => exact neg_mem_of_mem_core hB;
  · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB;
    show D ∈ scope 𝔸 A;
    grind;

end scope


abbrev ScopeOf (𝔸 : Axioms α) (A : Formula α) := { B : Formula α // B ∈ scope 𝔸 A }

abbrev ScopeOf.complement (B : ScopeOf 𝔸 A) : ScopeOf 𝔸 A := ⟨B.1.complement, by grind⟩

abbrev ScopeSet (𝔸 : Axioms α) (A : Formula α) := Finset (ScopeOf 𝔸 A)

namespace ScopeSet

variable {𝔸 : Axioms α} {A B C : Formula α}

def Consistent (X : ScopeSet 𝔸 A) := ⊬ʰ[N;𝔸] ∼⋀(X.image (·.1))

lemma iff_inconsistent {X : ScopeSet 𝔸 A} : ¬Consistent X ↔ ⊢ʰ[N;𝔸] ∼⋀(X.image (·.1)) := by
  dsimp [Consistent];
  tauto;

variable {X : ScopeSet 𝔸 A}

lemma either_consistent_of_consistent (hX : Consistent X) (B : ScopeOf 𝔸 A)
  : Consistent (insert B X) ∨ Consistent (insert B.complement X)  := by
  contrapose! hX;
  obtain ⟨h₁, h₂⟩ := hX;
  let Y := X.image (·.1);
  have h₁ : Y ⊢ʰ[N;𝔸] B.1 🡒 ⊥ := N.FinitelyDerivableHilbert.from_ctx $ (show (insert B X).image (·.1) = (insert B.1 Y) by simp [Y]) ▸ iff_inconsistent.mp h₁;
  have h₂ : Y ⊢ʰ[N;𝔸] B.complement.1 🡒 ⊥ := N.FinitelyDerivableHilbert.from_ctx $ (show (insert B.complement X).image (·.1) = (insert B.complement.1 Y) by simp [Y]) ▸ iff_inconsistent.mp h₂;
  apply iff_inconsistent.mpr;
  exact N.FinitelyDerivableHilbert.complement_lem_elim h₁ h₂;

def Maximal (X : ScopeSet 𝔸 A) := ∀ B : ScopeOf 𝔸 A, B ∈ X.1 ∨ B.complement ∈ X.1

variable (X : ScopeSet 𝔸 A)

end ScopeSet


structure MaximalConsistentScopeSet (𝔸 : Axioms α) (A : Formula α) where
  carrier : ScopeSet 𝔸 A
  consistent : carrier.Consistent
  maximal : carrier.Maximal

namespace MaximalConsistentScopeSet

attribute [simp, grind .] MaximalConsistentScopeSet.consistent MaximalConsistentScopeSet.maximal

variable {S : MaximalConsistentScopeSet 𝔸 A} -- {B C : Formula α}

@[grind =]
lemma iff_mem_notMem_complement {B : ScopeOf 𝔸 A} : B ∈ S.1.1 ↔ B.complement ∉ S.1.1 := by
  constructor;
  . intro h hc;
    apply S.consistent;
    apply N.ProvableHilbert.ctx_bot_of_provable_provable_complement (A := B) <;>
    . apply N.ProvableHilbert.fconjElim;
      grind;
  . grind [S.maximal B];

@[grind =]
lemma iff_mem_complement_notMem {B : ScopeOf 𝔸 A} : B.complement ∈ S.1.1 ↔ B ∉ S.1.1 := by
  constructor;
  . intro h hc;
    apply S.consistent;
    apply N.ProvableHilbert.ctx_bot_of_provable_provable_complement (A := B) <;>
    . apply N.ProvableHilbert.fconjElim;
      grind;
  . grind [S.maximal B];

lemma iff_mem_provable {B : ScopeOf 𝔸 A} : B ∈ S.1.1 ↔ ⊢ʰ[N;𝔸] ⋀(S.1.image (·.1)) 🡒 B := by
  constructor;
  . intro hB;
    apply N.ProvableHilbert.fconjElim (by simpa);
  . intro hB;
    have : ⊬ʰ[N;𝔸] ⋀(S.1.image (·.1)) 🡒 ⊥ := S.consistent;
    contrapose! this;
    apply N.ProvableHilbert.ctx_bot_of_provable_provable_complement;
    . exact hB;
    . apply N.ProvableHilbert.fconjElim;
      grind;

lemma mem_of_provable {B : ScopeOf 𝔸 A} : (⊢ʰ[N;𝔸] B.1) → B ∈ S.1.1 := by
  intro hB;
  apply iff_mem_provable.mpr;
  apply N.ProvableHilbert.af hB;

@[simp, grind .]
lemma not_mem_bot : ⟨(⊥ : Formula α), by grind⟩ ∉ S.1.1 := iff_mem_provable.not.mpr S.consistent

lemma mem_mdp (_ : B 🡒 C ∈ scope 𝔸 A) : ⟨B 🡒 C, by grind⟩ ∈ S.1.1 → ⟨B, by grind⟩ ∈ S.1.1 → ⟨C, by grind⟩ ∈ S.1.1 := by
  intro hBC hB;
  replace hBC := iff_mem_provable.mp hBC;
  replace hB := iff_mem_provable.mp hB;
  exact iff_mem_provable.mpr $ N.ProvableHilbert.ctx_mdp hBC hB;

lemma mem_af (_ : C 🡒 B ∈ scope 𝔸 A) : ⟨B, by grind⟩ ∈ S.1.1 → ⟨C 🡒 B, by grind⟩ ∈ S.1.1 := by
  intro hB;
  replace hB := iff_mem_provable.mp hB;
  exact iff_mem_provable.mpr $ N.ProvableHilbert.ctx_af hB;

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
        apply N.ProvableHilbert.ctx_nc $ iff_mem_provable.mp hB;
      | ⊥ | #_ | □_
      | _ 🡒 #_ | _ 🡒 (_ 🡒 _) | _ 🡒 □_
        =>
        apply iff_mem_provable.mpr;
        apply N.ProvableHilbert.ctx_nc2 $ iff_mem_provable.mp hB;
    . apply mem_af ‹_›;
      exact iff_mem_notMem_complement.mpr hC;

instance : Finite (MaximalConsistentScopeSet 𝔸 A) :=
  Finite.of_injective (fun S : MaximalConsistentScopeSet 𝔸 A => S.carrier) <| by
    rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl

namespace lindenbaum

open Classical

noncomputable def next (X : ScopeSet 𝔸 A) (B : ScopeOf 𝔸 A) : ScopeSet 𝔸 A :=
  if ScopeSet.Consistent (insert B X) then (insert B X) else insert (⟨B.1.complement, by grind⟩) X

variable {S : ScopeSet 𝔸 A} {B : ScopeOf 𝔸 A}

lemma next_mem_self : B ∈ next S B ∨ B.complement ∈ next S B := by
  unfold next;
  grind;

lemma next_consistent (hS : S.Consistent) : ScopeSet.Consistent (next S B) := by
  unfold next;
  grind [ScopeSet.either_consistent_of_consistent hS B];

lemma next_subset : S ⊆ (next S B) := by
  unfold next;
  split <;> simp;


noncomputable def enum (S : ScopeSet 𝔸 A) : List (ScopeOf 𝔸 A) → ScopeSet 𝔸 A
  | [] => S
  | B :: X => next (enum S X) B

variable {X : List (ScopeOf 𝔸 A)}

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

noncomputable def lindenbaum (S : ScopeSet 𝔸 A) (S_consis : S.Consistent) : MaximalConsistentScopeSet 𝔸 A where
  carrier := lindenbaum.enum S (Finset.univ.toList)
  consistent := lindenbaum.enum_consistent S_consis
  maximal := by
    intro B;
    apply lindenbaum.enum_of_mem;
    simp;

variable {S : ScopeSet 𝔸 A}

@[simp, grind .]
lemma lindenbaum_subset : S ⊆ (lindenbaum S S_consis).1 := lindenbaum.enum_subset

end MaximalConsistentScopeSet


noncomputable def countermodel (𝔸 : Axioms α) (A : Formula α) [Fact (⊬ʰ[N;𝔸] ⊥)] : Model (MaximalConsistentScopeSet 𝔸 A) α where
  Rel' B S T :=
    match B with
    | □C => (_ : □C ∈ scope 𝔸 A) → ⟨□C, by grind⟩ ∈ S.1.1 → ⟨C, by grind⟩ ∈ T.1.1
    | _  => True
  Val a S := (_ : #a ∈ scope 𝔸 A) → ⟨#a, by grind⟩ ∈ S.1.1
  root' := MaximalConsistentScopeSet.lindenbaum ∅ $ by
    suffices ⊬ʰ[N;𝔸] ⊥ by
      contrapose! this;
      replace : ⊢ʰ[N;𝔸] ∼∼⊥ := by simpa using ScopeSet.iff_inconsistent.mp this;
      exact N.ProvableHilbert.dneRule $ this;
    apply Fact.elim inferInstance;

variable [Fact (⊬ʰ[N;𝔸] ⊥)] in
lemma countermodel.truthlemma {S : (countermodel 𝔸 A).World} (B : ScopeOf 𝔸 A) : B ∈ S.1.1 ↔ S ⊩ B := by
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
        suffices ⊬ʰ[N;𝔸] ∼(B.complement) by simpa [ScopeSet.Consistent];
        contrapose! h;
        apply MaximalConsistentScopeSet.iff_mem_provable.mpr;
        apply N.ProvableHilbert.af;
        exact N.ProvableHilbert.nec $ N.ProvableHilbert.complementDneRule h;
      constructor;
      . tauto;
      . apply ihB (by grind) |>.not.mp;
        apply MaximalConsistentScopeSet.iff_mem_complement_notMem.mp;
        apply MaximalConsistentScopeSet.lindenbaum_subset;
        simp;

variable [Fact (⊬ʰ[N;𝔸] ⊥)] in
lemma countermodel.valid_axioms : ∀ B ∈ 𝔸, (countermodel 𝔸 A) ⊨ B := by
  intro B hB X;
  apply countermodel.truthlemma (B := ⟨B, by grind⟩) |>.mp;
  apply MaximalConsistentScopeSet.iff_mem_provable.mpr;
  exact N.ProvableHilbert.af $ N.ProvableHilbert.axm hB;

open MaximalConsistentScopeSet in
theorem finite_model_property : (∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A) → ⊢ʰ[N;𝔸] A := by
  contrapose;
  intro h;
  have : Fact (⊬ʰ[N;𝔸] ⊥) := ⟨N.ProvableHilbert.consistent_of_unprovable h⟩
  push Not;
  use (MaximalConsistentScopeSet 𝔸 A), inferInstance, countermodel 𝔸 A;
  constructor;
  . exact countermodel.valid_axioms;
  . apply iff_Valid_exists_world_not_Forces.mpr;
    use MaximalConsistentScopeSet.lindenbaum (𝔸 := 𝔸) (A := A) {⟨A.complement, by grind⟩} $ by
      suffices ⊬ʰ[N;𝔸] ∼(A.complement) by simpa [ScopeSet.Consistent]
      contrapose! h;
      exact N.ProvableHilbert.complementDneRule h;
    apply countermodel.truthlemma (B := ⟨A, by grind⟩) |>.not.mp;
    apply iff_mem_complement_notMem.mp;
    apply lindenbaum_subset;
    simp;

theorem result_model : List.TFAE [
  ⊢ʰ[N;𝔸] A,
  ∀ {κ : Type u}, ∀ M : Model κ α, (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _; apply soundness_model h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_model_property
  tfae_finish;

end FMT



end Modal
