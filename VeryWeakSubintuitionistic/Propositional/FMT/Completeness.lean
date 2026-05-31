module

public import VeryWeakSubintuitionistic.Propositional.FMT.Basic
public import VeryWeakSubintuitionistic.Propositional.Slash

@[expose] public section

namespace Formula

@[grind]
def subfmls [DecidableEq α] : Formula α → Finset (Formula α)
  | #a => {#a}
  | ⊥  => {⊥}
  | A ⋏ B => insert (A ⋏ B) (A.subfmls ∪ B.subfmls)
  | A ⋎ B => insert (A ⋎ B) (A.subfmls ∪ B.subfmls)
  | A 🡒 B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)

variable {A B C : Formula α} [DecidableEq α]

@[grind .] lemma mem_subfmls_self : A ∈ A.subfmls := by induction A <;> grind;
@[grind! =>] lemma mem_subfmls_of_mem_and_subfmls : (B ⋏ C) ∈ A.subfmls → B ∈ A.subfmls ∧ C ∈ A.subfmls := by induction A <;> grind;
@[grind! =>] lemma mem_subfmls_of_mem_or_subfmls : (B ⋎ C) ∈ A.subfmls → B ∈ A.subfmls ∧ C ∈ A.subfmls := by induction A <;> grind;
@[grind! =>] lemma mem_subfmls_of_mem_imp_subfmls : (B 🡒 C) ∈ A.subfmls → B ∈ A.subfmls ∧ C ∈ A.subfmls := by induction A <;> grind;

end Formula


variable {α : Type u} [DecidableEq α]
variable {Λ : Axioms α} {A : Formula α}

@[grind]
def scope (Λ : Axioms α) (A : Formula α) : Finset (Formula α) :=
  {⊤, ⊥} ∪
  A.subfmls ∪
  Λ.biUnion (·.subfmls)

section

variable {A B C : Formula α}

@[simp, grind .] lemma mem_scope_self : A ∈ scope Λ A := by grind [scope];
@[simp, grind .] lemma mem_scope_top : ⊤ ∈ scope Λ A := by grind [scope];
@[simp, grind .] lemma mem_scope_bot : ⊥ ∈ scope Λ A := by grind [scope];

@[grind =>] lemma mem_scope_of_mem_subfmls (h : B ∈ A.subfmls) : B ∈ scope Λ A := by grind [scope]
@[grind =>] lemma mem_scope_of_mem_axioms_subfmlss (h : B ∈ Λ.biUnion (·.subfmls)) : B ∈ scope Λ A := by grind [scope]
@[grind =>] lemma mem_scope_of_mem_axioms (h : B ∈ Λ) : B ∈ scope Λ A := by grind [scope]

@[grind =>] lemma mem_scope_of_mem_and_scope (h : (B ⋏ C) ∈ scope Λ A) : B ∈ scope Λ A ∧ C ∈ scope Λ A := by grind;
@[grind =>] lemma mem_scope_of_mem_or_scope (h : (B ⋎ C) ∈ scope Λ A) : B ∈ scope Λ A ∧ C ∈ scope Λ A := by grind;
@[grind =>] lemma mem_scope_of_mem_imp_scope (h : (B 🡒 C) ∈ scope Λ A) : B ∈ scope Λ A ∧ C ∈ scope Λ A := by grind;

end


abbrev ScopeOf (Λ : Axioms α) (A : Formula α) := { B // B ∈ (scope Λ A) }

instance : Fintype (Finset (ScopeOf Λ A)) where
  elems := Finset.univ.powerset;
  complete := by grind;


structure Tableau (Λ : Axioms α) (A : Formula α) where
  ant : (Finset (ScopeOf Λ A))
  con : (Finset (ScopeOf Λ A))

instance : Finite (Tableau Λ A) := Finite.of_injective (λ T => (T.ant, T.con)) $ by
  rintro ⟨_, _⟩ ⟨_, _⟩;
  simp;


namespace Tableau

variable {T : Tableau Λ A}

def Inconsistent (T : Tableau Λ A) : Prop := Λ ⊢ⱽ ⋀(T.ant.image (·.1)) 🡒 ⋁(T.con.image (·.1))
abbrev Consistent (T : Tableau Λ A) : Prop := ¬(T.Inconsistent)

lemma iff_inconsistent : T.Inconsistent ↔ Λ ⊢ⱽ ⋀ (T.ant.image (·.1)) 🡒 ⋁ (T.con.image (·.1)) := by tauto;

def insertAnt (T : Tableau Λ A) (B : ScopeOf Λ A) : Tableau Λ A := { T with ant := insert B T.ant }
def insertCon (T : Tableau Λ A) (B : ScopeOf Λ A) : Tableau Λ A := { T with con := insert B T.con }

open ProvableVF in
lemma either_consistent_insert
  (T : Tableau Λ A) (B : ScopeOf Λ A) (T_consis : T.Consistent)
  : Tableau.Consistent (Tableau.insertAnt T B) ∨ Tableau.Consistent (Tableau.insertCon T B) := by
  by_contra! hC;
  rcases hC with ⟨hB₁, hB₂⟩;
  apply T_consis;
  simp only [Inconsistent, insertAnt, insertCon] at hB₁ hB₂ ⊢;
  generalize eΓ : T.ant.image (·.1) = Γ at ⊢ hB₁ hB₂;
  generalize eΔ : T.con.image (·.1) = Δ at ⊢ hB₁ hB₂;
  generalize eΔB : (insert B T.con).image (·.1) = ΔB at ⊢ hB₁ hB₂;
  generalize eΓB : (insert B T.ant).image (·.1) = ΓB at ⊢ hB₁ hB₂;
  apply ruleI₃ (B := (⋁Δ ⋎ ⋀Γ) ⋏ ⋁ΔB) (C := (⋁Δ ⋎ ⋀ΓB))
  . exact ruleC orIntroR hB₂;
  . apply ruleI₃ (B := ((⋁Δ ⋎ ⋀Γ) ⋏ (⋁Δ ⋎ B))) (C := ⋁Δ ⋎ (⋀Γ ⋏ B));
    . apply replaceAnd₂;
      subst eΔB eΔ;
      simpa using sdisj_insert;
    . exact distributeOrAnd
    . apply replaceOr₂;
      subst eΓB eΓ;
      simpa using sconj_insert;
  . exact ruleD impId hB₁;

def Saturated (T : Tableau Λ A) := T.ant ∪ T.con = Finset.univ

@[grind =>]
lemma mem_ant_of_not_mem_con_of_saturated {T : Tableau Λ A} (hT : T.Saturated) {B : ScopeOf Λ A} : B ∉ T.con → B ∈ T.ant := by
  have := hT ▸ Finset.mem_univ B;
  grind only [= Finset.mem_union];

@[grind =>]
lemma mem_con_of_not_mem_ant_of_saturated {T : Tableau Λ A} (hT : T.Saturated) {B : ScopeOf Λ A} : B ∉ T.ant → B ∈ T.con := by
  have := hT ▸ Finset.mem_univ B;
  grind only [= Finset.mem_union];

end Tableau


structure SaturatedConsistentTableau (Λ : Axioms α) (A : Formula α) extends Tableau Λ A where
  consistent : toTableau.Consistent
  saturated : toTableau.Saturated

namespace SaturatedConsistentTableau

open ProvableVF

instance : Finite (SaturatedConsistentTableau Λ A) := Finite.of_injective (·.toTableau) $ by
  rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩;
  simp;

variable {T : SaturatedConsistentTableau Λ A}

@[grind =]
lemma iff_mem_ant_not_mem_con : B ∈ T.ant ↔ B ∉ T.con := by
  constructor;
  . intro hB₁;
    by_contra! hB₂;
    apply T.consistent;
    apply ruleI₃ (B := B) (C := B) <;> grind;
  . apply T.toTableau.mem_ant_of_not_mem_con_of_saturated T.saturated;

@[grind =]
lemma iff_mem_con_not_mem_ant : B ∈ T.con ↔ B ∉ T.ant := by
  constructor;
  . contrapose!;
    exact iff_mem_ant_not_mem_con.mp;
  . apply T.toTableau.mem_con_of_not_mem_ant_of_saturated T.saturated;

lemma imp_closed : Λ ⊢ⱽ (B.1 🡒 C.1) → B ∈ T.ant → C ∈ T.ant := by
  rintro hBC hB;
  by_contra! hC;
  apply T.consistent;
  apply ruleI₃ (B := B) (C := C) <;> grind;

@[simp, grind .]
lemma mem_ant_top : ⟨⊤, by grind⟩ ∈ T.ant := by
  have := T.consistent;
  contrapose! this;
  exact ruleI (af (show Λ ⊢ⱽ ⊤ by simp)) $ sdisj_of_mem (by grind);

@[simp, grind .]
lemma mem_con_bot : ⟨⊥, by grind⟩ ∈ T.con := by
  have := T.consistent;
  contrapose! this;
  exact ruleI (sconj_of_mem (by grind)) efq;

@[grind =>]
lemma iff_mem_ant_and (hBC : (B ⋏ C) ∈ scope Λ A) : (⟨B ⋏ C, hBC⟩ ∈ T.ant) ↔ (⟨B, by grind⟩ ∈ T.ant ∧ ⟨C, by grind⟩ ∈ T.ant) := by
  constructor;
  . rintro h;
    constructor <;> exact T.imp_closed (by grind) h;
  . rintro ⟨hB, hC⟩;
    by_contra! hBC;
    apply T.consistent;
    apply ruleI (B := B ⋏ C);
    . apply ruleC <;> grind;
    . grind;

@[grind =>]
lemma iff_mem_ant_or (hBC : (B ⋎ C) ∈ scope Λ A) : (⟨B ⋎ C, hBC⟩ ∈ T.ant) ↔ (⟨B, by grind⟩ ∈ T.ant ∨ ⟨C, by grind⟩ ∈ T.ant) := by
  constructor;
  . rintro hBC;
    by_contra!;
    rcases this with ⟨hB, hC⟩;
    apply T.consistent;
    apply ruleI (B := B ⋎ C);
    . grind;
    . apply ruleD <;> grind;
  . rintro (hB | hC);
    . exact T.imp_closed (by grind) hB;
    . exact T.imp_closed (by grind) hC;

@[grind =>]
lemma mem_ant_of_provable (hB : Λ ⊢ⱽ B.1) : B ∈ T.ant := imp_closed (by grind) mem_ant_top

@[grind .]
lemma not_mem_both : ¬(B ∈ T.ant ∧ B ∈ T.con) := by grind;


namespace lindenbaum

open Classical

noncomputable def next (T : Tableau Λ A) (B : ScopeOf Λ A) : Tableau Λ A :=
  if Tableau.Consistent (Tableau.insertAnt T B) then Tableau.insertAnt T B else Tableau.insertCon T B

variable {T : Tableau Λ A} {B : ScopeOf Λ A} {X : List (ScopeOf Λ A)}

lemma next_consistent (hT : T.Consistent) : Tableau.Consistent (next T B) := by
  dsimp [next];
  split;
  . trivial;
  . grind [Tableau.either_consistent_insert];

lemma next_monotone_ant : T.ant ⊆ (next T B).ant := by grind [next, Tableau.insertAnt, Tableau.insertCon];
lemma next_monotone_con : T.con ⊆ (next T B).con := by grind [next, Tableau.insertAnt, Tableau.insertCon];

lemma next_of_mem : B ∈ (next T B).ant ∨ B ∈ (next T B).con := by grind [next, Tableau.insertAnt, Tableau.insertCon];

noncomputable def enum (T : Tableau Λ A) : List (ScopeOf Λ A) → Tableau Λ A
  | [] => T
  | B :: X => next (enum T X) B

@[simp, grind .]
lemma enum_consistent (hT : T.Consistent) {X : List (ScopeOf Λ A)} : Tableau.Consistent (enum T X) := by
  induction X with
  | nil => trivial
  | cons _ _ ih => apply next_consistent ih;

lemma enum_monotone_ant : T.ant ⊆ (enum T X).ant := by
  induction X with
  | nil => simp [enum];
  | cons B X ih =>
    trans (enum T X).ant;
    . exact ih;
    . exact next_monotone_ant;

lemma enum_monotone_con : T.con ⊆ (enum T X).con := by
  induction X with
  | nil => simp [enum];
  | cons B X ih =>
    trans (enum T X).con;
    . exact ih;
    . exact next_monotone_con;

lemma enum_of_mem (hB : B ∈ X) : B ∈ (enum T X).ant ∨ B ∈ (enum T X).con := by
  induction X with
  | nil => contradiction
  | cons C X ih =>
    simp only [List.mem_cons] at hB;
    rcases hB with rfl | hB;
    . rcases next_of_mem (T := enum T X) (B := B) with h | h <;> grind [enum];
    . rcases ih hB with h | h;
      . left; apply next_monotone_ant h;
      . right; apply next_monotone_con h;

end lindenbaum

noncomputable def lindenbaum (T : Tableau Λ A) (T_consis : T.Consistent) : SaturatedConsistentTableau Λ A where
  toTableau := lindenbaum.enum (Λ := Λ) (A := A) T (Finset.univ.toList)
  consistent := lindenbaum.enum_consistent T_consis
  saturated := by
    ext B;
    simp only [Finset.mem_union, Finset.mem_univ, iff_true];
    apply lindenbaum.enum_of_mem;
    simp;

@[simp, grind .] lemma lindenbaum_subset_ant {T : Tableau Λ A} {T_consis : T.Consistent} : T.ant ⊆ (lindenbaum T T_consis).ant := lindenbaum.enum_monotone_ant
@[simp, grind .] lemma lindenbaum_subset_con {T : Tableau Λ A} {T_consis : T.Consistent} : T.con ⊆ (lindenbaum T T_consis).con := lindenbaum.enum_monotone_con

end SaturatedConsistentTableau


namespace FMTSemantics

open Classical
open ProvableVF
open SaturatedConsistentTableau

noncomputable abbrev countermodel.rootSeed (Λ : Axioms α) (A : Formula α) : Tableau Λ A where
  ant := ∅
  con := Finset.univ.filter (λ ⟨B, _⟩ => ∃ C D, B = C.1 🡒 D.1 ∧ ∃ T : SaturatedConsistentTableau Λ A, C ∈ T.ant ∧ D ∈ T.con )

@[simp, grind .]
lemma countermodel.rootSeed_consistent {Λ : Axioms α} [Λ.ConsistentVF] [Λ.DisjunctiveVF] : (countermodel.rootSeed Λ A).Consistent := by
  by_contra! hC;
  replace hC : Λ ⊢ⱽ ⊤ 🡒 ⋁((rootSeed Λ A).con.image (·.1)) := by
    simpa only [rootSeed, Subtype.exists, exists_and_left, Finset.image_empty, Formula.sconj_emptyset]
    using (Tableau.iff_inconsistent.mp hC);
  replace hC := mdp hC verum;
  wlog ne : (rootSeed Λ A).con.image (·.1) ≠ ∅;
  . apply unprovable_bot (Λ := Λ);
    grind;
  obtain ⟨C, D, T, hC, hD, hCD⟩ : ∃ C D : ScopeOf Λ A, ∃ T : SaturatedConsistentTableau Λ A, C ∈ T.ant ∧ D ∈ T.con ∧ (Λ ⊢ⱽ C.1 🡒 D.1) := by
    have := sdisj_disjunctive ne hC;
    unfold rootSeed at this;
    grind;
  apply T.consistent;
  apply ruleI₃ (B := C.1) (C := D.1) <;> grind;

noncomputable def countermodel (Λ : Axioms α) (A) [Λ.ConsistentVF] [Λ.DisjunctiveVF] : Model (SaturatedConsistentTableau Λ A) α where
  Val a T := (ha : #a ∈ scope Λ A) → ⟨#a, ha⟩ ∈ T.ant
  Rel' B T₁ T₂ :=
    match B with
    | (C 🡒 D) => (h : C 🡒 D ∈ scope Λ A) → ⟨C 🡒 D, h⟩ ∈ T₁.con ∨ ⟨C, (by grind)⟩ ∈ T₂.con ∨ ⟨D, (by grind)⟩ ∈ T₂.ant
    | _ => True
  root' := SaturatedConsistentTableau.lindenbaum (countermodel.rootSeed Λ A) (countermodel.rootSeed_consistent)
  root_rooted' := by
    intro B T;
    split;
    . rename_i B C D;
      intro h;
      by_contra!;
      rcases this with ⟨hCD, hC, hD⟩;
      apply hCD;
      apply lindenbaum_subset_con;
      grind;
    . trivial;

variable [Λ.ConsistentVF] [Λ.DisjunctiveVF]

lemma countermodel.truthlemma {T : (countermodel Λ A).World} (hB : B ∈ scope Λ A) : ⟨B, hB⟩ ∈ T.ant ↔ Forces T B := by
  induction B generalizing T with
  | atom a => tauto;
  | bot => grind;
  | and => apply Iff.trans $ iff_mem_ant_and hB; grind;
  | or => apply Iff.trans $ iff_mem_ant_or hB; grind;
  | imp C D ihC ihD =>
    constructor;
    . intro h S RTS hC;
      replace hC_ant := @ihC S (by grind) |>.mpr hC;
      rcases RTS hB with hCD | hC_con | hD_ant;
      . grind;
      . grind;
      . apply ihD _ |>.mp (by grind);
        grind;
    . contrapose!;
      intro h;
      apply iff_not_Forces_imp.mpr;
      use lindenbaum ⟨{⟨C, (by grind)⟩}, {⟨D, (by grind)⟩}⟩ $ by
        by_contra;
        replace : Λ ⊢ⱽ C 🡒 D := by simpa using Tableau.iff_inconsistent.mp this;
        exact h $ T.mem_ant_of_provable this;
      refine ⟨?_, ?_, ?_⟩
      . intro _;
        left;
        exact T.iff_mem_con_not_mem_ant.mpr h;
      . apply ihC (by grind) |>.mp;
        apply lindenbaum_subset_ant;
        simp;
      . apply ihD (by grind) |>.not.mp;
        apply iff_mem_con_not_mem_ant.mp;
        apply lindenbaum_subset_con;
        simp;

lemma countermodel.valid_axioms : ∀ B ∈ Λ, (countermodel Λ A) ⊨ B := by
  intro B hB T;
  exact countermodel.truthlemma _ |>.mp $ T.mem_ant_of_provable (B := ⟨B, mem_scope_of_mem_axioms hB⟩) (axm hB);

theorem finite_model_property : (∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A) → Λ ⊢ⱽ A := by
  contrapose;
  intro h;
  push Not;
  use (SaturatedConsistentTableau Λ A), inferInstance, countermodel Λ A;
  constructor;
  . exact countermodel.valid_axioms;
  . apply iff_Valid_exists_world_not_Forces.mpr;
    use lindenbaum (Λ := Λ) (A := A) ⟨∅, {⟨A, by grind⟩}⟩ $ by
      by_contra;
      replace : Λ ⊢ⱽ ⊤ 🡒 A := by simpa using Tableau.iff_inconsistent.mp this;
      exact h $ mdp this verum;;
    apply countermodel.truthlemma (by grind) |>.not.mp;
    apply iff_mem_con_not_mem_ant.mp;
    apply lindenbaum_subset_con;
    simp;

theorem finite_frame_property (h_closed : ∀ B ∈ Λ, B.Closed)
  : (∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, (∀ B ∈ Λ, F ⊨ B) → F ⊨ A) → Λ ⊢ⱽ A := by
  intro h;
  apply finite_model_property;
  intro κ hκ M hM;
  apply h;
  grind [iff_FrameValid_ModelValid_of_closed];

theorem result_model : List.TFAE [
  Λ ⊢ⱽ A,
  ∀ {κ : Type u}, ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, (∀ B ∈ Λ, M ⊨ B) → M ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _; apply soundness_model h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_model_property
  tfae_finish;

theorem result_frame (h_closed : ∀ B ∈ Λ, B.Closed) : List.TFAE [
  Λ ⊢ⱽ A,
  ∀ {κ : Type u}, ∀ F : Frame κ α, (∀ B ∈ Λ, F ⊨ B) → F ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, (∀ B ∈ Λ, F ⊨ B) → F ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _; apply soundness_frame h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_frame_property (by grind);
  tfae_finish;




theorem VF_completeness : List.TFAE [
  ∅ ⊢ⱽ A,
  ∀ {κ : Type u}, ∀ F : Frame κ α, F ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, F ⊨ A
] := by
  have : Fact (∀ A ∈ (∅ : Axioms α), A.IsClosedNegativeAxiom) := ⟨by grind⟩;
  simpa using result_frame (Λ := ∅) (by simp);

omit [DecidableEq α] in
lemma iff_validates_negnegtop {F : Frame κ α} : (F ⊨ ∼∼⊤) ↔ (∀ x : F.World, ∃ y, x ≺[∼⊤] y) := by
  apply Iff.trans $ iff_frameValid_closed_dn (by grind);
  simp;

theorem VFSer_completeness : List.TFAE [
  {∼∼⊤} ⊢ⱽ A,
  ∀ {κ : Type u}, ∀ F : Frame κ α, (∀ x : F.World, ∃ y, x ≺[∼⊤] y) → F ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, (∀ x : F.World, ∃ y, x ≺[∼⊤] y) → F ⊨ A
] := by
  have : Fact (∀ A ∈ ({∼∼⊤} : Axioms α), A.IsClosedNegativeAxiom) := ⟨by grind⟩;
  simpa [iff_validates_negnegtop] using result_frame (Λ := {∼∼⊤}) (by grind);

end FMTSemantics
