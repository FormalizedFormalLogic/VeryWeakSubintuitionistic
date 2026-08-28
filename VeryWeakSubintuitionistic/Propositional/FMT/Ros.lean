module

public import VeryWeakSubintuitionistic.Propositional.FMT.Completeness
public import VeryWeakSubintuitionistic.Propositional.Proof.VFR.Slash

@[expose] public section

namespace FMTSemantics

section Soundness

variable {κ α : Type*} {F : Frame κ α} {M : Model κ α} {𝔸 : Axioms α} {A B C : Formula α}

namespace Frame

class Rosser (F : Frame κ α) : Prop where
  ros : ∀ (x : F.World) (A B : Formula α), ∃ y : F.World, x ≺[A 🡒 B] y
export Rosser (ros)

end Frame


@[grind <=]
lemma frameValid_ros [F.Rosser] (hA : F ⊨ ∼A) (hB : F ⊨ B) : F ⊨ ∼(B 🡒 A) := by
  intro V x y Rxy hBA;
  obtain ⟨z, Ryz⟩ := Frame.ros y B A;
  apply hA V F.root z (by grind);
  exact hBA z Ryz (hB V z);

@[grind <=]
lemma modelValid_ros [M.Rosser] (hA : M ⊨ ∼A) (hB : M ⊨ B) : M ⊨ ∼(B 🡒 A) := by
  intro x y Rxy hBA;
  obtain ⟨z, Ryz⟩ := Frame.ros (F := M.toFrame) y B A;
  apply hA M.root z (by grind);
  exact hBA z Ryz (hB z);

theorem soundness_frame_ros [F.Rosser] (h𝔸 : ∀ B ∈ 𝔸, F ⊨ B) : (⊢ʰ[VFR;𝔸] A) → F ⊨ A := by
  intro h; induction h <;> grind;

theorem soundness_model_ros [M.Rosser] (h𝔸 : ∀ B ∈ 𝔸, M ⊨ B) : (⊢ʰ[VFR;𝔸] A) → M ⊨ A := by
  intro h; induction h <;> grind;

end Soundness

end FMTSemantics


section

variable {α : Type u} [DecidableEq α]
variable {𝔸 : Axioms α} {A : Formula α}

namespace Tableau

variable {T : Tableau 𝔸 A}

def InconsistentVFR (T : Tableau 𝔸 A) : Prop := ⊢ʰ[VFR;𝔸] ⋀(T.ant.image (·.1)) 🡒 ⋁(T.con.image (·.1))
abbrev ConsistentVFR (T : Tableau 𝔸 A) : Prop := ¬(T.InconsistentVFR)

lemma iff_inconsistentVFR : T.InconsistentVFR ↔ ⊢ʰ[VFR;𝔸] ⋀ (T.ant.image (·.1)) 🡒 ⋁ (T.con.image (·.1)) := by tauto;

open VFR.ProvableHilbert in
lemma either_consistentVFR_insert
  (T : Tableau 𝔸 A) (B : ScopeOf 𝔸 A) (T_consis : T.ConsistentVFR)
  : Tableau.ConsistentVFR (Tableau.insertAnt T B) ∨ Tableau.ConsistentVFR (Tableau.insertCon T B) := by
  by_contra! hC;
  rcases hC with ⟨hB₁, hB₂⟩;
  apply T_consis;
  simp only [InconsistentVFR, insertAnt, insertCon] at hB₁ hB₂ ⊢;
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

end Tableau



structure SaturatedConsistentTableauVFR (𝔸 : Axioms α) (A : Formula α) extends Tableau 𝔸 A where
  consistent : toTableau.ConsistentVFR
  saturated : toTableau.Saturated

namespace SaturatedConsistentTableauVFR

open VFR.ProvableHilbert

instance : Finite (SaturatedConsistentTableauVFR 𝔸 A) := Finite.of_injective (·.toTableau) $ by
  rintro ⟨⟨_, _⟩⟩ ⟨⟨_, _⟩⟩;
  simp;

variable {T : SaturatedConsistentTableauVFR 𝔸 A}

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

lemma imp_closed : ⊢ʰ[VFR;𝔸] (B.1 🡒 C.1) → B ∈ T.ant → C ∈ T.ant := by
  rintro hBC hB;
  by_contra! hC;
  apply T.consistent;
  apply ruleI₃ (B := B) (C := C) <;> grind;

@[simp, grind .]
lemma mem_ant_top : ⟨⊤, by grind⟩ ∈ T.ant := by
  have := T.consistent;
  contrapose! this;
  exact ruleI (af (show ⊢ʰ[VFR;𝔸] ⊤ by simp)) $ sdisj_of_mem (by grind);

@[simp, grind .]
lemma mem_con_bot : ⟨⊥, by grind⟩ ∈ T.con := by
  have := T.consistent;
  contrapose! this;
  exact ruleI (sconj_of_mem (by grind)) efq;

@[grind =>]
lemma iff_mem_ant_and (hBC : (B ⋏ C) ∈ scope 𝔸 A) : (⟨B ⋏ C, hBC⟩ ∈ T.ant) ↔ (⟨B, by grind⟩ ∈ T.ant ∧ ⟨C, by grind⟩ ∈ T.ant) := by
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
lemma iff_mem_ant_or (hBC : (B ⋎ C) ∈ scope 𝔸 A) : (⟨B ⋎ C, hBC⟩ ∈ T.ant) ↔ (⟨B, by grind⟩ ∈ T.ant ∨ ⟨C, by grind⟩ ∈ T.ant) := by
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
lemma mem_ant_of_provable (hB : ⊢ʰ[VFR;𝔸] B.1) : B ∈ T.ant := imp_closed (by grind) mem_ant_top

@[grind .]
lemma not_mem_both : ¬(B ∈ T.ant ∧ B ∈ T.con) := by grind;


namespace lindenbaum

open Classical

noncomputable def next (T : Tableau 𝔸 A) (B : ScopeOf 𝔸 A) : Tableau 𝔸 A :=
  if Tableau.ConsistentVFR (Tableau.insertAnt T B) then Tableau.insertAnt T B else Tableau.insertCon T B

variable {T : Tableau 𝔸 A} {B : ScopeOf 𝔸 A} {X : List (ScopeOf 𝔸 A)}

lemma next_consistent (hT : T.ConsistentVFR) : Tableau.ConsistentVFR (next T B) := by
  dsimp [next];
  split;
  . trivial;
  . grind [Tableau.either_consistentVFR_insert];

lemma next_monotone_ant : T.ant ⊆ (next T B).ant := by grind [next, Tableau.insertAnt, Tableau.insertCon];
lemma next_monotone_con : T.con ⊆ (next T B).con := by grind [next, Tableau.insertAnt, Tableau.insertCon];

lemma next_of_mem : B ∈ (next T B).ant ∨ B ∈ (next T B).con := by grind [next, Tableau.insertAnt, Tableau.insertCon];

noncomputable def enum (T : Tableau 𝔸 A) : List (ScopeOf 𝔸 A) → Tableau 𝔸 A
  | [] => T
  | B :: X => next (enum T X) B

@[simp, grind .]
lemma enum_consistent (hT : T.ConsistentVFR) {X : List (ScopeOf 𝔸 A)} : Tableau.ConsistentVFR (enum T X) := by
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

noncomputable def lindenbaum (T : Tableau 𝔸 A) (T_consis : T.ConsistentVFR) : SaturatedConsistentTableauVFR 𝔸 A where
  toTableau := lindenbaum.enum (𝔸 := 𝔸) (A := A) T (Finset.univ.toList)
  consistent := lindenbaum.enum_consistent T_consis
  saturated := by
    ext B;
    simp only [Finset.mem_union, Finset.mem_univ, iff_true];
    apply lindenbaum.enum_of_mem;
    simp;

@[simp, grind .] lemma lindenbaum_subset_ant {T : Tableau 𝔸 A} {T_consis : T.ConsistentVFR} : T.ant ⊆ (lindenbaum T T_consis).ant := lindenbaum.enum_monotone_ant
@[simp, grind .] lemma lindenbaum_subset_con {T : Tableau 𝔸 A} {T_consis : T.ConsistentVFR} : T.con ⊆ (lindenbaum T T_consis).con := lindenbaum.enum_monotone_con

end SaturatedConsistentTableauVFR


namespace FMTSemantics

open Classical
open VFR.ProvableHilbert
open SaturatedConsistentTableauVFR

noncomputable abbrev countermodelRos.rootSeed (𝔸 : Axioms α) (A : Formula α) : Tableau 𝔸 A where
  ant := ∅
  con := Finset.univ.filter (λ ⟨B, _⟩ => ∃ C D, B = C.1 🡒 D.1 ∧ ∃ T : SaturatedConsistentTableauVFR 𝔸 A, C ∈ T.ant ∧ D ∈ T.con )

@[simp, grind .]
lemma countermodelRos.rootSeed_consistent {𝔸 : Axioms α} [VFR.Consistent 𝔸] [VFR.Disjunctive 𝔸] : (countermodelRos.rootSeed 𝔸 A).ConsistentVFR := by
  by_contra! hC;
  replace hC : ⊢ʰ[VFR;𝔸] ⊤ 🡒 ⋁((rootSeed 𝔸 A).con.image (·.1)) := by
    simpa only [rootSeed, Subtype.exists, exists_and_left, Finset.image_empty, Formula.sconj_emptyset]
    using (Tableau.iff_inconsistentVFR.mp hC);
  replace hC := mdp hC verum;
  wlog ne : (rootSeed 𝔸 A).con.image (·.1) ≠ ∅;
  . apply unprovable_bot (𝔸 := 𝔸);
    grind;
  obtain ⟨C, D, T, hC, hD, hCD⟩ : ∃ C D : ScopeOf 𝔸 A, ∃ T : SaturatedConsistentTableauVFR 𝔸 A, C ∈ T.ant ∧ D ∈ T.con ∧ (⊢ʰ[VFR;𝔸] C.1 🡒 D.1) := by
    have := sdisj_disjunctive ne hC;
    unfold rootSeed at this;
    grind;
  apply T.consistent;
  apply ruleI₃ (B := C.1) (C := D.1) <;> grind;

noncomputable def countermodelRos (𝔸 : Axioms α) (A) [VFR.Consistent 𝔸] [VFR.Disjunctive 𝔸] : Model (SaturatedConsistentTableauVFR 𝔸 A) α where
  Val a T := (ha : #a ∈ scope 𝔸 A) → ⟨#a, ha⟩ ∈ T.ant
  Rel' B T₁ T₂ :=
    match B with
    | (C 🡒 D) => (h : C 🡒 D ∈ scope 𝔸 A) → ⟨C 🡒 D, h⟩ ∈ T₁.con ∨ ⟨C, (by grind)⟩ ∈ T₂.con ∨ ⟨D, (by grind)⟩ ∈ T₂.ant
    | _ => True
  root' := SaturatedConsistentTableauVFR.lindenbaum (countermodelRos.rootSeed 𝔸 A) (countermodelRos.rootSeed_consistent)
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

variable [VFR.Consistent 𝔸] [VFR.Disjunctive 𝔸]

lemma countermodelRos.truthlemma {T : (countermodelRos 𝔸 A).World} (hB : B ∈ scope 𝔸 A) : ⟨B, hB⟩ ∈ T.ant ↔ Forces T B := by
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
        replace : ⊢ʰ[VFR;𝔸] C 🡒 D := by simpa using Tableau.iff_inconsistentVFR.mp this;
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

lemma countermodelRos.valid_axioms : ∀ B ∈ 𝔸, (countermodelRos 𝔸 A) ⊨ B := by
  intro B hB T;
  exact countermodelRos.truthlemma _ |>.mp $ T.mem_ant_of_provable (B := ⟨B, mem_scope_of_mem_axioms hB⟩) (axm hB);

instance : (countermodelRos 𝔸 A).Rosser := by
  constructor;
  intro T C D;
  by_cases hCD : (C 🡒 D) ∈ scope 𝔸 A;
  . obtain ⟨hCs, hDs⟩ := mem_scope_of_mem_imp_scope hCD;
    by_cases hTcon : (⟨C 🡒 D, hCD⟩ : ScopeOf 𝔸 A) ∈ T.con;
    . use T;
      tauto;
    . by_cases hC : ⊢ʰ[VFR;𝔸] C;
      . by_cases hD : ⊢ʰ[VFR;𝔸] ∼D;
        . exfalso;
          have hbot : (⟨⊥, by grind⟩ : ScopeOf 𝔸 A) ∈ T.ant := by
            apply T.imp_closed (B := ⟨C 🡒 D, hCD⟩);
            . exact VFR.ProvableHilbert.ros hD hC;
            . exact T.iff_mem_ant_not_mem_con.mpr hTcon;
          exact T.not_mem_both ⟨hbot, T.mem_con_bot⟩;
        . refine ⟨lindenbaum ⟨{⟨D, hDs⟩}, ∅⟩ ?_, ?_⟩;
          . by_contra hc;
            apply hD;
            simpa using Tableau.iff_inconsistentVFR.mp hc;
          . intro _;
            right;
            right;
            apply lindenbaum_subset_ant;
            simp;
      . refine ⟨lindenbaum ⟨∅, {⟨C, hCs⟩}⟩ ?_, ?_⟩;
        . contrapose! hC;
          replace hc : ⊢ʰ[VFR;𝔸] ⊤ 🡒 C := by simpa using Tableau.iff_inconsistentVFR.mp hC;
          exact mdp hc verum;
        . intro _;
          right;
          left;
          apply lindenbaum_subset_con;
          simp;
  . use T;
    intro h;
    contradiction;

theorem finite_model_property_ros
  : (∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, M.Rosser → (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A) → ⊢ʰ[VFR;𝔸] A := by
  contrapose;
  intro h;
  push Not;
  use (SaturatedConsistentTableauVFR 𝔸 A), inferInstance, countermodelRos 𝔸 A, inferInstance;
  constructor;
  . exact countermodelRos.valid_axioms;
  . apply iff_Valid_exists_world_not_Forces.mpr;
    use lindenbaum (𝔸 := 𝔸) (A := A) ⟨∅, {⟨A, by grind⟩}⟩ $ by
      by_contra;
      replace : ⊢ʰ[VFR;𝔸] ⊤ 🡒 A := by simpa using Tableau.iff_inconsistentVFR.mp this;
      exact h $ mdp this verum;;
    apply countermodelRos.truthlemma (by grind) |>.not.mp;
    apply iff_mem_con_not_mem_ant.mp;
    apply lindenbaum_subset_con;
    simp;

theorem finite_frame_property_ros (h_closed : ∀ B ∈ 𝔸, B.Closed)
  : (∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, F.Rosser → (∀ B ∈ 𝔸, F ⊨ B) → F ⊨ A) → ⊢ʰ[VFR;𝔸] A := by
  intro h;
  apply finite_model_property_ros;
  intro κ hκ M hR hM;
  apply h;
  . exact hR;
  . grind [iff_FrameValid_ModelValid_of_closed];

theorem result_model_ros : List.TFAE [
  ⊢ʰ[VFR;𝔸] A,
  ∀ {κ : Type u}, ∀ M : Model κ α, M.Rosser → (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ M : Model κ α, M.Rosser → (∀ B ∈ 𝔸, M ⊨ B) → M ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _ M hR hM; haveI := hR; exact soundness_model_ros hM h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_model_property_ros
  tfae_finish;

theorem result_frame_ros (h_closed : ∀ B ∈ 𝔸, B.Closed) : List.TFAE [
  ⊢ʰ[VFR;𝔸] A,
  ∀ {κ : Type u}, ∀ F : Frame κ α, F.Rosser → (∀ B ∈ 𝔸, F ⊨ B) → F ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, F.Rosser → (∀ B ∈ 𝔸, F ⊨ B) → F ⊨ A
] := by
  tfae_have 1 → 2 := by intro h _ F hR h𝔸; haveI := hR; exact soundness_frame_ros h𝔸 h;
  tfae_have 2 → 3 := by grind;
  tfae_have 3 → 1 := finite_frame_property_ros (by grind);
  tfae_finish;

theorem VFR_completeness : List.TFAE [
  ⊢ʰ[VFR;∅] A,
  ∀ {κ : Type u}, ∀ F : Frame κ α, F.Rosser → F ⊨ A,
  ∀ {κ : Type u}, [Finite κ] → ∀ F : Frame κ α, F.Rosser → F ⊨ A
] := by
  have : Fact (∀ A ∈ (∅ : Axioms α), A.IsClosedNegativeAxiom) := ⟨by grind⟩;
  simpa using result_frame_ros (𝔸 := ∅) (by simp);

end FMTSemantics

end

end
