module

public import VeryWeakSubintuitionistic.Propositional.FMT.Completeness

@[expose] public section

namespace FMTSemantics

variable {F : Frame κ α} {A B C : Formula α}

class Frame.Rosser (F : Frame κ α) : Prop where
  ros : ∀ x A B, ∃ z : F.World, x ≺[B 🡒 A] z

lemma frameValid_ros [F.Rosser] (hA : F ⊨ ∼A) (hB : F ⊨ B) : F ⊨ ∼(B 🡒 A) := by
  intro V x y Rxy hBA;
  obtain ⟨z, _⟩ := Frame.Rosser.ros y A B;
  apply hA V F.root z (by grind);
  apply hBA;
  . assumption;
  . apply hB;

open Classical
open ProvableVF
open SaturatedConsistentTableau

noncomputable def countermodelRos (Λ : Axioms α) (A) [Λ.ConsistentVF] [Λ.DisjunctiveVF] : Model (SaturatedConsistentTableau Λ A) α where
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

variable {Λ : Axioms α} [Λ.ConsistentVF] [Λ.DisjunctiveVF]

lemma countermodelRos_Rosser : (countermodelRos Λ A).Rosser := by
  constructor;
  intro T B C;
  wlog _ :  C 🡒 B ∈ scope Λ A;
  . use T;
    intro h;
    contradiction;
  sorry;

end FMTSemantics

end
