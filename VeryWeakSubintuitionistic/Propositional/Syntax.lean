module

public import Mathlib

@[expose] public section

variable {α : Type*}

inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | bot    : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
deriving DecidableEq

namespace Formula

prefix:100 "#" => atom
notation:90 "⊥" => bot
infixr:85 " 🡒 " => imp
infixl:84 " ⋏ " => and
infixl:83 " ⋎ " => or

@[match_pattern]
abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
prefix:90 "∼" => neg

@[match_pattern]
abbrev top : Formula α := ∼⊥
notation:91 "⊤" => top

@[match_pattern]
abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
infix:82 " 🡘 " => iff


@[simp, grind]
def lconj : List (Formula α) → Formula α
  | [] => ⊤
  | [A] => A
  | A :: X => A ⋏ (lconj X)
prefix:100 "⋀" => lconj

@[simp, grind]
def ldisj : List (Formula α) → Formula α
  | [] => ⊥
  | [A] => A
  | A :: X => A ⋎ (ldisj X)
prefix:100 "⋁" => ldisj


noncomputable def sconj (s : Finset (Formula α)) : Formula α := ⋀(s.toList)
prefix:100 "⋀" => sconj

@[simp, grind =_] lemma sconj_emptyset : (sconj (∅ : Finset (Formula α))) = ⊤ := by simp [sconj, lconj];
@[simp, grind =] lemma sconj_singleton {A : Formula α} : (sconj {A}) = A := by simp [sconj, lconj];


noncomputable def sdisj (s : Finset (Formula α)) : Formula α := ⋁(s.toList)
prefix:100 "⋁" => sdisj

@[simp, grind =_] lemma sdisj_emptyset : (sdisj (∅ : Finset (Formula α))) = ⊥ := by simp [sdisj, ldisj];
@[simp, grind =] lemma sdisj_singleton {A : Formula α} : (sdisj {A}) = A := by simp [sdisj, ldisj];


@[grind]
def Closed : Formula α → Prop
  | #_ => False
  | ⊥ => True
  | A ⋎ B
  | A ⋏ B
  | A 🡒 B => A.Closed ∧ B.Closed


def cases_neg {P : Formula α → Prop}
  (bot : P (⊥ : Formula α))
  (atom : ∀ a, P (#a))
  (and : ∀ A B, P (A ⋏ B))
  (or : ∀ A B, P (A ⋎ B))
  (imp : ∀ A B, B ≠ (⊥ : Formula α) → P (A 🡒 B))
  (neg : ∀ A, P (∼A))
  : ∀ A, P A := by
  intro A;
  match A with
  | ⊥ | #_ | _ ⋏ _ | _ ⋎ _
  | _ 🡒 ⊥ | _ 🡒 #_
  | _ 🡒 (_ ⋏ _) | _ 🡒 (_ ⋎ _) | _ 🡒 (_ 🡒 _)
    => grind;

end Formula

end
