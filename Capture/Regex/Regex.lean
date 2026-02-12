-- Regex defines a regular expression types, denotation of semantics, derivative function and its commutative proof and also a filter function and proof.
-- We define: Regex, null, denote, derive, validate and filter.
-- We prove: null_commutes, derive_commutes, validate_commutes, mem_filter.
-- We also show that validate is decidable.

import Capture.Std.Decidable

import Capture.Regex.Lang

-- A symbolic regular expression defined over a generic symbol
inductive Regex (σ: Type) where
  | emptyset | emptystr | symbol (s: σ) | or (r1 r2: Regex σ)
  | concat (r1 r2: Regex σ) | star (r1: Regex σ)
  | group (id: Nat) (x: Regex σ)
  deriving DecidableEq, Ord, Repr, Hashable

-- null defines whether a regular expression matches the empty string.
def Regex.null: (r: Regex σ) → Bool
  | emptyset => false | emptystr => true | symbol _ => false
  | or r1 r2 => (null r1 || null r2) | concat r1 r2 => (null r1 && null r2)
  | star _ => true | group _ r1 => null r1

-- denote defines the semantics of a regular expression.
def Regex.denote (Φ: σ → α → Prop) (r: Regex σ) (xs: List α): Prop :=
  match r with
  | emptyset => False
  | emptystr => xs = []
  | symbol s => match xs with
    | [x] => Φ s x | _ => False
  | or r1 r2 => (denote Φ r1 xs) \/ (denote Φ r2 xs)
  | concat r1 r2 => ∃ (i: Fin (xs.length + 1)),
      (denote Φ r1 (List.take i xs)) /\ (denote Φ r2 (List.drop i xs))
  | star r1 => match xs with
    | [] => True
    | (x::xs') => ∃ (i: Fin xs.length),
                        (denote Φ r1 (x::List.take i xs'))
                        /\ (denote Φ (Regex.star r1) (List.drop i xs'))
  | group _ r1 => denote Φ r1 xs
  termination_by (r, xs.length)

namespace Regex

-- unescapable is true if a derivative will always result in the same regular expression that the input.
def unescapable :(x: Regex σ) → Bool
  | emptyset => true | _ => false

-- onlyif (scalar operator in https://doi.org/10.1145/3473583) is a helper function use to define derivatives of regular expressions.
def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex σ): Regex σ :=
  if cond then r else emptyset

-- oneOrMore is the `r+` operator for regular expressions.
def oneOrMore (r: Regex σ) := concat r (star r)

-- optional is the `r?` operator for regular expressions.
def optional (r: Regex σ) := or r emptystr

-- denote_onlyif proves the the onlyif function (or operator) is equivalent to the language semantics.
theorem denote_onlyif {α: Type} (Φ : σ → α → Prop) (condition: Prop) [dcond: Decidable condition] (r: Regex σ):
  denote Φ (onlyif condition r) = Lang.onlyif condition (denote Φ r) := by
  unfold Lang.onlyif
  unfold onlyif
  funext xs
  split
  case isTrue h =>
    simp
    intro h'
    assumption
  case isFalse h =>
    simp
    simp [denote]
    intro h'
    contradiction

end Regex

-- derive defines the derivative of a regular expression.
def Regex.derive (Φ: σ → α → Bool) (r: Regex σ) (a: α): Regex σ := match r with
  | emptyset => emptyset | emptystr => emptyset
  | symbol s => onlyif (Φ s a) emptystr
  | or r1 r2 => or (derive Φ r1 a) (derive Φ r2 a)
  | concat r1 r2 => or
      (concat (derive Φ r1 a) r2)
      (onlyif (null r1) (derive Φ r2 a))
  | star r1 => concat (derive Φ r1 a) (star r1)
  | group n r1 => group n (derive Φ r1 a)

-- example derivative
#guard Regex.derive (· == ·) (Regex.or (Regex.symbol 1) (Regex.symbol 2)) 1
  = Regex.or Regex.emptystr Regex.emptyset

-- validate returns whether a regular expression matches a string.
def Regex.validate (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  null (List.foldl (derive Φ) r xs)

namespace Regex

-- derive theorems

theorem derive_emptyset {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  derive Φ emptyset a = emptyset := by
  simp only [derive]

theorem derive_emptystr {α: Type} {σ: Type} (Φ: σ → α → Bool) (a: α):
  derive Φ emptystr a = emptyset := by
  simp only [derive]

theorem derive_symbol {α: Type} {σ: Type} (Φ: σ → α → Bool) (s: σ) (a: α):
  derive Φ (symbol s) a = onlyif (Φ s a) emptystr := by
  simp only [derive]

theorem derive_or {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  derive Φ (or r1 r2) a = or (derive Φ r1 a) (derive Φ r2 a) := by
  simp only [derive]

theorem derive_concat {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1 r2: Regex σ) (a: α):
  derive Φ (concat r1 r2) a
    = or
      (concat (derive Φ r1 a) r2)
      (onlyif (null r1) (derive Φ r2 a)) := by
  simp only [derive]

theorem derive_star {α: Type} {σ: Type} (Φ: σ → α → Bool) (r1: Regex σ) (a: α):
  derive Φ (star r1) a = concat (derive Φ r1 a) (star r1) := by
  simp only [derive]

-- We prove that for each regular expression the denotation holds for the specific language definition:
-- * Regex.denote Φ Regex.emptyset = Lang.emptyset
-- * Regex.denote Φ Regex.emptystr = Lang.emptystr
-- * Regex.denote Φ (Regex.symbol s) = Φ s
-- * Regex.denote Φ (Regex.or p q) = Lang.or (Regex.denote Φ p) (Regex.denote Φ q)
-- * Regex.denote Φ (Regex.concat p q) = Lang.concat (Regex.denote Φ p) (Regex.denote Φ q)
-- * Regex.denote Φ (Regex.star r) = Lang.star (Regex.denote Φ r)

theorem denote_emptyset {α: Type} {σ: Type} (Φ: σ → α → Prop):
  denote Φ emptyset = Lang.emptyset := by
  funext xs
  simp only [denote, Lang.emptyset]

theorem denote_emptystr {α: Type} {σ: Type} (Φ: σ → α → Prop):
  denote Φ emptystr = Lang.emptystr := by
  funext xs
  simp only [denote, Lang.emptystr]

theorem denote_symbol {α: Type} {σ: Type} (Φ: σ → α → Prop) (s: σ):
  denote Φ (symbol s) = Lang.symbol Φ s := by
  funext xs
  cases xs with
  | nil =>
    simp only [denote, Lang.symbol]
    -- aesop?
    simp_all only [List.ne_cons_self, false_and, exists_false]
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [denote, Lang.symbol]
      -- aesop?
      simp_all only [List.cons.injEq, and_true, exists_eq_left']
    | cons x' xs =>
      simp only [denote, Lang.symbol]
      -- aesop?
      simp_all only [List.cons.injEq, reduceCtorEq, and_false, false_and, exists_false]

theorem denote_or {α: Type} {σ: Type} (Φ: σ → α → Prop) (r1 r2: Regex σ):
  denote Φ (or r1 r2) = Lang.or (denote Φ r1) (denote Φ r2) := by
  funext
  simp only [denote, Lang.or]

theorem denote_concat {α: Type} {σ: Type} (Φ: σ → α → Prop) (r1 r2: Regex σ):
  denote Φ (concat r1 r2) = Lang.concat (denote Φ r1) (denote Φ r2) := by
  funext
  simp only [denote, Lang.concat]

theorem denote_star_iff {α: Type} {σ: Type} (Φ: σ → α → Prop) (r1: Regex σ) (xs: List α):
  denote Φ (star r1) xs ↔ Lang.star (denote Φ r1) xs := by
  cases xs with
  | nil =>
    simp only [denote, Lang.star]
  | cons x xs =>
    simp only [denote, Lang.star]
    apply Iff.intro
    case mp =>
      intro h
      obtain ⟨⟨i, hi⟩, h1, h2⟩ := h
      exists ⟨i, hi⟩
      apply And.intro h1
      rw [<- (denote_star_iff Φ r1 (List.drop i xs))]
      simp only at h2
      exact h2
    case mpr =>
      intro h
      obtain ⟨⟨i, hi⟩, h1, h2⟩ := h
      exists ⟨i, hi⟩
      apply And.intro h1
      rw [(denote_star_iff Φ r1 (List.drop i xs))]
      simp only at h2
      exact h2
  termination_by xs.length

theorem denote_star {α: Type} {σ: Type} (Φ: σ → α → Prop) (r: Regex σ):
  denote Φ (star r) = Lang.star (denote Φ r) := by
  funext xs
  rw [denote_star_iff]

theorem denote_group {α: Type} {σ: Type} (Φ: σ → α → Prop) (r: Regex σ):
  denote Φ (group n r) = denote Φ r := by
  funext xs
  simp [denote]

-- Commutes proofs

theorem null_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) (r: Regex σ):
  ((null r) = true) = Lang.null (denote Φ r) := by
  unfold Lang.null
  induction r with
  | emptyset =>
    unfold denote
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    unfold null
    simp only
  | symbol p =>
    unfold denote
    unfold null
    apply Bool.false_eq_true
  | or r1 r2 ih1 ih2 =>
    unfold denote
    unfold null
    rw [<- ih1]
    rw [<- ih2]
    rw [Bool.or_eq_true]
  | concat r1 r2 ih1 ih2 =>
    unfold denote
    unfold null
    rw [Bool.and_eq_true r1.null r2.null]
    rw [ih1]
    rw [ih2]
    simp only [List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.take_nil, List.drop_nil,
      exists_const]
  | star r1 ih1 =>
    unfold denote
    unfold null
    simp only
  | group _ r1 ih =>
    unfold denote
    unfold null
    exact ih

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (x: α):
  denote Φ (derive (fun s a => Φ s a) r x) = Lang.derive (denote Φ r) x := by
  induction r with
  | emptyset =>
    simp only [derive, denote_emptyset]
    rw [Lang.derive_emptyset]
  | emptystr =>
    simp only [derive, denote_emptyset, denote_emptystr]
    rw [Lang.derive_emptystr]
  | symbol p =>
    simp only [denote_symbol]
    rw [Lang.derive_symbol]
    unfold derive
    rw [denote_onlyif]
    simp only [denote_emptystr]
    simp only [decide_eq_true_eq]
  | or r1 r2 ih1 ih2 =>
    simp only [denote_or, derive]
    rw [Lang.derive_or]
    unfold Lang.or
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [denote_concat, denote_or, derive]
    rw [Lang.derive_concat]
    rw [<- ih1]
    rw [<- ih2]
    rw [denote_onlyif]
    congr
    rw [null_commutes]
  | star r1 ih1 =>
    simp only [denote_star, denote_concat, derive]
    rw [Lang.derive_star]
    guard_target =
      Lang.concat (denote Φ (derive (fun s a => Φ s a) r1 x)) (Lang.star (denote Φ r1))
      = Lang.concat (Lang.derive (denote Φ r1) x) (Lang.star (denote Φ r1))
    congr
  | group n r1 ih1 =>
    simp [denote_group]
    simp [derive]
    simp [denote_group]
    congr

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (x: α):
  denote (fun s a => Φ s a) (derive Φ r x) = Lang.derive (denote (fun s a => Φ s a) r) x := by
  rw [<- derive_commutes]
  congr
  funext s a
  simp only [Bool.decide_eq_true]

theorem derives_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  denote Φ (List.foldl (derive (decideRel Φ)) r xs) = Lang.derives (denote Φ r) xs := by
  rw [Lang.derives_foldl]
  induction xs generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes Φ r x
    have ih' := ih (derive (fun s a => Φ s a) r x)
    rw [h] at ih'
    exact ih'

theorem validate_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  (validate (decideRel Φ) r xs = true) = (denote Φ r) xs := by
  rw [<- Lang.validate (denote Φ r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms
def decidableDenote (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ): DecidablePred (denote Φ r) :=
  fun xs => decidable_of_decidable_of_eq (validate_commutes Φ r xs)

end Regex

-- filter

-- filter filters a list of strings based on whether they match a regular expression.
def Regex.filter (Φ: σ → α → Bool) (r: Regex σ) (xs: List (List α)) :=
  List.filter (validate Φ r) xs

namespace Regex

-- mem_filter proves that the filter implementation matches the semantic definition.
theorem mem_filter (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xss: List (List α)) :
  ∀ xs, (xs ∈ filter (decideRel Φ) r xss) ↔ (Lang.MemFilter (denote Φ r) xss xs) := by
  unfold filter
  intro xs
  rw [List.mem_filter]
  unfold Lang.MemFilter
  apply Iff.intro
  case mp =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [<- validate_commutes]
    assumption
  case mpr =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [validate_commutes]
    assumption
