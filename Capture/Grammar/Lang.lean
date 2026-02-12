-- We extend the semantics of regular expressions in Capture.Regex.Lang to also include hedge nodes.

import Capture.Std.Hedge

import Capture.Regex.Lang

namespace Lang

-- The denotation of node used in Grammar.Denote
def node_match {α: Type} (φ: α → Bool) (R: Lang (Hedge.Node α)): Lang (Hedge.Node α) :=
  fun xs =>
    match xs with
    | [Hedge.Node.mk label children] =>
      φ label /\ R children
    | _ => False

-- The denotation of node that we would have liked to use, if match was not required for termination proof purposes.
-- Luckily we still get to use this definition in a lot of proofs.
def node {α: Type} (φ: α → Bool) (R: Lang (Hedge.Node α)): Lang (Hedge.Node α) :=
  fun xs => ∃ label children, xs = [Hedge.Node.mk label children] /\ φ label /\ R children

-- We show that the two definitions of denotation of node is equivalent.
theorem node_is_node_match:
  node φ R = node_match φ R := by
  unfold node
  unfold node_match
  funext xs
  cases xs with
  | nil =>
    simp only [List.ne_cons_self, false_and, exists_const, exists_false]
  | cons x xs =>
    cases xs with
    | nil =>
      simp only [List.cons.injEq, and_true, eq_iff_iff]
      cases x with
      | mk label children =>
      simp only [Hedge.Node.mk.injEq]
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨label1, children1, ⟨h1, h2⟩, h3⟩ := h
        subst_vars
        exact h3
      case mpr =>
        intro ⟨h1, h2⟩
        exists label
        exists children
    | cons x' xs =>
      simp only [List.cons.injEq, reduceCtorEq, and_false, false_and, exists_const, exists_false]

example: Lang (Hedge.Node Nat) := (node (fun x => x = 1) (Lang.or (node (fun x => x = 1) Lang.emptystr) Lang.emptyset))

theorem null_iff_node {α: Type} {p: α → Bool} {children: Lang (Hedge.Node α)}:
  Lang.null (node p children) <-> False :=
  Iff.intro nofun nofun

theorem null_node {α: Type} {p: α → Bool} {children: Lang (Hedge.Node α)}:
  Lang.null (node p children) = False := by
  rw [null_iff_node]

theorem derive_iff_node {α: Type} {p: α → Bool} {childlang: Lang (Hedge.Node α)} {label: α} {children: Hedge α} {xs: Hedge α}:
  (Lang.derive (node p childlang) (Hedge.Node.mk label children)) xs <->
  (Lang.onlyif (p label /\ childlang children) Lang.emptystr) xs := by
  simp only [Lang.derive]
  simp only [Lang.onlyif, Lang.emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    unfold node
    simp only [List.cons.injEq, Hedge.Node.mk.injEq]
    intro ⟨ label', children', ⟨ ⟨ hlabel', hchildren' ⟩, hxs ⟩ , hif ⟩
    subst_vars
    simp only [and_true]
    exact hif
  case invFun =>
    intro ⟨ hif , hxs  ⟩
    unfold node
    exists label
    exists children
    rw [hxs]
    simp only [true_and]
    exact hif

theorem derive_node {α: Type} {p: α → Bool} {childlang: Lang (Hedge.Node α)} {label: α} {children: Hedge α}:
  (Lang.derive (node p childlang) (Hedge.Node.mk label children)) =
  (Lang.onlyif (p label /\ childlang children) Lang.emptystr) := by
  funext
  rw [derive_iff_node]
