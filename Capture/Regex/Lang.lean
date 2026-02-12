-- We define a language, without depending on a regular expression, but for a regular expression.
-- We define semantics for all the operators.
-- We also define alternative semantic defintions and prove their equivalence to the versions we end up using, for extra surity.
-- The operators with extra defintions include: concat, star and interleave.
-- We also prove a few simplifcation rules.

import Capture.Std.List

-- The denotation of a Regex or Grammar defines its meaning or semantics via the Language, Lang.
-- A Regex is defined as the set of strings it matches, while a Grammar is defined as the set of hedges it matches,
-- both of which can be represented as \Lang with a different generic parameter.
def Lang (α: Type): Type := List α → Prop

-- Whether a language matches the empty string
def Lang.null (R: Lang α): Prop := R []

-- The derivative of a language is the language consisting of all strings remaining after the input element has been matched.
def Lang.derive (R: Lang α) (x: α): Lang α := fun (xs: List α) => R (x :: xs)

def Lang.emptyset: Lang α := fun _ => False

def Lang.emptystr: Lang α := fun xs => xs = []

def Lang.symbol (Φ: σ → α → Prop) (s: σ): Lang α :=
  fun xs => ∃ x, xs = [x] /\ Φ s x

def Lang.onlyif (cond : Prop) (P : Lang α): Lang α := fun xs => cond /\ P xs

def Lang.or (P : Lang α) (Q : Lang α): Lang α := fun xs => P xs \/ Q xs

def Lang.concat (P : Lang α) (Q : Lang α): Lang α := fun (xs : List α) =>
  ∃ n: Fin (xs.length + 1), P (List.take n xs) /\ Q (List.drop n xs)

def Lang.star (R: Lang α) (xs: List α): Prop :=
  match xs with
  | [] => True
  | (x::xs') => ∃ (n: Fin xs.length),
      R (x::List.take n xs') /\ Lang.star R (List.drop n xs')
  termination_by xs.length

def Lang.and {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun xs => P xs /\ Q xs

def Lang.compliment {α: Type} (R: Lang α): Lang α :=
  fun xs => (Not (R xs))

def Lang.interleave (P : Lang α) (Q : Lang α) (xs: List α): Prop :=
  ∃ (i: Fin (List.interleaves xs).length),
    P (List.get (List.interleaves xs) i).1
    /\ Q (List.get (List.interleaves xs) i).2

-- Verifying the correctness of a filtering function, requires proving that the filtered elements are
-- exactly those that both occur in the original list and belong to the language.
def Lang.MemFilter {α: Type} (R: Lang α) (xs: List (List α)): Lang α :=
  fun x => x ∈ xs /\ R x

namespace Lang

-- Alternative definitions of interleave interleave_mem and interleave_derive.
-- Theorems proving equivalence to alternative definitions of interleave.

def interleave_mem (P : Lang α) (Q : Lang α) (xs: List α): Prop :=
  ∃ interleave ∈ List.interleaves xs, P interleave.1 ∧ Q interleave.2

def interleave_derive (P : Lang α) (Q : Lang α) (xs: List α): Prop :=
  match xs with
  | [] => P [] /\ Q []
  | (x::xs') =>
      (interleave_derive (P.derive x) Q xs')
    \/ (interleave_derive (Q.derive x) P xs')

theorem interleave_iff_interleave_mem (P Q : Lang α) (xs : List α) :
  interleave P Q xs ↔ interleave_mem P Q xs := by
  constructor
  · intro h
    rcases h with ⟨i, hp, hq⟩
    exists (List.get (List.interleaves xs) i)
    and_intros
    · exact List.get_mem xs.interleaves i
    · exact hp
    · exact hq
  · intro h
    rcases h with ⟨p, hp, hpq⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 hp
    rcases hpq with ⟨hpqP, hpqQ⟩
    exists i
    rw [hi]
    and_intros
    · exact hpqP
    · exact hpqQ

theorem interleave_derive_iff_interleave_mem (P Q : Lang α) (xs : List α) :
  interleave_derive P Q xs ↔ interleave_mem P Q xs := by
  induction xs generalizing P Q with
  | nil =>
    constructor
    all_goals
      intro h
      simp [Lang.interleave_derive, Lang.interleave_mem, List.interleaves, List.interleaves] at *
      exact h
  | cons x xs ih =>
    constructor
    · intro h
      rcases h with h | h
      · obtain ⟨p, hp, hpq⟩ := (ih (P.derive x) Q).1 h
        rcases hpq with ⟨hpqP, hpqQ⟩
        exists (x :: p.fst, p.snd)
        and_intros
        · simp [List.interleaves, List.interleaves]
          left
          exact hp
        · exact hpqP
        · exact hpqQ
      · obtain ⟨p, hp, hpq⟩ := (ih (Q.derive x) P).1 h
        have hp' := List.interleaves_mem_swap xs hp
        rcases hpq with ⟨hpqP, hpqQ⟩
        exists (p.snd, x :: p.fst)
        and_intros
        · simp [List.interleaves, List.interleaves]
          right
          exact hp'
        · exact hpqQ
        · exact hpqP
    · intro h
      unfold Lang.interleave_derive at h
      rcases h with ⟨p, h, hp, hq⟩
      simp [List.interleaves, List.interleaves, List.mem_append] at h
      rcases h with h | h
      · rcases h with ⟨fst, snd, hmem, heq⟩
        have hmem' : ∃ p ∈ List.interleaves xs, Lang.derive P x p.1 ∧ Q p.2 := by
          exists (fst, snd)
          and_intros
          · exact hmem
          · rw [←heq] at hp
            rw [←heq] at hq
            simp [Lang.derive]
            exact hp
          · rw [←heq] at hq
            exact hq
        left
        exact (ih (Lang.derive P x) Q).2 hmem'
      · rcases h with ⟨fst, snd, hmem, heq⟩
        have hmem_swap := List.interleaves_mem_swap xs hmem
        have hmem' : ∃ p ∈ List.interleaves xs, Lang.derive Q x p.1 ∧ P p.2 := by
          exists (snd, fst)
          and_intros
          · exact hmem_swap
          · rw [←heq] at hp
            rw [←heq] at hq
            simp [Lang.derive]
            exact hq
          · rw [←heq] at hp
            exact hp
        right
        exact (ih (Lang.derive Q x) P).2 hmem'

theorem interleave_derive_iff_interleave (P Q : Lang α) (xs : List α) :
  interleave_derive P Q xs ↔ interleave P Q xs := by
  rw [interleave_derive_iff_interleave_mem]
  exact Iff.symm (interleave_iff_interleave_mem P Q xs)

theorem interleave_derive_is_interleave (P Q : Lang α) :
  interleave_derive P Q = interleave P Q := by
  funext xs
  exact propext (interleave_derive_iff_interleave P Q xs)

-- Alternative definitions of concat: concat_append.
-- Theorems proving equivalence to alternative definitions of concat.

def concat_append {α: Type} (P : Lang α) (Q : Lang α) : Lang α :=
  fun (xs : List α) =>
    ∃ (xs1 : List α) (xs2 : List α), P xs1 /\ Q xs2 /\ xs = (xs1 ++ xs2)

theorem concat_iff_concat_append:
  concat P Q xs <-> concat_append P Q xs := by
  apply Iff.intro
  case mp =>
    intro h
    cases h with
    | intro n h =>
    cases h with
    | intro hx hy =>
    exists (List.take n xs)
    exists (List.drop n xs)
    apply And.intro hx
    apply And.intro hy
    simp only [List.take_append_drop]
  case mpr =>
    intro h
    cases h with
    | intro xs h =>
    cases h with
    | intro ys h =>
    cases h with
    | intro hx h =>
    cases h with
    | intro hy hxsys =>
    rw [hxsys]
    unfold concat
    exists (Fin.mk (List.length xs) (by
      simp only [List.length_append]
      omega
    ))
    simp only [List.take_left', List.drop_left']
    apply And.intro hx hy

theorem concat_is_concat_append:
  concat P Q = concat_append P Q := by
  funext xs
  rw [concat_iff_concat_append]

-- Alternative definitions of star: star_append, star_flatten and star_append_empty.
-- Theorems proving equivalence to alternative definitions of star.

inductive star_append {α: Type} (R: Lang α): Lang α where
  | zero: star_append R []
  | more: ∀ (x: α) (xs1 xs2 xs: List α),
    xs = (x::xs1) ++ xs2
    -> R (x::xs1)
    -> star_append R xs2
    -> star_append R xs

theorem star_is_star_append:
  star P xs <-> star_append P xs := by
  apply Iff.intro
  case mp =>
    intro h
    unfold star at h
    cases xs with
    | nil =>
      apply star_append.zero
    | cons x xs =>
      simp at h
      obtain ⟨⟨n, hn⟩, ⟨hp, hq⟩⟩ := h
      simp at hp hq
      apply star_append.more x (List.take n xs) (List.drop n xs)
      · rw [List.cons_append]
        simp
      · assumption
      · apply star_is_star_append.mp hq
  case mpr =>
    intro h
    cases xs with
    | nil =>
      unfold star
      simp
    | cons x xs =>
      unfold star
      cases h with
      | more x xs1 xs2 _ hxs hp hq =>
        simp at hxs
        obtain ⟨hx, hxs⟩ := hxs
        subst_vars
        exists (Fin.mk xs1.length (by
          simp
          omega
        ))
        simp
        apply And.intro hp
        apply star_is_star_append.mpr hq
  termination_by xs.length

inductive All {α: Type} (P : α -> Prop) : (List α -> Prop) where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

def star_flatten {α: Type} (P : Lang α) : Lang α :=
  fun (w : List α) =>
    ∃ (ws : List (List α)), (All P ws) /\ w = (List.flatten ws)

inductive star_append_empty {α: Type} (R: Lang α): Lang α where
  | zero: star_append_empty R []
  | more: ∀ (xs1 xs2 xs: List α),
    xs = xs1 ++ xs2
    -> R xs1
    -> star_append_empty R xs2
    -> star_append_empty R xs

theorem star_append_empty_is_star_append {xs: List α}:
  star_append_empty P xs <-> star_append P xs := by
  apply Iff.intro
  case mp =>
    intro h
    induction h with
    | zero =>
      apply star_append.zero
    | more xs1 xs2 xs3 hxs3 hxs hone ih =>
      rw [hxs3]
      cases xs1 with
      | nil =>
        simp
        exact ih
      | cons x1 xs1' =>
        apply star_append.more x1 xs1' xs2
        · rfl
        · exact hxs
        · exact ih
  case mpr =>
    intro h
    induction h with
    | zero =>
      apply star_append_empty.zero
    | more xs1 xs2 xs xs' hxs hone hmore ih =>
      apply star_append_empty.more (xs1::xs2) xs
      · exact hxs
      · exact hone
      · exact ih

theorem star_append_empty_is_star_flatten {xs: List α}:
  star_append_empty P xs <-> star_flatten P xs := by
  apply Iff.intro
  case mp =>
    intro h
    have h' := star_append_empty_is_star_append.mp h
    clear h
    induction h' with
    | zero =>
      unfold star_flatten
      exists []
      apply And.intro
      · apply All.nil
      · simp only [List.flatten_nil]
    | more x xs1 xs2 xs3 hxs hone hmore ih =>
      unfold star_flatten
      unfold star_flatten at ih
      obtain ⟨ws, ih1, ih2⟩ := ih
      subst hxs
      subst ih2
      exists [x :: xs1] ++ ws
      apply And.intro
      · apply All.cons hone
        simp
        exact ih1
      · simp
  case mpr =>
    intro h
    unfold star_flatten at h
    obtain ⟨ws, h1, h2⟩ := h
    induction ws generalizing xs with
    | nil =>
      simp at h2
      rw [h2]
      apply star_append_empty.zero
    | cons w ws ih =>
      cases h1 with
      | cons h1 h1s =>
      have ih' := @ih ws.flatten h1s rfl
      simp at h2
      apply star_append_empty.more w ws.flatten
      · exact h2
      · exact h1
      · exact ih'

theorem star_append_is_star_flatten {xs: List α}:
  star_append P xs <-> star_flatten P xs := by
  rw [<- star_append_empty_is_star_append]
  exact star_append_empty_is_star_flatten

theorem star_is_star_flatten {xs: List α}:
  star P xs <-> star_flatten P xs := by
  rw [<- star_append_is_star_flatten]
  exact star_is_star_append

theorem star_is_star_append_empty {xs: List α}:
  star P xs <-> star_append_empty P xs := by
  rw [star_append_empty_is_star_append]
  exact star_is_star_append

-- basic derive theorems

def derives {α: Type} (R: Lang α) (xs: List α): Lang α :=
  λ ys => R (xs ++ ys)

def derive' {α: Type} (R: Lang α) (x: α): Lang α :=
  derives R [x]

theorem derive_is_derive' {α: Type}:
  @derive α = derive' :=
  rfl

theorem derives_empty_list {α: Type} (R: Lang α):
  derives R [] = R :=
  rfl

theorem derives_strings {α: Type} (R: Lang α) (xs ys: List α):
  derives R (xs ++ ys) = derives (derives R xs) ys :=
  match xs with
  | [] => rfl
  | (x :: xs) => derives_strings (derive R x) xs ys

theorem derives_step {α: Type} (R: Lang α) (x: α) (xs: List α):
  derives R (x :: xs) = derives (derive R x) xs := by
  rw [derive_is_derive']
  simp only [derive']
  rw [<- derives_strings]
  congr

theorem null_derives {α: Type} (R: Lang α) (xs: List α):
  (null ∘ derives R) xs = R xs := by
  unfold derives
  unfold null
  simp only [Function.comp_apply]
  simp only [List.append_nil]

theorem validate {α: Type} (R: Lang α) (xs: List α):
  null (derives R xs) = R xs := by
  unfold derives
  unfold null
  simp only [List.append_nil]

theorem derives_foldl (R: Lang α) (xs: List α):
  (derives R) xs = (List.foldl derive R) xs := by
  revert R
  induction xs with
  | nil =>
    unfold derives
    simp only [List.nil_append, List.foldl_nil, implies_true]
  | cons x xs ih =>
    rw [derive_is_derive']
    simp only [List.foldl_cons, derive']
    intro R
    rw [derives_step]
    rw [ih (derive R x)]
    rw [derive_is_derive']
    simp only [derive']

-- null theorems

theorem null_emptyset {α: Type}:
  @null α emptyset = False :=
  rfl

theorem null_iff_emptyset {α: Type}:
  @null α emptyset <-> False := by
  rw [null_emptyset]

theorem not_null_if_emptyset {α: Type}:
  @null α emptyset → False :=
  null_iff_emptyset.mp

theorem null_iff_emptystr {α: Type}:
  @null α emptystr <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => rfl)

theorem null_if_emptystr {α: Type}:
  @null α emptystr :=
  rfl

theorem null_emptystr {α: Type}:
  @null α emptystr = True := by
  rw [null_iff_emptystr]

theorem null_iff_symbol {σ: Type} {α: Type} {Φ: σ → α → Prop} {s: σ}:
  null (symbol Φ s) <-> False :=
  Iff.intro nofun nofun

theorem not_null_if_symbol {σ: Type} {α: Type} {Φ: σ → α → Prop} {s: σ}:
  null (symbol Φ s) → False :=
  nofun

theorem null_symbol {σ: Type} {α: Type} {Φ: σ → α → Prop} {s: σ}:
  null (symbol Φ s) = False := by
  rw [null_iff_symbol]

theorem null_or {α: Type} {P Q: Lang α}:
  null (or P Q) = ((null P) \/ (null Q)) :=
  rfl

theorem null_iff_or {α: Type} {P Q: Lang α}:
  null (or P Q) <-> ((null P) \/ (null Q)) := by
  rw [null_or]

theorem null_iff_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) <-> ((null P) /\ (null Q)) := by
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro ⟨⟨n, hn⟩, hp, hq⟩
    simp at hn
    subst hn
    simp only [List.take] at hp
    simp only [List.drop] at hq
    exact And.intro hp hq
  case invFun =>
    intro ⟨hp, hq⟩
    unfold concat
    simp only [null, List.length_nil, Nat.reduceAdd, Fin.val_eq_zero, List.take_nil, List.drop_nil,
      exists_const]
    exact And.intro hp hq

theorem null_concat {α: Type} {P Q: Lang α}:
  null (concat P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_concat]

theorem null_iff_interleave_idx {α: Type} {P Q: Lang α}:
  null (interleave P Q) <-> ((null P) /\ (null Q)) := by
  rw [<- Lang.interleave_derive_is_interleave]
  rfl

theorem null_interleave {α: Type} {P Q: Lang α}:
  null (interleave P Q) = ((null P) /\ (null Q)) := by
  rw [null_iff_interleave_idx]

theorem null_iff_star {α: Type} {R: Lang α}:
  null (star R) <-> True :=
  Iff.intro
    (fun _ => True.intro)
    (fun _ => by
      unfold null
      simp only [star]
    )

theorem null_star {α: Type} {R: Lang α}:
  null (star R) = True := by
  rw [null_iff_star]

theorem null_and {α: Type} {P Q: Lang α}:
  null (and P Q) = ((null P) /\ (null Q)) :=
  rfl

theorem null_compliment {α: Type} {R: Lang α}:
  null (compliment R) = null (Not ∘ R) :=
  rfl

-- Theorems: derive

theorem derive_emptyset {α: Type} {a: α}:
  (derive emptyset a) = emptyset :=
  rfl

theorem derive_iff_emptystr {α: Type} {a: α} {w: List α}:
  (derive emptystr a) w <-> emptyset w :=
  Iff.intro nofun nofun

theorem derive_emptystr {α: Type} {a: α}:
  (derive emptystr a) = emptyset := by
  funext
  rw [derive_iff_emptystr]

theorem derive_iff_symbol {α: Type} {Φ: σ → α → Prop} {x: α} {xs: List α}:
  (derive (symbol Φ s) x) xs <-> (onlyif (Φ s x) emptystr) xs := by
  rw [derive_is_derive']
  simp only [derive', derives, List.singleton_append]
  simp only [onlyif, emptystr]
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro D
    match D with
    | Exists.intro x' D =>
    simp only [List.cons.injEq] at D
    match D with
    | And.intro (And.intro hxx' hxs) hpx =>
    rw [<- hxx'] at hpx
    exact And.intro hpx hxs
  case invFun =>
    intro ⟨ hpx , hxs  ⟩
    unfold symbol
    exists x
    simp only [List.cons.injEq, true_and]
    exact And.intro hxs hpx

theorem derive_symbol {α: Type} {Φ: σ → α → Prop} {x: α}:
  (derive (symbol Φ s) x) = (onlyif (Φ s x) emptystr) := by
  funext
  rw [derive_iff_symbol]

theorem derive_or {α: Type} {a: α} {P Q: Lang α}:
  (derive (or P Q) a) = (or (derive P a) (derive Q a)) :=
  rfl

theorem derive_onlyif {α: Type} {a: α} {s: Prop} {P: Lang α}:
  (derive (onlyif s P) a) = (onlyif s (derive P a)) :=
  rfl

theorem derive_iff_star {α: Type} {x: α} {R: Lang α} {xs: List α}:
  (derive (star R) x) xs <-> (concat (derive R x) (star R)) xs := by
  rw [derive_is_derive']
  refine Iff.intro ?toFun ?invFun
  case toFun =>
    intro h
    unfold derive' at h
    unfold derives at h
    simp only [List.cons_append, List.nil_append] at h
    simp only [star] at h
    unfold concat
    obtain ⟨n, h⟩ := h
    simp only [List.length_cons] at h
    exists n
  case invFun =>
    intro h
    unfold concat at h
    obtain ⟨n, h⟩ := h
    simp only [derive', derives, List.cons_append, List.nil_append] at h
    unfold derive'
    unfold derives
    simp only [List.cons_append, List.nil_append]
    simp only [star]
    exists n

theorem derive_star {α: Type} {x: α} {R: Lang α}:
  (derive (star R) x) = (concat (derive R x) (star R)) := by
  funext
  rw [derive_iff_star]

theorem derive_interleave_derive {α: Type} {x: α} {P Q: Lang α}:
  (derive (interleave_derive P Q) x) = (or (interleave_derive (derive P x) Q) (interleave_derive (derive Q x) P)) := by
  rfl

theorem derive_interleave {α: Type} {x: α} {P Q: Lang α}:
  (derive (interleave P Q) x) = (or (interleave (derive P x) Q) (interleave (derive Q x) P)) := by
  rw [<- interleave_derive_is_interleave]
  rw [<- interleave_derive_is_interleave]
  rw [<- interleave_derive_is_interleave]
  rfl

theorem derive_and {α: Type} {a: α} {P Q: Lang α}:
  (derive (and P Q) a) = (and (derive P a) (derive Q a)) :=
  rfl

theorem derive_compliment {α: Type} {x: α} {R: Lang α}:
  (derive (compliment R) x) = Not ∘ (derive R x) :=
  rfl

theorem derive_iff_concat {α: Type} {x: α} {P Q: Lang α} {xs: List α}:
  (derive (concat P Q) x) xs <->
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) xs := by
  rw [derive_is_derive']
  apply Iff.intro
  case mp =>
    intro h
    obtain ⟨n, hp, hq⟩ := h
    simp only [Lang.or, Lang.concat, derive', derives, null, onlyif]
    simp only [List.cons_append, List.nil_append, List.length_cons] at n
    obtain ⟨n, hn⟩ := n
    simp_all only
    cases n with
    | zero =>
      apply Or.inr
      simp_all
    | succ n =>
      apply Or.inl
      simp_all
      exists Fin.mk n (by omega)
  case mpr =>
    simp only [Lang.or, Lang.concat, derive', derives, null, onlyif]
    intro h
    cases h with
    | inl h =>
      obtain ⟨⟨n, hn⟩, hp, hq⟩ := h
      simp_all
      exists Fin.mk (n+1) (by omega)
    | inr h =>
      obtain ⟨hp, hq⟩ := h
      exists Fin.mk 0 (by omega)

theorem derive_concat {α: Type} {x: α} {P Q: Lang α}:
  (derive (concat P Q) x) =
    (or (concat (derive P x) Q) (onlyif (null P) (derive Q x))) := by
  funext
  rw [derive_iff_concat]

-- simplification rules

theorem simp_or_emptyset_l_is_r (r: Lang α):
  or emptyset r = r := by
  unfold or
  simp only [emptyset, false_or]

theorem simp_or_emptyset_r_is_l (r: Lang α):
  or r emptyset = r := by
  unfold or
  simp only [emptyset, or_false]

theorem simp_or_null_l_emptystr_is_l
  (r: Lang α)
  (nullr: null r):
  or r emptystr = r := by
  unfold or
  simp only [emptystr]
  unfold null at nullr
  funext xs
  simp only [eq_iff_iff, or_iff_left_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_emptystr_null_r_is_r
  (r: Lang α)
  (nullr: null r):
  or emptystr r = r := by
  unfold or
  simp only [emptystr]
  unfold null at nullr
  funext xs
  simp only [eq_iff_iff, or_iff_right_iff_imp]
  intro hxs
  rw [hxs]
  exact nullr

theorem simp_or_idemp (r: Lang α):
  or r r = r := by
  unfold or
  funext xs
  apply or_self

theorem simp_or_comm (r s: Lang α):
  or r s = or s r := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h
  case mpr =>
    intro h
    match h with
    | Or.inl h =>
      exact Or.inr h
    | Or.inr h =>
      exact Or.inl h

theorem simp_or_assoc (r s t: Lang α):
  or (or r s) t = or r (or s t) := by
  unfold or
  funext xs
  simp only [eq_iff_iff]
  apply Iff.intro
  · case mp =>
    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        left
        exact h
      | inr h =>
        right
        left
        exact h
    | inr h =>
      right
      right
      exact h
  · case mpr =>
    intro h
    cases h with
    | inl h =>
      left
      left
      exact h
    | inr h =>
      cases h with
      | inl h =>
        left
        right
        exact h
      | inr h =>
        right
        exact h

theorem not_not_intro' {p : Prop} (h : p) : ¬ ¬ p :=
  fun hn : (p → False) => hn h

def onlyif_true {cond: Prop} {l: List α → Prop} (condIsTrue: cond):
  Lang.onlyif cond l = l := by
  unfold Lang.onlyif
  funext xs
  simp only [eq_iff_iff, and_iff_right_iff_imp]
  intro p
  assumption

def onlyif_false {cond: Prop} {l: List α → Prop} (condIsFalse: ¬cond):
  Lang.onlyif cond l = Lang.emptyset := by
  funext xs
  rw [eq_iff_iff]
  apply Iff.intro
  case mp =>
    intro h
    cases h
    case intro condIsTrue lxs =>
    contradiction
  case mpr =>
    intro h
    nomatch h

theorem simp_onlyif_and {α: Type} (cond1 cond2 : Prop) (P : Lang α):
  onlyif (cond1 /\ cond2) P = onlyif cond1 (onlyif cond2 P) := by
  unfold onlyif
  funext xs
  -- aesop?
  simp_all only [eq_iff_iff]
  apply Iff.intro
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [and_self]
