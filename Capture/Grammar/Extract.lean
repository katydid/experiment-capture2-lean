import Capture.Regex.Regex
import Capture.Grammar.Grammar

import Capture.Std.Hedge


def extract (x: Regex σ (Captured α)): Hedge (Nat ⊕ α) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Regex.emptyset => []
  | Regex.emptystr => []
  -- should never be encountered, since tree is not nullable.
  | Regex.symbol _ => []
  | Regex.matched c => [c]
  | Regex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.null
    then extract y
    else extract z
  | Regex.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Regex.star _ => []
    -- Ignore group, this group will be extracted later by extractGroups.
  | Regex.group n y => [Hedge.Node.mk (Sum.inl n) (extract y)]

def extractHedge (xs: Hedge (Nat ⊕ α)): Hedge α :=
  match xs with
  | [] => []
  | Hedge.Node.mk (Sum.inl _id) children::xs' =>
    extractHedge children ++ extractHedge xs'
  | Hedge.Node.mk (Sum.inr a) children::xs' =>
    Hedge.Node.mk a (extractHedge children)::extractHedge xs'

def extractGroups' (xs: Hedge (Nat ⊕ α)): List (Nat × Hedge α) :=
  match xs with
  | [] => []
  | Hedge.Node.mk (Sum.inl id) children::xs' =>
    (id, extractHedge children) :: extractGroups' xs'
  | Hedge.Node.mk (Sum.inr _a) children::xs' =>
    extractGroups' children ++ extractGroups' xs'

def extractPathGroups' (xs: Hedge (Nat ⊕ α)): List (Nat × Hedge α) :=
  match xs with
  | [] => []
  | Hedge.Node.mk (Sum.inl id) children::xs' =>
    (id, extractHedge children) :: extractPathGroups' xs'
  | Hedge.Node.mk (Sum.inr a) children::xs' =>
    List.map (fun (id, h) => (id, [Hedge.Node.mk a h])) (extractPathGroups' children) ++ extractPathGroups' xs'

def extractGroups (x: Regex σ (Captured α)): List (Nat × Hedge α) :=
  extractGroups' (extract x)

def extractPathGroups (x: Regex σ (Captured α)): List (Nat × Hedge α) :=
  extractPathGroups' (extract x)
