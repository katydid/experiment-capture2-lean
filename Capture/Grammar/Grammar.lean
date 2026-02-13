-- Grammar defines a symbolic regular hedge grammar.

import Capture.Regex.Regex

import Capture.Std.Hedge

-- ## Definition 3.2.3: Regular Hedge Grammar
--   𝐺 = (𝑁, 𝑇, 𝑆, 𝑃)
--   𝑁 a finite set of non-terminals
--   𝑇 a finite set of terminals
--   𝑆 the start symbol of a regular hedge grammar is a regular expression comprising pairs of nonterminals and terminals (a regular expression over N × T)
--   𝑃 a set of production rules of a regular hedge grammar are of the form X → r such that r is a regular expression over N × T.

-- Ref is a non-terminal, where n represents the number of non-terminals
abbrev Ref (n: Nat) := Fin n

abbrev Captured α := Hedge.Node (Nat ⊕ α)

-- symbolic regular hedge grammar
structure Grammar (n: Nat) (φ: Type) (α: Type) where
  start: Regex (φ × Ref n) α
  prods: Vector (Regex (φ × Ref n) α) n

namespace Grammar

def lookup (G: Grammar n φ α) (ref: Ref n): Regex (φ × Ref n) α :=
  Vector.get G.prods ref
