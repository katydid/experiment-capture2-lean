inductive Hedge.Node (α: Type) where
  | mk (label: α) (children: List (Hedge.Node α))
  deriving BEq, Ord, Repr, Hashable

abbrev Hedge α := List (Hedge.Node α)
