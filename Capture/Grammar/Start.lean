import Capture.Std.Hedge

inductive Tegex α where
  | emptyset
  | epsilon
  -- Cegex.matched is extended to trees
  | matched (tok: α) (childExpr: Tegex α)
  | tree (tok: α) (childExpr: Tegex α)
  | or (y z: Tegex α)
  | concat (y z: Tegex α)
  | star (y: Tegex α)
  -- group is a copy of Cegex.group without the captured string.
  | group (id: Nat) (x: Tegex α)
  deriving DecidableEq, Hashable

def Tegex.nullable (x: Tegex α): Bool :=
  match x with
  | Tegex.emptyset => false
  | Tegex.epsilon => true
  -- matched is technically the same as epsilon, except that it stores the matched token and childExpr.
  | Tegex.matched _ _ => true
  | Tegex.tree _ _ => false
  | Tegex.or y z => nullable y || nullable z
  | Tegex.concat y z => nullable y && nullable z
  | Tegex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | Tegex.group _ y => nullable y

-- neutralize replaces all tree operators with emptyset.
-- It is used when deriving concat.
-- This way we do not lose capture information on nullable expressions.
def neutralize (x: Tegex α): Tegex α :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | Tegex.epsilon => Tegex.epsilon
  | Tegex.matched tok childExpr => Tegex.matched tok (neutralize childExpr)
  | Tegex.tree _ _ => Tegex.emptyset
  | Tegex.or y z => Tegex.or (neutralize y) (neutralize z)
  | Tegex.concat y z => Tegex.concat (neutralize y) (neutralize z)
  | Tegex.star y => Tegex.star (neutralize y)
  | Tegex.group id y => Tegex.group id (neutralize y)

partial def derive [DecidableEq α] (x: Tegex α) (tree: Hedge.Node α): Tegex α :=
  match x with
  | Tegex.emptyset => Tegex.emptyset
  | Tegex.epsilon => Tegex.emptyset
  -- remember matched is just epsilon, so has the same derivative.
  | Tegex.matched _ _ => Tegex.emptyset
  | Tegex.tree tok' childExpr =>
    match tree with
    | Hedge.Node.mk tok children =>
      if tok' = tok
      then
        let dchild := List.foldl derive childExpr children
        if dchild.nullable
        then Tegex.matched tok' dchild
        else Tegex.emptyset
      else Tegex.emptyset
  | Tegex.or y z => Tegex.or (derive y tree) (derive z tree)
  | Tegex.concat y z =>
    if Tegex.nullable y
    then Tegex.or
      (Tegex.concat (derive y tree) z)
      -- A difference from the usual derive algorithm:
      -- To preserve the capture information in the nullable expression y,
      -- instead of (derive z tree), we write:
      (Tegex.concat (neutralize y) (derive z tree))
    else Tegex.concat (derive y tree) z
  | Tegex.star y => Tegex.concat (derive y tree) x
  | Tegex.group n y =>
    Tegex.group n (derive y tree)

def extract (x: Tegex α): Hedge α :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  -- should never be encountered, since tree is not nullable.
  | Tegex.tree _ _ => []
  | Tegex.matched tok childExpr => [Hedge.Node.mk tok (extract childExpr)]
  | Tegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extract y
    else extract z
  | Tegex.concat y z =>
    extract y ++ extract z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Tegex.star _ => []
    -- Ignore group, this group will be extracted later by extractGroups.
  | Tegex.group _ y => extract y

def extractGroups (x: Tegex α): List (Nat × Hedge α) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  -- should never be encountered, since tree is not nullable.
  | Tegex.tree _ _ => []
  -- There may be groups in the childExpr that needs to be extracted.
  | Tegex.matched _ childExpr => extractGroups childExpr
  | Tegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extractGroups y
    else extractGroups z
  | Tegex.concat y z =>
    extractGroups y ++ extractGroups z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported, which we do not want under POSIX semantics.
  | Tegex.star _ => []
    -- extract the forest for the single group id
  | Tegex.group id y => (id, extract y) :: extractGroups y


def captures [DecidableEq α] (x: Tegex α) (nodes: Hedge α): Option (List (Nat × Hedge α)) :=
  let dx := List.foldl derive x nodes
  if dx.nullable
  then Option.some (extractGroups dx)
  else Option.none

def capture [DecidableEq α] [Ord α] (name: Nat) (x: Tegex α) (nodes: Hedge α): Option (Hedge α) :=
  match captures x nodes with
  | Option.none => Option.none
  | Option.some cs =>
  let hedges := List.filterMap
    (fun (name', forest) =>
      if name = name'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort hedges (le := fun x y => (Ord.compare x y).isLE)))

-- extractPathGroups is just like extractGroups, except for the Tregex.matched case.
-- This now records the full path if a group below was matched.
def extractPathGroups [DecidableEq α] (x: Tegex α): List (Nat × Hedge α) :=
  match x with
  | Tegex.emptyset => []
  | Tegex.epsilon => []
  | Tegex.tree _ _ => []
  | Tegex.matched tok childExpr =>
  -- NEW: The only line that is different from extractGroups
    List.map (fun (id, children) => (id, [Hedge.Node.mk tok children])) (extractPathGroups childExpr)
  | Tegex.or y z =>
    if y.nullable
    then extractPathGroups y
    else extractPathGroups z
  | Tegex.concat y z =>
    extractPathGroups y ++ extractPathGroups z
  | Tegex.star _ => []
  | Tegex.group id y => (id, extract y) :: extractPathGroups y

-- capturePaths is just like captures, except extractGroups is replaced by extractPathGroups
def capturePaths [DecidableEq α] (x: Tegex α) (forest: Hedge α): Option (List (Nat × Hedge α)) :=
  let dx := List.foldl derive x forest
  if dx.nullable
  then Option.some (extractPathGroups dx)
  else Option.none

-- capturePath is just like capture, except captures is replaced by capturePaths
def capturePath [DecidableEq α] [Ord α] (name: Nat) (x: Tegex α) (forest: Hedge α): Option (Hedge α) :=
  match capturePaths x forest with
  | Option.none => Option.none
  | Option.some cs =>
  let forests := List.filterMap
    (fun (name', forest) =>
      if name = name'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort forests (le := fun x y => (Ord.compare x y).isLE)))

def Tegex.char (c: Char): Tegex Char :=
  (Tegex.tree c Tegex.epsilon)

instance {α : Type u} [DecidableEq α] : DecidableEq (Option α) := inferInstance

def treeString (s: String): Hedge Char :=
  List.map (fun c => Hedge.Node.mk c []) s.toList

-- no group
#guard captures (Tegex.char 'a') (treeString "a")
  == Option.some []

-- simplest group
#guard captures (Tegex.group 1 (Tegex.char 'a')) (treeString "a")
  == Option.some [(1, [Hedge.Node.mk 'a' []])]

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.char 'b')))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaabaaa")
  == Option.some (treeString "b")


#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.star (Tegex.char 'b'))))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaabbbaaa")
  == Option.some (treeString "bbb")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1
      (Tegex.or
        (Tegex.star (Tegex.char 'b'))
        (Tegex.star (Tegex.char 'c'))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaacccaaa")
  == Option.some (treeString "ccc")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1
      (Tegex.or
        (Tegex.star (Tegex.char 'b'))
        (Tegex.concat (Tegex.char 'b') (Tegex.star (Tegex.char 'c')))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  (treeString "aaabccaaa")
  == Option.some (treeString "bcc")

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.group 1 (Tegex.char 'b')))
    (Tegex.star (Tegex.char 'a'))
  )
  [
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'b' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' []
  ]
  == Option.some [
    Hedge.Node.mk 'b' []
  ]

#guard capture 1
    (Tegex.group 1 (Tegex.tree 'b'
      (Tegex.tree 'c' Tegex.epsilon))
    )
  [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' [],
    ],
  ]
  == Option.some [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' []
    ]
  ]

#guard capture 1
    (Tegex.tree 'b'
      (Tegex.group 1 (Tegex.tree 'c' Tegex.epsilon))
    )
  [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' [],
    ],
  ]
  == Option.some [
    Hedge.Node.mk 'c' []
  ]

#guard capturePath 1
    (Tegex.tree 'b'
      (Tegex.group 1 (Tegex.tree 'c' Tegex.epsilon))
    )
  [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' [],
    ],
  ]
  == Option.some [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' []
    ]
  ]

#guard capture 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.tree 'b'
      (Tegex.concat (Tegex.concat
        (Tegex.star (Tegex.char 'a'))
        (Tegex.group 1 (Tegex.char 'c')))
        (Tegex.star (Tegex.char 'a'))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  [
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'c' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
    ],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' []
  ]
  == Option.some [
    Hedge.Node.mk 'c' []
  ]

#guard capturePath 1 (Tegex.concat (Tegex.concat
    (Tegex.star (Tegex.char 'a'))
    (Tegex.tree 'b'
      (Tegex.concat (Tegex.concat
        (Tegex.star (Tegex.char 'a'))
        (Tegex.group 1 (Tegex.char 'c')))
        (Tegex.star (Tegex.char 'a'))
      )
    ))
    (Tegex.star (Tegex.char 'a'))
  )
  [
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'c' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
      Hedge.Node.mk 'a' [],
    ],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' [],
    Hedge.Node.mk 'a' []
  ]
  == Option.some [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' []
    ]
  ]
