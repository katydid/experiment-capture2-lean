import Capture.Regex.Regex
import Capture.Grammar.Grammar
import Capture.Grammar.Extract

import Capture.Std.Hedge

def neutralize (x: Regex (φ × Ref n) α): Regex (φ × Ref n) α :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptystr
  | Regex.matched a => Regex.matched a
  | Regex.symbol _ => Regex.emptyset
  | Regex.or y z => Regex.or (neutralize y) (neutralize z)
  | Regex.concat y z => Regex.concat (neutralize y) (neutralize z)
  | Regex.star y => Regex.star (neutralize y)
  | Regex.group id y => Regex.group id (neutralize y)

def derive (G: Grammar n φ (Captured α)) (Φ: φ -> α -> Bool) (x: Regex (φ × Ref n) (Captured α)) (node: Hedge.Node α): Regex (φ × Ref n) (Captured α) :=
  match x with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  -- remember matched is just epsilon, so has the same derivative.
  | Regex.matched _ => Regex.emptyset
  | Regex.symbol (labelPred, ref) =>
    match node with
    | Hedge.Node.mk label children =>
      if Φ labelPred label
      then
        let dchild := List.foldl (derive G Φ) (G.lookup ref) children
        if dchild.null
        then Regex.matched (Hedge.Node.mk (Sum.inr label) (extract dchild))
        else Regex.emptyset
      else Regex.emptyset
  | Regex.or y z => Regex.or (derive G Φ y node) (derive G Φ z node)
  | Regex.concat y z =>
    if Regex.null y
    then Regex.or
      (Regex.concat (derive G Φ y node) z)
      -- A difference from the usual derive algorithm:
      -- To preserve the capture information in the nullable expression y,
      -- instead of (derive z node), we write:
      (Regex.concat (neutralize y) (derive G Φ z node))
    else Regex.concat (derive G Φ y node) z
  | Regex.star y => Regex.concat (derive G Φ y node) x
  | Regex.group n y =>
    Regex.group n (derive G Φ y node)
  termination_by (node, x)
  decreasing_by
    · sorry -- symbol
    · sorry -- left or
    · sorry -- right or
    · sorry -- left concat
    · sorry -- right concat
    · sorry -- left concat not null
    · sorry -- star
    · sorry -- group

def captures (G: Grammar n φ (Captured α)) (Φ: φ -> α -> Bool) (x: Regex (φ × Ref n) (Captured α)) (nodes: Hedge α): Option (List (Nat × Hedge α)) :=
  let dx := List.foldl (derive G Φ) x nodes
  if dx.null
  then Option.some (extractGroups dx)
  else Option.none

def capture [Ord α] (G: Grammar n φ (Captured α)) (Φ: φ -> α -> Bool) (name: Nat) (x: Regex (φ × Ref n) (Captured α)) (nodes: Hedge α): Option (Hedge α) :=
  match captures G Φ x nodes with
  | Option.none => Option.none
  | Option.some cs =>
  let hedges := List.filterMap
    (fun (name', forest) =>
      if name = name'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort hedges (le := fun x y => (Ord.compare x y).isLE)))

-- capturePaths is just like captures, except extractGroups is replaced by extractPathGroups
def capturePaths (G: Grammar n φ (Captured α)) (Φ: φ -> α -> Bool) (x: Regex (φ × Ref n) (Captured α)) (forest: Hedge α): Option (List (Nat × Hedge α)) :=
  let dx := List.foldl (derive G Φ) x forest
  if dx.null
  then Option.some (extractPathGroups dx)
  else Option.none

-- capturePath is just like capture, except captures is replaced by capturePaths
def capturePath [Ord α] (G: Grammar n φ (Captured α)) (Φ: φ -> α -> Bool) (name: Nat) (x: Regex (φ × Ref n) (Captured α)) (forest: Hedge α): Option (Hedge α) :=
  match capturePaths G Φ x forest with
  | Option.none => Option.none
  | Option.some cs =>
  let forests := List.filterMap
    (fun (name', forest) =>
      if name = name'
      then Option.some forest
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort forests (le := fun x y => (Ord.compare x y).isLE)))

def Regex.char (c: Char): Regex (Char × Ref (n + 1)) (Captured Char) :=
  Regex.symbol (c, 0)

instance {α : Type u} [DecidableEq α] : DecidableEq (Option α) := inferInstance

def treeString (s: String): Hedge Char :=
  List.map (fun c => Hedge.Node.mk c []) s.toList

def runCaptures (G: Grammar n Char (Captured Char)) (xs: Hedge Char): Option (List (Nat × Hedge Char)) :=
  captures G (· == ·) G.start xs

def runCapture (id: Nat) (G: Grammar n Char (Captured Char)) (xs: Hedge Char): Option (Hedge Char) :=
  capture G (· == ·) id G.start xs

def runCapturePath (id: Nat) (G: Grammar n Char (Captured Char)) (xs: Hedge Char): Option (Hedge Char) :=
  capturePath G (· == ·) id G.start xs

-- no group
#guard runCaptures
  (Grammar.mk (Regex.char 'a') #v[Regex.emptystr])
  (treeString "a")
  == Option.some []

-- simplest group
#guard runCaptures
  (Grammar.mk (Regex.group 1 (Regex.char 'a')) #v[Regex.emptystr])
  (treeString "a")
  == Option.some [(1, [Hedge.Node.mk 'a' []])]

#guard runCapture 1 (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1 (Regex.char 'b')))
    (Regex.star (Regex.char 'a'))
  ) #v[Regex.emptystr])
  (treeString "aaabaaa")
  == Option.some (treeString "b")

#guard runCapture 1 (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1 (Regex.star (Regex.char 'b'))))
    (Regex.star (Regex.char 'a'))
  ) #v[Regex.emptystr])
  (treeString "aaabbbaaa")
  == Option.some (treeString "bbb")

#guard runCapture 1 (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1
      (Regex.or
        (Regex.star (Regex.char 'b'))
        (Regex.star (Regex.char 'c'))
      )
    ))
    (Regex.star (Regex.char 'a'))
  ) #v[Regex.emptystr])
  (treeString "aaacccaaa")
  == Option.some (treeString "ccc")

#guard runCapture 1 (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1
      (Regex.or
        (Regex.star (Regex.char 'b'))
        (Regex.concat (Regex.char 'b') (Regex.star (Regex.char 'c')))
      )
    ))
    (Regex.star (Regex.char 'a'))
  ) #v[Regex.emptystr])
  (treeString "aaabccaaa")
  == Option.some (treeString "bcc")

#guard runCapture 1 (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.group 1 (Regex.char 'b')))
    (Regex.star (Regex.char 'a'))
  ) #v[Regex.emptystr])
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

#guard runCapture 1 (Grammar.mk (Regex.group 1 (Regex.symbol ('b', 1)))
    #v[Regex.emptystr, (Regex.char 'c')]
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

#guard runCapture 1
  (Grammar.mk (Regex.symbol ('b', 1)) #v[Regex.emptystr, Regex.group 1 (Regex.char 'c')])
  [
    Hedge.Node.mk 'b' [
      Hedge.Node.mk 'c' [],
    ],
  ]
  == Option.some [
    Hedge.Node.mk 'c' []
  ]

#guard runCapturePath 1
  (Grammar.mk (Regex.symbol ('b', 1)) #v[Regex.emptystr, Regex.group 1 (Regex.char 'c')])
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

#guard runCapture 1
  (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.symbol ('b', 1)))
    (Regex.star (Regex.char 'a'))
  )
  #v[Regex.emptystr, (Regex.concat (Regex.concat
        (Regex.star (Regex.char 'a'))
        (Regex.group 1 (Regex.char 'c')))
        (Regex.star (Regex.char 'a')))
    ]
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

#guard runCapturePath 1
  (Grammar.mk (Regex.concat (Regex.concat
    (Regex.star (Regex.char 'a'))
    (Regex.symbol ('b', 1)))
    (Regex.star (Regex.char 'a'))
  )
  #v[Regex.emptystr, (Regex.concat (Regex.concat
        (Regex.star (Regex.char 'a'))
        (Regex.group 1 (Regex.char 'c')))
        (Regex.star (Regex.char 'a')))
    ]
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
