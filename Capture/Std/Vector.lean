-- A Vector library that suppliments Lean's standard Vector type with extra definitions and proofs.

import Capture.Std.List

namespace Vector

abbrev nil (α: Type): Vector α 0 := #v[]

-- basic theorems

theorem eq (xs ys: Vector α n) (h: Vector.toList xs = Vector.toList ys): xs = ys := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  obtain ⟨⟨ys⟩, hxs⟩ := ys
  simp_all only [toList_mk]

theorem toList_snoc {xs : Vector α n} :
  (Vector.push xs x).toList = xs.toList ++ [x] := by
  simp only [push, toList_mk, Array.toList_push, List.append_cancel_right_eq]
  rfl

theorem append_nil (xs: Vector α n):
  xs ++ (@Vector.nil α) = Vector.cast (Eq.symm (Nat.add_zero n)) xs := by
  apply eq
  rw [Vector.toList_append]
  simp only [toList_mk, List.append_nil, Nat.add_zero, cast_rfl]

theorem nil_append (xs: Vector α n):
  (@Vector.nil α) ++ xs = Vector.cast (Eq.symm (Nat.zero_add n)) xs := by
  simp only [empty_append, Vector.cast]

theorem toList_length (xs : Vector α l):
  xs.toList.length = l := by
  simp only [length_toList]

-- cast theorems

def cast_assoc (xs: Vector σ (n + n1 + n2)): Vector σ (n + (n1 + n2)) :=
  have h : (n + n1 + n2) = n + (n1 + n2) := by
    rw [<- Nat.add_assoc]
  Vector.cast h xs

theorem cast_toList_nil {α: Type u} (h: 0 = n):
  (Vector.cast (α := α) h #v[]).toList = [] := by
  cases n with
  | zero =>
    rw [Vector.cast_rfl]
    simp only [toList_mk]
  | succ n =>
    contradiction

theorem cast_toList {n: Nat} (xs: Vector α n) (h: n = n2):
  (Vector.cast h xs).toList = xs.toList := by
  subst h
  rw [Vector.cast_rfl]

theorem cast_append (xs: Vector α n1) (ys: Vector α n2):
  Vector.append (Vector.cast h1 xs) ys = Vector.cast h2 (Vector.append xs ys) := by
  subst h1
  rw [Vector.cast_rfl]
  rw [Vector.cast_rfl]

theorem append_cast_r {h: n2 = n3} (xs: Vector α n1) (ys: Vector α n2):
  xs ++ (Vector.cast h ys) = Vector.cast (by subst h; rfl) (xs ++ ys) := by
  subst h
  rw [Vector.cast_rfl]
  rw [Vector.cast_rfl]

theorem get_cast (xs: Vector α n) (h: n = m):
  Vector.get (Vector.cast h xs) i = Vector.get xs ⟨i.val, by omega⟩ := by
  subst h
  simp_all only [Fin.eta]
  rfl

-- cons theorems

def cons (x: α) (xs: Vector α n): Vector α (n + 1) :=
  Vector.cast (by omega) (Vector.append #v[x] xs)

theorem singleton_toList (x: α):
  [x] = #v[x].toList := by
  simp only [toList_mk]

theorem cons_cast {α: Type u} {l n: Nat} (x: α) (xs: Vector α l) (h: l = n):
  (Vector.cons x (Vector.cast h xs)) = Vector.cast (by omega) (Vector.cons x xs) := by
  subst h
  rfl

theorem toList_cons {xs : Vector α n} :
  (Vector.cons x xs).toList = List.cons x xs.toList := by
  rw [← List.singleton_append]
  simp only [Vector.cons]
  rw [<- show #v[x] ++ xs = #v[x].append xs from rfl]
  rw [cast_toList]
  rw [Vector.toList_append]
  rw [<- singleton_toList]

theorem cons_append_list (xs: Vector α n1) (ys: Vector α n2):
  (Vector.cons x (xs ++ ys)).toList = ((Vector.cons x xs) ++ ys).toList := by
  rw [toList_cons]
  rw [toList_append]
  rw [toList_append]
  rw [toList_cons]
  simp only [List.cons_append]

theorem cons_append (xs: Vector α n1) (ys: Vector α n2):
  Vector.cons x (xs ++ ys) = Vector.cast (by omega) ((Vector.cons x xs) ++ ys) := by
  apply eq
  rw [cons_append_list]
  rw [cast_toList]

theorem append_cons_list (xs: Vector α n1) (ys: Vector α n2):
  ((Vector.cons x xs) ++ ys).toList = (Vector.cons x (xs ++ ys)).toList := by
  rw [cons_append_list]

theorem append_cons (xs: Vector α n1) (ys: Vector α n2):
  (Vector.cons x xs) ++ ys = Vector.cast (by omega) (Vector.cons x (xs ++ ys)) := by
  apply eq
  rw [append_cons_list]
  rw [cast_toList]

theorem cons_push:
  (Vector.push (cons x xs) y) = cons x (Vector.push xs y) := by
  apply eq
  rw [toList_cons]
  rw [toList_snoc]
  rw [toList_cons]
  rw [toList_snoc]
  ac_rfl

-- take theorems

theorem take_zero (xs : Vector α n):
  Vector.take xs 0 = #v[] := by
  simp only [Vector.take, Vector.take]
  simp only [Array.extract_zero]

theorem take_nil (i: Nat):
  Vector.take #v[] i = Vector.cast (α := α) (Eq.symm (Nat.min_zero i)) #v[] := by
  induction i with
  | zero =>
    rw [take_zero]
    simp only [Vector.cast_rfl]
  | succ i ih =>
    congr

theorem take_succ_toList (xs: Vector α (n + 1)) (h: k <= n):
  (List.take (k + 1) xs.toList) = (List.take k (xs.toList)) ++ [xs.get ⟨k, by omega⟩] := by
  obtain ⟨⟨xs⟩, hxs⟩ := xs
  simp only [toList_mk]
  have hk : k < xs.length := by
    simp only [List.size_toArray] at hxs
    omega
  have h: (Vector.mk (Array.mk xs) hxs).get ⟨k, (by omega)⟩ = List.get xs ⟨k, hk⟩ := rfl
  rw [h]
  -- aesop?
  simp_all only [List.get_eq_getElem, List.take_append_getElem]

-- drop theorems

theorem drop_zero (xs : Vector α n):
  Vector.drop xs 0 = xs := by
  simp only [Vector.drop]
  simp only [Nat.sub_zero, Array.drop_eq_extract, size_toArray, mk_eq, Array.extract_eq_self_iff,
    Nat.le_refl, and_self, or_true]

theorem drop_nil (i: Nat):
  Vector.drop #v[] i = Vector.cast (α := α) (by omega) #v[] := by
  cases i with
  | zero =>
    rw [drop_zero]
    simp only [Nat.sub_zero, cast_rfl]
  | succ i =>
    simp only [Vector.drop]
    simp only [Array.drop_eq_extract, List.size_toArray, List.length_nil, Array.extract_zero,
      cast_mk]

-- map theorems

theorem map_nil {f: α → β}:
  Vector.map f #v[] = #v[] := by
  simp only [Vector.map]
  simp only [List.map_toArray, List.map_nil]

theorem push_map_list (xs: Vector α l) (f: α → β):
  (Vector.map f (Vector.push xs x)).toList
  = (Vector.push (Vector.map f xs) (f x)).toList := by
  rw [toList_map]
  rw [toList_snoc]
  rw [toList_snoc]
  rw [toList_map]
  simp only [List.map_append, List.map_cons, List.map_nil]

theorem push_map (xs: Vector α l) (f: α → β):
  (Vector.map f (Vector.push xs x))
  = (Vector.push (Vector.map f xs) (f x)) := by
  apply eq
  apply push_map_list

theorem map_toList:
  (Vector.map f xs).toList = List.map f (xs.toList) := by
  simp_all only [Vector.toList_map]

theorem map_cast (xs : Vector α l) (f: α → β) (h: l = n):
  (Vector.map f (Vector.cast h xs)) = Vector.cast h (Vector.map f xs) := by
  apply eq
  rw [map_toList]
  repeat rw [cast_toList]
  rw [map_toList]

theorem map_zip_is_zip_map {α: Type u} {β: Type v} (f: α → β) (xs: Vector α l):
  (Vector.map (fun x => (x, f x)) xs) =
  (Vector.zip xs (Vector.map f xs)) := by
  ext i h : 2
  · simp_all only [Vector.getElem_map, Vector.getElem_zip]
  · simp_all only [Vector.getElem_map, Vector.getElem_zip]

-- take drop theorems

theorem take_append_drop_list (i : Nat) (xs : Vector α l): ((xs.take i) ++ (xs.drop i)).toList = xs.toList := by
  induction i generalizing xs l with
  | zero =>
    simp only [Vector.take_zero]
    simp only [Vector.drop_zero]
    rw [toList_append]
    simp only [toList_mk, List.nil_append]
  | succ i ih =>
    rw [toList_append]
    rw [Vector.toList_take]
    rw [Vector.toList_drop]
    simp only [List.take_append_drop]

theorem take_append_drop (i : Nat) (xs : Vector α l): ((xs.take i) ++ (xs.drop i)) = (Vector.cast (by omega) xs) := by
  apply eq
  rw [take_append_drop_list]
  rw [Vector.cast_toList]

theorem take_append_drop_cast (i : Nat) (xs : Vector α l): Vector.cast (by omega) ((xs.take i) ++ (xs.drop i)) = xs := by
  rw [take_append_drop]
  unfold Vector.cast
  simp only [mk_toArray]

-- get theorems

theorem get_is_getElem {n: Nat} {α: Type u} (xs: Vector α n) (hi: i < n):
  Vector.get xs (Fin.mk i hi) = xs[i] := by
  rfl

theorem append_getElem (xs: Vector α n) (ys: Vector α m) (h: i < n):
  (xs ++ ys)[i] = xs[i] := by
  rw [Vector.getElem_append_left]

theorem append_get (xs: Vector α n) (ys: Vector α m) (h: i < n):
  Vector.get (xs ++ ys) ⟨i, by omega⟩ = Vector.get xs ⟨i, h⟩ := by
  rw [get_is_getElem]
  rw [get_is_getElem]
  rw [append_getElem]

theorem take_get (xs: Vector α (n + m)) (h1: i < n):
  Vector.get (Vector.take xs n) ⟨i, (by omega)⟩ = Vector.get xs ⟨i, h⟩ := by
  have h := take_append_drop_cast (xs := xs) (i := n)
  rw [<- h]
  rw [Vector.get_cast]
  simp only
  rw [append_get]
  rw [h]

theorem push_getElem {n: Nat} {α: Type u} (xs: Vector α n) (y: α):
  (Vector.push xs y)[n] = y := by
  simp only [push, Array.push, List.concat_eq_append, getElem_mk, List.getElem_toArray,
    Array.length_toList, size_toArray, Nat.le_refl, List.getElem_append_right, Nat.sub_self,
    List.getElem_cons_zero]

theorem push_get {n: Nat} {α: Type u} (xs: Vector α n) (y: α):
  Vector.get (Vector.push xs y) (Fin.mk n (by omega)) = y := by
  rw [get_is_getElem]
  rw [push_getElem]
