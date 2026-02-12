-- We define a map function for regular expression and using it to
-- define instances of Functor and LawfulFunctor.

import Capture.Regex.Regex

def Regex.map (r: Regex α) (f: α → β): Regex β := match r with
  | emptyset => emptyset | emptystr => emptystr | star r1 => star (map r1 f)
  | symbol s => symbol (f s) | or r1 r2 => or (map r1 f) (map r2 f)
  | concat r1 r2 => concat (map r1 f) (map r2 f)
  | interleave r1 r2 => interleave (map r1 f) (map r2 f)
  | and r1 r2 => and (map r1 f) (map r2 f)
  | compliment r1 => compliment (map r1 f)

namespace Regex

theorem map_id (r: Regex α):
  map r (fun s => s) = r := by
  induction r with
  | emptyset =>
    simp only [map]
  | emptystr =>
    simp only [map]
  | symbol =>
    simp only [map]
  | or r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [map]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | and r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    simp only [map]
    rw [ih1]

theorem map_map (r: Regex α) (f: α → β) (g: β → σ):
  map (map r f) g = map r (fun r' => g (f r')) := by
  induction r with
  | emptyset =>
    simp only [map]
  | emptystr =>
    simp only [map]
  | symbol =>
    simp only [map]
  | or r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [map]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | and r1 r2 ih1 ih2 =>
    simp only [map]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    simp only [map]
    rw [ih1]

theorem map_null {σ} (Φ: σ → Bool) (r: Regex σ):
  (map r (fun s => (s, Φ s))).null = r.null := by
  induction r with
  | emptyset =>
    simp only [map, Regex.null]
  | emptystr =>
    simp only [map, Regex.null]
  | symbol _ =>
    simp only [map, Regex.null]
  | or r1 r2 ih1 ih2 =>
    simp only [map, Regex.null]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [map, Regex.null]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [map, Regex.null]
  | interleave r1 r2 ih1 ih2 =>
    simp only [map, Regex.null]
    rw [ih1]
    rw [ih2]
  | and r1 r2 ih1 ih2 =>
    simp only [map, Regex.null]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    simp only [map, Regex.null]
    rw [ih1]

instance: Functor Regex where
  map f := Regex.map (f := f)

instance: LawfulFunctor Regex where
  map_const {α β}: (Functor.mapConst : α → Regex β → Regex α) = Functor.map ∘ Function.const β := by
    unfold Functor.mapConst
    unfold instFunctor
    unfold Function.const
    unfold Functor.map
    simp only
  id_map {α} (x : Regex α) : id <$> x = x := by apply map_id
  comp_map {α β γ} (f : α → β) (g : β → γ) (r : Regex α) : (g ∘ f) <$> r = g <$> f <$> r := by
    unfold Functor.map
    unfold instFunctor
    simp only
    rw [map_map]
    rfl
