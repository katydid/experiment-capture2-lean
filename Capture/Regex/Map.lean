-- We define a map function for regular expression and using it to
-- define instances of Functor and LawfulFunctor.

import Capture.Regex.Regex

def Regex.map (r: Regex σ₁ α) (f: σ₁ → σ₂): Regex σ₂ α := match r with
  | emptyset => emptyset
  | emptystr => emptystr
  | matched a => matched a
  | symbol s => symbol (f s)
  | or r1 r2 => or (map r1 f) (map r2 f)
  | concat r1 r2 => concat (map r1 f) (map r2 f)
  | star r1 => star (map r1 f)
  | group n r1 => group n (map r1 f)

namespace Regex

theorem map_id (r: Regex σ₁ α):
  map r (fun s => s) = r := by
  induction r with
  | emptyset =>
    simp only [map]
  | emptystr =>
    simp only [map]
  | matched _ =>
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
  | group _ r1 ih1 =>
    simp only [map]
    rw [ih1]

theorem map_map (r: Regex σ₁ α) (f: σ₁ → σ₂) (g: σ₂ → σ₃):
  map (map r f) g = map r (fun r' => g (f r')) := by
  induction r with
  | emptyset =>
    simp only [map]
  | emptystr =>
    simp only [map]
  | matched _ =>
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
  | group _ r1 ih1 =>
    simp only [map]
    rw [ih1]

theorem map_null {σ} (Φ: σ → Bool) (r: Regex σ α):
  (map r (fun s => (s, Φ s))).null = r.null := by
  induction r with
  | emptyset =>
    simp only [map, Regex.null]
  | emptystr =>
    simp only [map, Regex.null]
  | matched _ =>
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
  | group _ r1 ih1 =>
    simp only [map, Regex.null]
    rw [ih1]
