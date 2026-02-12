-- A Decidable library that suppliments Lean's standard Decidable definitions.

def decideRel (p : α → β → Prop) [DecidableRel p]: α → β → Bool :=
  fun a b => decide (p a b)

instance {α: Type} {β: α -> Type}
  [DecidableEq α] [∀ a, DecidableEq (β a)]
  : DecidableEq (Σ (a: α), β a) :=
  fun x y =>
    let ⟨x1, x2⟩ := x
    let ⟨y1, y2⟩ := y
    if h: x1 = y1
    then
      by
        subst h
        by_cases h': y2 = x2
        · apply Decidable.isTrue
          congr
          rw [h']
        · apply Decidable.isFalse
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
          intro h''
          subst h''
          apply h'
          rfl
    else Decidable.isFalse (by
      simp only [Sigma.mk.injEq, not_and]
      intro h'
      contradiction
    )
