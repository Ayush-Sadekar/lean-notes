example (h: p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (p q r : Prop)
example (hp: p) : p ∨ q := Or.intro_left q hp

example (h: p ∨ q) : q ∨ p :=
  Or.elim h (fun (hp:p) => Or.inr hp) (fun (hq:q) => Or.inl hq)
  -- basically saying: we have p ∨ q, so either p or q is true. That means we can prove q ∨ p by using either proof of p or a proof of q.

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
