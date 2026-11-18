example (h: p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (p q r : Prop)
example (hp: p) : p ∨ q := Or.intro_left q hp

example (h: p ∨ q) : q ∨ p :=
  Or.elim h (fun (hp:p) => Or.inr hp) (fun (hq:q) => Or.inl hq)
  -- basically saying: we have p ∨ q, so either p or q is true. That means we can prove q ∨ p by using either proof of p or a proof of q.

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
-- using the absurd thing. We have hq to prove p, so now it becomes 'absurd p ¬p' which follows the 'absurd' keyword usage

-- exercise 1
theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

-- copy pasted proof from (h: p ∨ q) : q ∨ p to solve each case of the iff
example : p ∨ q ↔ q ∨ p :=
  -- cases: first: if given p or q, then q or p. Second: do flip case of first
  Iff.intro
    (fun h : p ∨ q => show q ∨ p from Or.elim h (fun (hp:p) => Or.inr hp) (fun (hq:q) => Or.inl hq))
    (fun h : q ∨ p => show p ∨ q from Or.elim h (fun (hq:q) => Or.inr hq) (fun (hp:p) => Or.inl hp))

-- less verbose version: `fun hp => Or.inr hp` is just `Or.inr`, and Iff.intro already tells Lean the types
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => Or.elim h Or.inr Or.inl)
    (fun h => Or.elim h Or.inr Or.inl)


-- BOOMMMM
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  -- need another Iff.intro to solve this.
  -- Case 1: if (p ∧ q) ∧ r then p ∧ (q ∧ r). Second case flips this. If I can solve the first case, second shouldn't be bad
  Iff.intro
    (fun h : (p ∧ q) ∧ r => And.intro (And.left h.left) (And.intro (And.right h.left) h.right))
    (fun h : p ∧ (q ∧ r) => And.intro (And.intro h.left (And.left h.right)) (And.right h.right))

-- I hate associativity
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (fun hpq => Or.elim hpq
          (fun hp => Or.inl hp)
          (fun hq => Or.inr (Or.inl hq))
        )
        fun hr => Or.inr (Or.inr hr)
    )
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h
        (fun hp => Or.inl (Or.inl hp)) -- notice that we're dealing with the cases the way each term appears in h. So have to do p first before unfolding the (q ∨ r)
        (fun hqr => Or.elim hqr
          (fun hq => Or.inl (Or.inr hq))
          (fun hr => Or.inr hr)
        )
    )

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h: p ∧ (q ∨ r) =>
      Or.elim h.right
        (fun hq => Or.inl (And.intro h.left hq))
        (fun hr => Or.inr (And.intro h.left hr))
    )
    (fun h: (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq => And.intro hpq.left (Or.inl hpq.right))
        (fun hpr => And.intro hpr.left (Or.inr hpr.right))
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      Or.elim h
        (fun hp => And.intro (Or.inl hp) (Or.inl hp))
        (fun hqr =>
          And.intro (Or.inr hqr.left) (Or.inr hqr.right)
        )
    ) -- didn't know I could maneuver like this. Can decompose an outer statement wherever I want I guess.
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim h.left (fun hp => Or.inl hp) (fun hq =>
        Or.elim h.right
          (fun hp => Or.inl hp)
          (fun hr => Or.inr (And.intro hq hr)))
    )
