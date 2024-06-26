-- chp 3
variable (p q r : Prop)

-- commutativity of and ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun h : p ∧ q =>
      have hp : p := h.left
      have hq : q := h.right
      show q ∧ p from ⟨hq, hp⟩)
    (fun h : q ∧ p =>
      have hp : p := h.right
      have hq : q := h.left
      show p ∧ q from ⟨hp, hq⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h 
        (fun hp : p =>
          show q ∨ p from Or.inr hp)
        (fun hq : q =>
          show q ∨ p from Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h 
        (fun hq : q =>
          show p ∨ q from Or.inr hq)
        (fun hp : p =>
          show p ∨ q from Or.inl hp))

-- associativity of and ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      have hp : p := h.left.left
      have hq : q := h.left.right
      have hr : r := h.right
      show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩)
    (fun h : p ∧ (q ∧ r) => 
      have hp : p := h.left
      have hq : q := h.right.left
      have hr : r := h.right.right
      show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (fun hpq : p ∨ q =>
          Or.elim hpq
            (fun hp : p => Or.inl hp)
            (fun hq : q => Or.inr (Or.inl hq)))
        (fun hr : r => Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h 
        (fun hp : p => Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          Or.elim hqr
            (fun hq : q => Or.inl (Or.inr hq))
            (fun hr : r => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h₁ : p ∧ (q ∨ r) =>
      have hp : p := h₁.left
      have hqr : q ∨ r := h₁.right
      show (p ∧ q) ∨ (p ∧ r) from
        Or.elim hqr
          (fun hq : q => Or.inl (⟨hp, hq⟩))
          (fun hr : r => Or.inr (⟨hp, hr⟩)))
    (fun h₂ : (p ∧ q) ∨ (p ∧ r) =>
      h₂.elim
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq ⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h₁ : p ∨ (q ∧ r) =>
      h₁.elim
        (fun hp : p => 
        show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr : q ∧ r =>
        show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hqr.left, Or.inr hqr.right⟩))

    (fun h₂ : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := h₂.left
      have hpr : p ∨ r := h₂.right
      show p ∨ (q ∧ r) from 
        Or.elim hpq
          (fun hp : p => Or.inl hp)
          (fun hq : q => Or.inr hq)
        Or.elim hpr
          (fun hp : p => Or.inl hp)
          (fun hr : r => Or.inr hr))


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) => 
      show p ∧ q → r from
        (fun hp : p =>
          (fun hq : q =>
            (fun hr : r =>
              (fun (fun hpq : p ∧ q => ⟨hp,hq⟩) =>
                (fun hhr : r => hr))))))
    (fun h : p ∧ q → r =>
      show p → (q → r) from sorry)





