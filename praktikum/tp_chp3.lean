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
          (fun hq : q => 
            Or.elim hpr
              (fun hp : p => Or.inl hp)
              (fun hr : r => Or.inr (⟨hq, hr⟩))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) => 
      (fun hpq : p ∧ q =>
        let ⟨hp, hq⟩ := hpq
        h hp hq))
    (fun h : p ∧ q → r =>
      (fun hp : p =>
        (fun hq : q =>
          h ⟨hp,hq⟩)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h₁ : (p ∨ q) → r =>
      And.intro
        (fun hp => h₁ (Or.inl hp))
        (fun hq => h₁ (Or.inr hq)))
    (fun h₂ : (p → r) ∧ (q → r) => 
      (fun hpq : p ∨ q =>
        hpq.elim
          (fun hp : p => h₂.left hp)
          (fun hq : q => h₂.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h₁ : ¬(p ∨ q) =>
      And.intro
        (fun hp : p => show False from h₁ (Or.inl hp))
        (fun hq : q => show False from h₁ (Or.inr hq)))
    (fun h₂ : ¬p ∧ ¬q =>
      (fun hpq : p ∨ q =>
        hpq.elim
          (fun hp : p => show False from h₂.left hp)
          (fun hq : q => show False from h₂.right hq)))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun h : ¬p ∨ ¬q =>
    (fun hpq : p ∧ q =>
      h.elim
        (fun hnp : ¬p => show False from False.elim (hnp hpq.left))
        (fun hnq : ¬q => show False from False.elim (hnq hpq.right))))

example : ¬(p ∧ ¬p) :=
  (fun hpnp : p ∧ ¬p =>
    have hp := hpnp.left
    have hnp := hpnp.right
    show False from absurd hp hnp)

example : p ∧ ¬q → ¬(p → q) :=
  (fun hpnq : p ∧ ¬q =>
    (fun hpq : p → q =>
      show False from hpnq.right (hpq hpnq.left)))

example : ¬p → (p → q) :=
  (fun hnp : ¬p =>
    (fun hp : p => False.elim (hnp hp)))

example : (¬p ∨ q) → (p → q) :=
  (fun hnpq : ¬p ∨ q =>
    (fun hp : p =>
      hnpq.elim
        (fun hnp : ¬p => False.elim (hnp hp))
        (fun hq : q => hq)))

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h₁ : p ∨ False =>
      h₁.elim
        (fun hp : p => hp)
        (fun hf : False => False.elim hf))
    (fun h₂ : p => Or.inl h₂)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h₁ : p ∧ False =>
      have hf : False := h₁.right
      show False from hf)
    (fun h₂ : False => False.elim h₂)

example : (p → q) → (¬q → ¬p) :=
  (fun hpq : p → q =>
    (fun hnq : ¬q =>
      (fun hp : p => show False from hnq (hpq hp))))


open Classical

--variable (p q r : Prop)
#check em p

-- additional exercise
example : (p ∨ ¬p) ↔ (¬¬p → p) :=
  Iff.intro
    (fun h₁ : p ∨ ¬p =>
      (fun hnnp : ¬¬p =>
        h₁.elim
          (fun hp : p => hp)
          (fun hnp : ¬p => absurd hnp hnnp)))
    (fun _ : ¬¬p → p =>
      byCases
        (fun hp : p => Or.inl hp)
        (fun hnp : ¬p => Or.inr hnp))

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (fun hpqr : p → q ∨ r =>
    --Or.elim (em p)
    byCases
      (fun hp : p =>
        Or.elim (hpqr hp)
          (fun hq =>
            Or.inl (fun _ => hq))
          (fun hr =>
            Or.inr (fun _ => hr)))
      (fun hnp : ¬p =>
        Or.inl (fun hp => absurd hp hnp)))
          
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun hnpq : ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp : p =>
        Or.inr
          (show ¬q from
            fun hq : q =>
              hnpq ⟨hp,hq⟩))
      (fun hp : ¬p =>
        Or.inl hp))
      
example : ¬(p → q) → p ∧ ¬q :=
  (fun hnpq : ¬(p → q) =>
    (fun hp : p =>
      byCases (em q)
        (fun hq : q =>
          absurd
            (fun hpq : p → q => hpq (hp))
            hnpq)
        (fun hq : ¬q => ⟨hp,hq⟩)))



















example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
