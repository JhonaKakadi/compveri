-- relational algebra relies on set operations

def Set (\alpha) := \alpha -> Prop

namespace Set
  def emptyset : Set \alpha := fun _ => False

  def element (e : \alpha) (X : Set \alpha) : Prop := X e

  def subset (X Y : Set \alpha) : Prop := \all e : \alpha, element X e -> element Y e

-- basic set operations needed for the relational algebra
  def union (X Y : Set \alpha) : Set \alpha := fun e => element X e \or element Y e
  
  def intersec(X Y : Set \alpha) : Set \alpha := fun e => element X e \and element Y e

