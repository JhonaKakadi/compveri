import «RelationalAlgebra.Set»
import «RelationalAlgebra.Relation»

variable {\alpha : Type}

-- the basic operations:
def project (R : Rel) (A : Attr) : Rel :=
-- TODO, maybe use a list of attributes; make it a set, not a multiset

def select (R : Rel) (A : Attr) (P : Prop) : Rel := -- a Set of all Attr with the property
-- TODO, list of properties

def rename (A : Attr) (new : String) : Attr := {name := new, list := A.list}
-- TODO

-- the set operations:
def union (R S : Rel) : Rel := 

def intersec

def diff

def symmdiff

-- kartesian product

-- joins

-- division



-- proofs:
--   joins are admissible
--   intersection is admissible
--   ...
