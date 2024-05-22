-- realtions (or tables) consist of attributes (columns) which have a name
-- and some elements

variable {\alpha : Type}

-- attribute
structure Attr where
  name : String
  playload : Set \alpha
  -- TODO set or list?
deriving Repr

-- a relation is a set of attributes
def Rel
-- TODO relations must have compatible types
   -- i.e. same amount of attributes
   -- attribute types must be identical
