inductive DBType where
  | int | float | string | bool
deriving DecidableEq

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .float => Float
  | .string => String
  | .bool => Bool

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with 
  | .int => x == y
  | .float => x == y
  | .string => x == y
  | .bool => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .float => reprPrec
    | .string => reprPrec
    | .bool => reprPrec


--
structure Column where
  name : String
  contains : DBType
deriving DecidableEq

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  -- @Antonio: Good eye in seeying that col2 can be seemingly omitted here; however: this is intended to clearly distinguish the last case from the second case. In the second case the length of the schema is exactly one and by using col1 :: col2 :: cols in the last case, one can ensure that length is at least 2 here. With omitting col2, this would only be length at least 1. Not sure if this is a problem, but I like it better to have disjoint cases here.
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
  --| col1 :: cols => col1.contains.asType × Row (cols)

abbrev Table (s : Schema) := List (Row s)

def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq

inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨ name, t ⟩ :: _) name t 
  | there : HasCol s name t → HasCol (_ :: s) name t 

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next


--
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger

def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
  match sub with
  | .nil => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)


--
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2 => evaluate row e1 == evaluate row e2
  | .lt e1 e2 => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v



-- queries
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s .bool → Query s
  | project : Query s → (s' : Schema) → Subschema s' s → Query s'
  | product :
      Query s1 → Query s2 →
      disjoint (s1.map Column.name) (s2.map Column.name) →
      Query (s1 ++ s2)
  | renameColumn :
      Query s → (c : HasCol s n t) → (n' : String) → !((s.map Column.name).contains n') → 
      Query (s.renameColumn c n')
  | prefixWith :
      (n : String) → Query s →
      Query (s.map fun c => {c with name := n ++ "." ++ c.name})
  | naturalJoin : 
    Query s1 -> Query s2 -> Query (s1 ++ (s2.removeAll s1))

-- cartesian
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | _ :: _, v' => (v, v')

def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)

def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f

def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append

-- join
def Table.nJoin (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.filterMap r1.append
  -- like cartesianProduct, but with a condition: two columns must be of the same name
  -- and have at least one common entry
  -- Option type
  -- output schema should merge common rows, not like s1 ++ s2
  

-- difference
def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)

-- renaming
def Row.rename (c : HasCol s n t) (row : Row s) : Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)

-- prefix
def prefixRow (row : Row s) : Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

-- execute query
def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
  | .select q e => exec q |>.filter e.evaluate
  | .project q _ sub => exec q |>.map (·.project _ sub) 
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c) 
  | .prefixWith _ q => exec q |>.map prefixRow
  | .naturalJoin q1 q2 => exec q1 |>.nJoin (exec q2)

-- TODO: prove this theorem
theorem join_eq_product_on_disjoint_schema (q1 : Query s1) (q2 : Query s2) (disj : disjoint (s1.map Column.name) (s2.map Column.name)) : (cast (by 
    have : s2.removeAll s1 = s2 := by 
      -- TODO: first show that the types are equal by showing that removing s1 from s2 yields exactly s2 (using disj)
      -- this should probably go into another general theorem about lists
      sorry
    rw [this]
  ) (Query.naturalJoin q1 q2).exec) = (Query.product q1 q2 disj).exec := by 
  sorry

def join_via_other_operations (q1 : Query s1) (q2 : Query s2) : Table (s1 ++ (s2.removeAll s1)) :=
  sorry -- TODO: define join via other operations (prefixWith, product, select, project) (could be quite hard due to renamings)

theorem join_defs_eq (q1 : Query s1) (q2 : Query s2) : (Query.naturalJoin q1 q2).exec = join_via_other_operations q1 q2 := by 
  sorry



-- tests
def R : Schema := [
  ⟨"A", DBType.int⟩,
  ⟨"B", DBType.int⟩
]

def S : Schema := [
  ⟨"A", DBType.int⟩,
  ⟨"F", DBType.int⟩,
  ⟨"G", DBType.int⟩
]

def exR : Table R := [
  (1, 2),
  (4, 5),
  (7, 8)
]

def exS : Table S := [
  (1, 2, 3),
  (7, 8, 9)
]

open Query in
def example1 :=
  let t1 := table exR |>.prefixWith "R"
  let t2 := table exS |>.prefixWith "S"
  t1.product t2 (by repeat constructor)
    |>.select (.eq (c! "R.A") (c! "S.A"))
    |>.project [⟨"R.A", .int⟩, ⟨"S.A", .int⟩] (by repeat constructor)

-- common column still needs to be merged, so that solution contains only 4 columns
def solution : Table (R ++ S) := [
  (1, 2, 1, 2, 3),
  (7, 8, 7, 8, 9)
]

#eval example1
-- compare example1 and solution
