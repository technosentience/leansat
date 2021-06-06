import Std.Data.HashMap

inductive Literal : Type where
  | var (i : Nat) : Literal
  | neg (i : Nat) : Literal

structure Clause : Type where
  disjuncts : Array Literal

structure CNF : Type where
  conjucts : Array Clause

structure Assignment : Type where
  map : Std.HashMap Nat Bool

inductive Value : Type where
  | sat     : Value
  | unsat   : Value
  | unknown : Value

def vOr : Value → Value → Value
  | Value.sat,     _           => Value.sat
  | Value.unknown, Value.unsat => Value.unknown
  | Value.unknown, v           => v
  | Value.unsat,   v           => v

def vAnd : Value → Value → Value
  | Value.unsat,   _         => Value.unsat
  | Value.unknown, Value.sat => Value.unknown
  | Value.unknown, v         => v
  | Value.sat,     v         => v

def evalLiteral (a : Assignment) : Literal → Value
  | Literal.var i =>
    match a.map.find? i with
    | none       => Value.unknown
    | some false => Value.unsat
    | some true  => Value.sat
  | Literal.neg i =>
    match a.map.find? i with
    | none       => Value.unknown
    | some false => Value.sat
    | some true  => Value.unsat

def evalClause (a : Assignment) (c : Clause) : Value :=
  let or (v : Value) (l : Literal) := vOr v $ evalLiteral a l
  Array.foldl or Value.unsat c.disjuncts

def evalCNF (a : Assignment) (c : CNF) : Value :=
  let and (v : Value) (c : Clause) := vAnd v $ evalClause a c
  Array.foldl and Value.sat c.conjucts

def satisfies (a: Assignment) (c: CNF) := evalCNF a c = Value.sat

def satisfiable (c: CNF) := ∃ a, satisfies a c
