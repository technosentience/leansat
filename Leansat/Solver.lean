import Std.Data.HashMap
import Leansat.CNF

structure SolverState : Type where
  assignment : Assignment
  assignmentHistory : Array Nat
  cnf : CNF
  fuel : Nat
  currentVariable : Nat
  maxVariable : Nat

def assign (st : SolverState) (i : Nat) (v : Bool) : SolverState :=
  {
    st with
      assignment := { map := st.assignment.map.insert i v },
      assignmentHistory := st.assignmentHistory.push i,
  }

def literalAssign (st : SolverState) : Literal -> SolverState
| Literal.var i => assign st i true
| Literal.neg i => assign st i false

def isAssigned (st: SolverState) (i : Nat) : Bool :=
  st.assignment.map.contains i

def backtrack (st : SolverState) : SolverState :=
  let i := st.assignmentHistory.back
  {
    st with
      assignment := { map := st.assignment.map.erase i },
      assignmentHistory := st.assignmentHistory.pop
  }

def currentState (st : SolverState) : Value :=
  evalCNF st.assignment st.cnf

def litIndex : Literal -> Nat
| Literal.var i => i
| Literal.neg i => i

def freeLiterals (a : Assignment) (c : Clause) : Array Literal :=
  Array.filter (a.map.contains ∘ litIndex) c.disjuncts

def pickUnit : Array Literal -> Option Literal
| #[u] => some u
| _    => none

def unitLiterals (a : Assignment) (c : CNF) : Array Literal :=
  Array.filterMap (pickUnit ∘ freeLiterals a) c.conjucts

inductive Purity : Type where
  | pos    : Purity
  | neg    : Purity
  | impure : Purity

structure Purities : Type where
  purities : Std.HashMap Nat Purity

def addPurity : Option Purity -> Literal -> Purity
| none,               Literal.var _ => Purity.pos
| none,               Literal.neg _ => Purity.neg
| some Purity.pos,    Literal.var _ => Purity.pos
| some Purity.pos,    Literal.neg _ => Purity.impure
| some Purity.neg,    Literal.var _ => Purity.impure
| some Purity.neg,    Literal.neg _ => Purity.neg
| some Purity.impure, _             => Purity.impure

def addLiteral (p : Purities) (l : Literal) : Purities :=
  let i := litIndex l
  { purities := p.purities.insert i (addPurity (p.purities.find? i) l) }

def addClause (p : Purities) (c : Clause) : Purities :=
  Array.foldl addLiteral p c.disjuncts

def purities (c : CNF) : Purities :=
  Array.foldl addClause { purities := ∅ } c.conjucts
