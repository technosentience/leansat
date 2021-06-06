import Std.Data.HashMap
import Leansat.CNF

structure SolverState : Type where
  assignment : Assignment
  assignmentHistory : Array Nat
  cnf : CNF
  maxVariable : Nat

def assign (st : SolverState) (i : Nat) (v : Bool) : SolverState :=
  { st with
      assignment := { map := st.assignment.map.insert i v },
      assignmentHistory := st.assignmentHistory.push i }

def literalAssign (st : SolverState) : Literal -> SolverState
| Literal.var i => assign st i true
| Literal.neg i => assign st i false

def isAssigned (st: SolverState) (i : Nat) : Bool :=
  st.assignment.map.contains i

def backtrack (st : SolverState) : SolverState :=
  let i := st.assignmentHistory.back
  { st with
      assignment := { map := st.assignment.map.erase i },
      assignmentHistory := st.assignmentHistory.pop }

def currentState (st : SolverState) : Value :=
  evalCNF st.assignment st.cnf

def litIndex : Literal -> Nat
| Literal.var i => i
| Literal.neg i => i

def freeLiterals (a : Assignment) (c : Clause) : Array Literal :=
  if evalClause a c = Value.sat then #[]
  else Array.filter (a.map.contains ∘ litIndex) c.disjuncts

def pickUnit : Array Literal -> Option Literal
| #[u] => some u
| _    => none

def unitLiterals (a : Assignment) (c : CNF) : Array Literal :=
  Array.filterMap (pickUnit ∘ freeLiterals a) c.conjucts

def assignUnitLiterals (st : SolverState) : SolverState :=
  let u := unitLiterals st.assignment st.cnf
  Array.foldl literalAssign st u

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

def addClause (a : Assignment) (p : Purities) (c : Clause) : Purities :=
  Array.foldl addLiteral p $ freeLiterals a c

def purities (a : Assignment) (c : CNF) : Purities :=
  Array.foldl (addClause a) { purities := ∅ } c.conjucts

def pickPure : Nat × Purity -> Option Literal
| ⟨n, Purity.pos⟩    => some (Literal.var n)
| ⟨n, Purity.neg⟩    => some (Literal.neg n)
| ⟨_, Purity.impure⟩ => none

def pureLiterals (p : Purities) :=
  Array.filterMap pickPure p.purities.toArray

def assignPureLiterals (st : SolverState) : SolverState :=
  let p := pureLiterals $ purities st.assignment st.cnf
  Array.foldl literalAssign st p

def nextVariable (cur : Nat) (st : SolverState) : Nat :=
  let range := (List.range (st.maxVariable + 1)).drop (cur + 1)
  (List.filter (not ∘ isAssigned st) range).headD 0

def revertTo (n : Nat) (st : SolverState) : SolverState :=
  match st.assignmentHistory.findIdx? (fun x => x = n) with
  | none   => st
  | some i =>
    let range := (List.range st.assignmentHistory.size).drop (i + 1)
    List.foldl (fun s _ => backtrack s) st range

def DPLL : SolverState -> Nat -> SolverState × Value
| st, 0 => ⟨st, Value.unknown⟩
| st, fuel + 1 =>
  match currentState st with
  | Value.sat => ⟨st, Value.sat⟩
  | Value.unsat => ⟨st, Value.unsat⟩
  | Value.unknown =>
    let st := assignUnitLiterals st
    let st := assignPureLiterals st

    let cur := st.assignmentHistory.back
    let next := nextVariable cur st
    let st := assign st next true
    let ⟨st, val⟩ := DPLL st fuel

    if val = Value.unsat then
      let st := revertTo cur st
      let st := assign st next false
      DPLL st fuel
    else
      ⟨st, Value.sat⟩
      
def maxVariableClause (c : Clause) :=
  Array.foldl max 0 $ Array.map litIndex c.disjuncts

def maxVariable (c : CNF) :=
  Array.foldl max 0 $ Array.map maxVariableClause c.conjucts

def solveCNF (c : CNF) (fuel : Nat) : Value :=
  let st : SolverState := 
    { assignment := { map := ∅ },
      assignmentHistory := ∅,
      cnf := c,
      maxVariable := maxVariable c }
  (DPLL st fuel).snd
