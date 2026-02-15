module
public meta import Batteries.Data.Array
public meta import TreeSearch.Abstract.Basic
public meta import Lean

namespace Reap.TreeSearch

public meta section
/- Helper functions for working with an array of objects in StateT -/
variable {σ : Type} {m : Type → Type} [Monad m]

/-- Push a new element onto the state array, returning its index -/
def pushT (x : σ) : StateT (Array σ) m Nat :=
  .modifyGet fun a => (a.size, a.push x)

def getAtT (i : Nat) (d : σ) : StateT (Array σ) m σ := do
  return (← get)[i]?.getD d

def getsAtT {τ : Type} (i : Nat) (f : σ → τ) (d : τ) : StateT (Array σ) m τ := do
  return (← get)[i]?.elim d f

def setAtT (i : Nat) (x : σ) : StateT (Array σ) m Unit :=
  modify fun a => a.set! i x
end

public meta section
abbrev SearchT σ ε m := StateT (Array (Node σ (ε × Nat))) m

variable {σ ε : Type}
variable {m : Type → Type} [Monad m]

def resolve (node : Node σ (ε × Nat)) : SearchT σ ε m (Node σ (ε × σ)) := do
  let data := node.data
  let children ← node.children.mapM fun (e, i) => do pure (e, ← getsAtT i Node.data data)
  return { data, children }

partial def mctsStep
    (isTerminal : σ → m Bool)
    (expand : Node σ (ε × σ) → m (Array (ε × σ)))
    (selectChild : Node σ (ε × σ) → m (Option Nat))
    (updateEdge : σ → ε → σ → m ε)
    (updateNode : Node σ (ε × σ) → m σ)
    (i : Nat) : SearchT σ ε m (Option Nat) := do
  let nodes ← get
  let some x := nodes[i]? | unreachable!
  let s := x.data
  let node ← resolve x
  match ← selectChild node with
  | none =>
      let mut newChildren := #[]
      let mut result := none
      for (e, s') in ← expand node do
        let i' ← pushT { data := s' }
        newChildren := newChildren.push (e, i')
        if ← isTerminal s' then
          result := some i'
      modify fun a => a.set! i { x with children := x.children ++ newChildren }
      return result
  | some k =>
      let some (e, j) := x.children[k]? | unreachable!
      let result ← mctsStep isTerminal expand selectChild updateEdge updateNode j
      let e' ← updateEdge s e (← getsAtT j Node.data s)
      let x' := { x with children := x.children.set! k (e', j) }
      let s' ← updateNode (← resolve x')
      let x'' := { x' with data := s' }
      setAtT i x''
      return result

partial def monteCarloTreeSearch
    (isTerminal : σ → m Bool)
    (expand : Node σ (ε × σ) → m (Array (ε × σ)))
    (selectChild : Node σ (ε × σ) → m (Option Nat))
    (updateEdge : σ → ε → σ → m ε)
    (updateNode : Node σ (ε × σ) → m σ)
    (start : σ) (maxNodes : Nat := 64) (maxSteps : Nat := 64) : m (Option Nat × Array (Node σ (ε × Nat))) :=
  StateT.run (s := #[ { data := start } ]) do
    let mut step := 0
    while (← get).size <= maxNodes && step < maxSteps do
      let result ← mctsStep isTerminal expand selectChild updateEdge updateNode 0
      if result.isSome then
        return result
      step := step + 1
    return none
end

end Reap.TreeSearch
