module
public meta import Batteries.Data.Array
public meta import TreeSearch.Basic
public meta import Lean

namespace TreeSearch

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
abbrev IndexedTreeT σ ε m := StateT (Array (Node σ (ε × Nat))) m

variable {σ ε : Type}
variable {m : Type → Type} [Monad m]

local notation "SearchM" => IndexedTreeT σ ε m

def resolve (node : Node σ (ε × Nat)) : SearchM (Node σ (ε × σ)) := do
  let data := node.data
  let children ← node.children.mapM fun (e, i) => do pure (e, ← getsAtT i Node.data data)
  return { data, children }

unsafe def mctsStep
    (visitNode : Node σ (ε × σ) → SearchM (σ × Array (ε × σ)))
    (selectChild : Node σ (ε × σ) → SearchM (Option Nat))
    (updateEdge : σ → ε → σ → σ → SearchM ε)
    (updateNode : Node σ (ε × σ) → σ → SearchM σ)
    (i : Nat) : SearchM σ := do
  let nodes ← get
  let x := nodes[i]'lcProof
  let s := x.data
  let node ← resolve x
  match ← selectChild node with
  | none =>
      let (data', children') ← visitNode node
      let mut newChildren := #[]
      for (e, s') in children' do
        let i' ← pushT { data := s' }
        newChildren := newChildren.push (e, i')
      modify fun a => a.set! i { data := data', children := x.children ++ newChildren }
      return node.data
  | some k =>
      let (e, j) := x.children[k]'lcProof
      let data ← mctsStep visitNode selectChild updateEdge updateNode j
      let e' ← updateEdge s e (← getsAtT j Node.data s) data
      let x' := { x with children := x.children.set! k (e', j) }
      let s' ← updateNode (← resolve x') data
      let x'' := { x' with data := s' }
      setAtT i x''
      return data

def MCTS.defaultMaxNodes : Nat := 64
def MCTS.defaultMaxSteps : Nat := 64

unsafe def monteCarloTreeSearch
    (isTerminal : σ → SearchM Bool)
    (visitNode : Node σ (ε × σ) → SearchM (σ × Array (ε × σ)))
    (selectChild : Node σ (ε × σ) → SearchM (Option Nat))
    (updateEdge : σ → ε → σ → σ → SearchM ε)
    (updateNode : Node σ (ε × σ) → σ → SearchM σ)
    (start : σ)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) :
    m (Option Nat × Array (Node σ (ε × Nat))) :=
  StateT.run (s := #[ { data := start } ]) do
    let mut step := 0
    while (← get).size <= maxNodes && step < maxSteps do
      discard <| mctsStep visitNode selectChild updateEdge updateNode 0
      let result ← (← get).findIdxM? fun x => isTerminal x.data
      if result.isSome then
        return result
      step := step + 1
    return none
end

end TreeSearch
