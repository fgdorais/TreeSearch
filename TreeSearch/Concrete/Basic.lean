import Lean
import Reap
import TreeSearch.Abstract.BestFirst
open Lean Elab Tactic

def evalTacticStr (str : String) : TacticM (Option Tactic.SavedState) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `tactic str | return none
  try
    evalTactic stx
    pruneSolvedGoals
    if (← getThe Core.State).messages.hasErrors then
      return none
  catch _ => return none
  return ← Tactic.saveState

structure SearchState where
  state : Tactic.SavedState
  priority : Float := 0.0

def SearchState.restore (ss : SearchState) : TacticM Unit := ss.state.restore

def isTerminal (ss : SearchState) : TacticM Bool := do
  ss.restore
  return (← getUnsolvedGoals).isEmpty

def priority (ss : SearchState) : TacticM Float := do
  if ← isTerminal ss then
    return Float.inf
  else
    return ss.priority

def expand (ss : SearchState) : TacticM (Array (String × SearchState)) := do
  let mut newStates := #[]
  let p := ss.priority
  ss.restore
  let g ← getMainGoal
  let tactics ← TacticGenerator.generateTactics g
  for (t, Δp) in tactics do
    ss.restore
    if let some s' ← evalTacticStr t then
      -- TODO: merge nodes
      newStates := newStates.push (t, ⟨ s', p + Δp ⟩)
  return newStates

structure PPSearchState where
  pp : List String
  priority : Float
deriving ToJson

def ppSearchState (ss : SearchState) : TacticM PPSearchState := do
  ss.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => return toString (← Meta.ppGoal g)
  return ⟨ pp, ss.priority ⟩

def reapBFS : TacticM Unit := do
  let (k, nodes) ← bestFirstSearch priority isTerminal expand ⟨ ← Tactic.saveState, 0.0 ⟩
  let ppNodes ← nodes.mapM fun node => do
    let pp ← ppSearchState node.data
    return json%{
      state: $pp,
      children: $(node.children)
    }
  let info := json%{
    solution: $k,
    nodes: $ppNodes
  }

  -- Do something with the JSON data
  IO.println info

  if let some k := k then
    let some node := nodes[k]? | unreachable!
    node.data.restore

elab "reap?!" : tactic => reapBFS
