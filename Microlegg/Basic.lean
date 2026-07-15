import Std.Data.HashMap
open Std

abbrev ID := Nat

structure ENode where
  f : String
  l : List ID
  deriving Hashable, BEq

structure UnionFind where
  parent : Array ID := #[]

namespace UnionFind

def makeset (uf: UnionFind) : ID × UnionFind :=
  let id' := uf.parent.size
  (id', ⟨uf.parent.push id'⟩)

partial def find (uf: UnionFind) (id : ID) : ID :=
  let pid := uf.parent[id]!
  if pid == id then id else find uf pid

def union (uf: UnionFind) (a b : ID) : Bool × UnionFind :=
  let a' := find uf a
  let b' := find uf b
  if a' == b' then
    (false, uf)
  else
    (true, ⟨uf.parent.set! b' a'⟩)

end UnionFind

structure EGraph where
  uf : UnionFind := {}
  memo : HashMap ENode ID := ∅

namespace EGraph

def canonicalizeNode (n : ENode) : StateM EGraph ENode := do
  let eg ← get
  return ⟨n.f, n.l.map (eg.uf.find)⟩

def add (n : ENode) : StateM EGraph ID := do
  let eg ← get
  let n ← canonicalizeNode n
  match eg.memo[n]? with
    | some id => return id
    | none =>
      let (newId, uf) := eg.uf.makeset
      set { eg with uf := uf, memo := eg.memo.insert n newId }
      return newId

def union (a b : ID) : StateM EGraph Bool := do
  let (changed, uf) := (← get).uf.union a b
  modify (fun eg => { eg with uf := uf })
  return changed

def rebuild : StateM EGraph Unit := do
  let mut keepGoing := true
  while keepGoing do
    keepGoing := false
    let oldMemo := (← get).memo
    modify (fun eg => {eg with memo := ∅})
    for (oldNode, oldId) in oldMemo.toList do
      let newNode ← canonicalizeNode oldNode
      let newId ← match (← get).memo[newNode]? with
        | some newId => pure newId
        | none =>
          let newId := (← get).uf.find oldId
          modify (fun eg => {eg with memo := eg.memo.insert newNode newId })
          pure newId
      if (← union newId oldId) then keepGoing := true

end EGraph

inductive Pattern where
  | var : String → Pattern
  | app : String → List Pattern → Pattern

abbrev Subst := HashMap String ID

namespace EGraph

def instantiate (pat : Pattern) (subst : Subst) : StateM EGraph ID :=
  match pat with
    | .var name => return subst[name]!
    | .app f l => do
      let node := ⟨f, (← l.mapM (fun p => instantiate  p subst))⟩
      return (← add node)

def nodesInClass (eg : EGraph) (root : ID) : List ENode :=
  eg.memo.toList.filterMap (fun (n, id) => if id == root then some n else none)

partial def ematchRec (pat : Pattern)
                      (root : ID)
                      (subst : Subst) : StateM EGraph (List Subst) := do
  match pat with
    | .var name => match subst[name]? with
      | none => return [subst.insert name root]
      | some v => if v == root then return [subst] else return []
    | .app f subpats => do
      let nodes := (← get).nodesInClass root
      let mut outputs : List Subst := []
      for node in nodes do
        if node.f != f then continue
        if node.l.length != subpats.length then continue
        let mut todo : List Subst := [subst]
        for (subId, subPat) in node.l.zip subpats do
          let mut results : List Subst := []
          for newSubst in todo do
            results := results ++ (← ematchRec subPat subId newSubst)
          todo := results
        outputs := outputs ++ todo
      return outputs

def ematch (pat : Pattern) (root : ID) : StateM EGraph (List Subst) :=
  ematchRec pat root ∅


end EGraph

structure Rewrite where
  lhs : Pattern
  rhs : Pattern

structure Match where
  rhs : Pattern
  root : ID
  subst : Subst

namespace EGraph

def allIds (eg : EGraph) : List ID :=
  (eg.memo.toList.map (·.2)).eraseDups

def rewrite (rules : List Rewrite) : StateM EGraph Unit := do
  let mut ms : List Match := []
  for rule in rules do
    for id in (← get).allIds do
      let substs := (← ematch rule.lhs id)
      for subst in substs do
        ms := ms.concat ⟨rule.rhs, id, subst⟩
  for m in ms do
    let newId ← instantiate m.rhs m.subst
    let _ ← union m.root newId

def saturate (rules : List Rewrite) : StateM EGraph Unit := do
  rebuild
  let mut fingerprint := ((← get).uf.parent.size, (← get).memo.size)
  while true do
    rewrite rules
    rebuild
    let newFingerprint := ((← get).uf.parent.size, (← get).memo.size)
    if fingerprint == newFingerprint then
      break
    else
      fingerprint := newFingerprint

end EGraph
