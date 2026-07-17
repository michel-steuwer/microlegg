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

abbrev EGraphM := StateM EGraph

namespace EGraph

def modifyUF (g : UnionFind → α × UnionFind) : EGraphM α := do
  let (a, uf) := g (← get).uf
  modify fun eg => {eg with uf := uf}
  return a

def uf.makeset : EGraphM ID := modifyUF UnionFind.makeset

def uf.find (id : ID) : EGraphM ID := return (← get).uf.find id

def uf.parent.size : EGraphM Nat := return (← get).uf.parent.size

def memo.clear : EGraphM Unit := modify (fun eg => {eg with memo := ∅})

def memo.insert (n : ENode) (id : ID) : EGraphM Unit :=
  modify fun eg => {eg with memo := eg.memo.insert n id}

def memo.find? (n : ENode) : EGraphM (Option ID) := return (← get).memo[n]?

def memo.size : EGraphM Nat := return (← get).memo.size

def canonicalizeNode (n : ENode) : EGraphM ENode := do
  return ⟨n.f, (<- n.l.mapM uf.find)⟩

def add (n : ENode) : EGraphM ID := do
  let n ← canonicalizeNode n
  if let some id := ← memo.find? n then
    return id
  else
    let newId ← uf.makeset
    memo.insert n newId
    return newId

def union (a b : ID) : EGraphM Bool := modifyUF (·.union a b)

def rebuild : EGraphM Unit := do
  let mut keepGoing := true
  while keepGoing do
    keepGoing := false
    let oldMemo := (← get).memo
    memo.clear
    for (oldNode, oldId) in oldMemo.toList do
      let newNode ← canonicalizeNode oldNode
      let mut newId := 0
      if let some id := ← memo.find? newNode then
        newId := id
      else
        let id ← uf.find oldId
        modify (fun eg => {eg with memo := eg.memo.insert newNode id })
        newId := id
      if (← union newId oldId) then keepGoing := true

end EGraph

inductive Pattern where
  | var : String → Pattern
  | app : String → List Pattern → Pattern

abbrev Subst := HashMap String ID

namespace EGraph

def instantiate (pat : Pattern) (subst : Subst) : EGraphM ID :=
  match pat with
    | .var name => return subst[name]!
    | .app f l => do
      let node := ⟨f, (← l.mapM (fun subpat => instantiate subpat subst))⟩
      return (← add node)

def nodesInClass (root : ID) : EGraphM (List ENode) := do
  return (← get).memo.toList.filterMap (fun (n, id) => if id == root then some n else none)

partial def ematchRec (pat : Pattern)
                      (root : ID)
                      (subst : Subst) : EGraphM (List Subst) := do
  match pat with
    | .var name => match subst[name]? with
      | none => return [subst.insert name root]
      | some v => if v == root then return [subst] else return []
    | .app f subpats => do
      let nodes ← nodesInClass root
      let mut outputs := []
      for node in nodes do
        if node.f != f then continue
        if node.l.length != subpats.length then continue
        let mut todo := [subst]
        for (subId, subPat) in node.l.zip subpats do
          todo ← todo.flatMapM (ematchRec subPat subId ·)
        outputs := outputs ++ todo
      return outputs

def ematch (pat : Pattern) (root : ID) : EGraphM (List Subst) :=
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

def allIds : EGraphM (List ID) :=
  return ((← get).memo.toList.map (·.2)).eraseDups

def rewrite (rules : List Rewrite) : EGraphM Unit := do
  let mut ms : List Match := []
  for rule in rules do
    for id in ← allIds do
      let substs := (← ematch rule.lhs id)
      for subst in substs do
        ms := ms.concat ⟨rule.rhs, id, subst⟩
  for m in ms do
    let newId ← instantiate m.rhs m.subst
    let _ ← union m.root newId

def saturate (rules : List Rewrite) : EGraphM Unit := do
  rebuild
  let mut fingerprint := (← uf.parent.size, (← memo.size))
  while true do
    rewrite rules
    rebuild
    let newFingerprint := (← uf.parent.size, (← memo.size))
    if fingerprint == newFingerprint then
      break
    else
      fingerprint := newFingerprint

end EGraph
