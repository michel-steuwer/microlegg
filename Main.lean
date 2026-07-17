import Microlegg

def check (name : String) (cond : Bool) : IO Unit :=
  IO.println s!"{if cond then "✔" else "✘ FAIL"} {name}"

def ufTest : Bool :=
  let uf : UnionFind := {}
  let (a, uf) := uf.makeset
  let (b, uf) := uf.makeset
  let (c, uf) := uf.makeset
  let (_, uf) := uf.union a b
  let (_, uf) := uf.union b c
  (uf.find a == uf.find c)

#eval check "UF find" ufTest

open EGraph

def leaf (name : String) : ENode := ENode.mk name ∅

def egTest : EGraphM Bool := do
  let a   ← add (leaf "a")
  let a'  ← add (leaf "a")
  let b   ← add (leaf "b")
  return a == a' && a != b

#eval check "egTest" (egTest.run' {})

def congruenceTest : EGraphM Bool := do
  let a  ← add (leaf "a")
  let b  ← add (leaf "b")
  let fa ← add (ENode.mk "f" [a])
  let fb ← add (ENode.mk "f" [b])
  let _  ← union a b
  rebuild
  return (← get).uf.find fa == (← get).uf.find fb

#eval check "congruenceTest" (congruenceTest.run' {})

-- constants are just 0-ary applications; `+` is binary
def commRule : Rewrite :=
  ⟨.app "+" [.var "a", .var "b"],
   .app "+" [.var "b", .var "a"]⟩

def assocRule : Rewrite :=
  ⟨.app "+" [.app "+" [.var "a", .var "b"], .var "c"],
   .app "+" [.var "a", .app "+" [.var "b", .var "c"]]⟩

def sevenSum : Pattern :=
  .app "+" [
    .app "+" [.app "+" [.app "a" [], .app "b" []],
              .app "+" [.app "c" [], .app "d" []]],
    .app "+" [.app "+" [.app "e" [], .app "f" []],
              .app "g" []]]

def bigTest : EGraphM Bool := do
  let _ ← instantiate sevenSum ∅
  saturate [commRule, assocRule]
  return ((← allIds).length, ← memo.size) == (127, 1939)

#eval check "big test" (bigTest.run' {})


def main : IO Unit := do
  check "UF find" ufTest
  check "egTest" (egTest.run' {})
  check "congruenceTest" (congruenceTest.run' {})
  check "big test" (bigTest.run' {})
