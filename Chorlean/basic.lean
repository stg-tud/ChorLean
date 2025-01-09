inductive Tm
| add: Tm -> Tm -> Tm | lit: Nat -> Tm


structure with_logs (α:Type) where
  v: α
  logs: List String

def append (s:String) : with_logs Unit := {logs:= [s], v:= ()}

def with_logs.bind : {α β : Type} → with_logs α → (α → with_logs β) → with_logs β := fun x f =>
   let res := (f x.v)
  ⟨res.v, x.logs.append res.logs⟩

instance: Monad with_logs where
  pure x := ⟨x, []⟩
  bind := with_logs.bind


def Tm.eval: Tm -> with_logs Nat
| .add a b =>do
  let a' <- a.eval
  let b' <- b.eval

  let res := a' + b'
  append s!"{a'}+{b'}={res}"
  return res
| .lit x => return x

def comp_with_logs: with_logs Nat := do
  append "hello"
  append "world"
  return 3

#eval comp_with_logs.logs

#eval (Tm.eval $ .add (.lit 1) (.add (.lit 2) (.lit 3)) ).logs
