import Chorlean.Free
import Chorlean.utils

class Signature (ops: Type -> Type) where
  interpretation: ops α -> IO α

instance [Signature ops]: MonadLiftT ops IO where
  monadLift := Signature.interpretation

class Role where
  N: Nat
  sig: Fin N → (Type → Type) := fun _ => IO

  name: Fin N -> String := fun (x) => s!"#{x.val}"
  unique_names: ∀ a b: Fin N, name a = name b -> a = b := by decide

  [executable: ∀ (l:Fin N), Signature (sig l)]

@[reducible]
def Fin.enumerate: (n:Nat) -> List (Fin n)
| 0 => []
| i + 1 =>
  let temp: List (Fin (i+1)) := enumerate i
  temp ++ [⟨i, Nat.lt_add_one i⟩]


variable [Role]
abbrev N := Role.N
abbrev δ := Fin N

abbrev Role.list := Fin.enumerate N

def max_name_len [Role]: Nat :=
  longest_string ((Role.list).map (fun x => Role.name x))

def Role.ofString? (s:String) [Role]:  Option δ := do
  for e in (FinEnum.toList δ) do
    if (Role.name e == s) then
      return e
  Option.none
