import Mathlib.Data.FinEnum
import Chorlean.Free

class Signature (ops: Type -> Type) where
  interpretation: ops α -> IO α

instance [Signature ops]: MonadLiftT ops IO where
  monadLift := Signature.interpretation

class Role where
  -- Role datatype. Each value represents one distinct role in a choreography
  δ: Type
  -- defines a directed graph over locations, where edges indicate channels
  adj: (s r:δ) → (s ≠ r) -> Bool := fun _ _ _ => True


  sig: δ → (Type → Type)
  [executable: ∀ (l:δ), Signature (sig l)]
  [deq_inst: DecidableEq δ]
  [fe_inst : FinEnum δ]
  [repr_inst: Repr δ]

variable [Role]
abbrev δ := Role.δ

instance: DecidableEq (Role.δ) := Role.deq_inst
instance: FinEnum (Role.δ) := Role.fe_inst
instance: Repr (Role.δ) := Role.repr_inst

instance: ∀ (l:Role.δ), (Signature (Role.sig l)) := Role.executable