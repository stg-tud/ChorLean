import Chorlean.Choreo
import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Chorlean.Effects

inductive TestRoles
| A | B | C
deriving Repr, Fintype, DecidableEq, Inhabited

instance : FinEnum TestRoles :=
  FinEnum.ofEquiv _ (proxy_equiv% TestRoles).symm

open TestRoles


instance: Role where
  δ := TestRoles
  sig
  | _ => Effect.EmptyEff
  executable
  | _ =>  inferInstance

variable [Endpoint]
variable [MonadLiftT NetEff IO]


def showcase: Choreo all c Unit := do


  let b: Nat @ (· = B) := Located.wrap 3
  let m1 <- (bcast' b)

  let c: Nat @ (· = C) := Located.wrap 2
  let m2 <- (bcast' c)

  let result:Nat := m1 + m2

  -------------------
  have b_is_3: ∀ z: (ep' = B), b z = 3 := by revert b; simp [Located.wrap]; exact fun a b z h =>False.elim (h z)
  have c_is_2: ∀ z: (ep' = C), c z = 2 := by revert c; simp [Located.wrap]; exact fun a b z h =>False.elim (h z)

  have m1_is_3: (ep' = B) -> m1 = (3:Nat) := fun e => by simp [b_is_3 e, m1.prop e]
  have m2_is_2: (ep' = C) -> m2 = (2:Nat) := fun e => by simp [c_is_2 e, m2.prop e]
  -------------------

  have m1_is_3: m1 = (3:Nat) := Knowledge m1_is_3
  have m2_is_2: m2 = (2:Nat) := Knowledge m2_is_2

  have: result = 5 := by simp [result, m1_is_3, m2_is_2];

  have : ∀ l1 l2 : δ, l1 = l2 :=
    λ l1 l2 =>
      have h1 : ep' = l1 := Knowledge (λ h => h)
      have h2 : ep' = l2 := Knowledge (λ h => h)
      Eq.trans (Eq.symm h1) h2

  return
