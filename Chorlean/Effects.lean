import Chorlean.utils
import Chorlean.Free
import Chorlean.Role

instance [Signature ops] [Signature ops'] : Signature (CoProd ops ops') where
  interpretation
  | CoProd.l o => Signature.interpretation o
  | CoProd.r o => Signature.interpretation o

namespace Effect


/--
`EmptyEff` is a non inhabited effect
-/
inductive EmptyEff: Type → Type

inductive ComputeEff: Type → Type
| compute: α -> ComputeEff α

instance: Signature ComputeEff where
  interpretation
  | .compute v => return v

instance: Signature EmptyEff where
  interpretation x := by contradiction


  inductive Log: Type → Type
  | warning: String → Log Unit
  | info: String → Log Unit
  | error: String → Log Unit
  deriving Repr

  instance: Signature Log where
    interpretation m := match m with
    | .info msg => IO.println     s!"[info]    {msg}"
    | .warning msg => IO.println  s!"[warning] {msg}"
    | .error msg => IO.eprintln   s!"[error]   {msg}"

  inductive CmdInput: Type → Type
  | readString (msg: Option String := none): CmdInput String
  | readNat (msg: Option String := none): CmdInput Nat
  | readBool (msg: Option String := none): CmdInput Bool




  instance: Signature CmdInput where
    interpretation
    | .readString msg => do
      if h:(msg.isSome) then
        IO.println (msg.get h)
      return <- IO.getLine
    | .readNat  msg => do
      if h:(msg.isSome) then
        IO.println (msg.get h)
      return (<-IO.getLine).toNat!
    | .readBool msg => do
      if h:(msg.isSome) then
        IO.println ((msg.get h) ++ " (y/n)")
      return (<-IO.getLine) == "y"

  inductive Sleep: Type → Type
  | sleep (ms: UInt32): Sleep Unit

  instance: Signature Sleep where
    interpretation
    | .sleep d => do
      IO.sleep d

  inductive Time: Type → Type
  | getTime: Time Nat

  instance: Signature Time where
    interpretation
    | .getTime => do
      IO.monoNanosNow

  inductive Rand: Type → Type
  | rand (hi lo: Nat): Rand Nat

  instance: Signature Rand where
    interpretation
      | .rand hi lo => do
        IO.rand hi lo


  def Time.NanosToSec: Nat → Float :=  fun x => x.toFloat / 1000000000


  
end Effect


def generate_random_list_rec: (l: List Nat) → Nat → Free Effect.Rand (List Nat)
| _, 0 =>  return []
| remaining, len+1 =>  do
  let index <- Effect.Rand.rand 0 (remaining.length-1)
  let rest_list <- generate_random_list_rec (remaining.eraseIdx index) len
  return rest_list.concat remaining[index]!

def descending_list: Nat → List Nat
| 0 => []
| x+1 => [x+1] ++ descending_list (x)

def generate_random_list (n:Nat): Free Effect.Rand (List Nat) := do
  let sorted := descending_list n
  generate_random_list_rec sorted n


