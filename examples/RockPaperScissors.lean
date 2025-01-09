import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Effect
inductive Move   | Rock | Paper | Scissors
deriving Lean.ToJson, Lean.FromJson, Repr

inductive Result | A | B | Draw


instance: ToString Move where toString | .Rock => "Rock" |.Paper => "Paper" |.Scissors => "Scissors"

def wins: Move -> Move -> Bool
| .Rock, .Scissors | .Scissors, .Paper | .Paper, .Rock => true | _, _ => false

instance: ToString Result where toString | .A => "A" |.B => "B" |.Draw => "Draw"

def eval (a b: Move): Result :=
  if (wins a b) then
    .A
  else if (wins b a) then
    .B
  else
    .Draw

partial def promptMove: IO Move := do
  IO.println "enter your move (R|P|S)"
  let line <- IO.getLine
  match line with
  | "s" | "S" => return .Scissors
  | "r" | "R" => return .Rock
  | "p" | "P" => return .Paper
  | _ => promptMove

instance: Role where
  N := 2
  name | 0 => "A" | 1 => "B"

def A: δ := 0
def B: δ := 1

variable [Endpoint]
variable [MonadLiftT NetEff IO]


instance: ChorMain where
  main _ := do
    let moves <- par promptMove
    let moves <- gatherAll moves
    let resAB := eval (moves ⟨A, by decide⟩) (moves ⟨B,by decide⟩)

    let msg: Faceted String := Faceted.of fun id =>
      match resAB with
      | .A    => s!"you {if (id = A) then "won" else "lost"}"
      | .B    => s!"you {if (id = B) then "won" else "lost"}"
      | .Draw => "Draw!"

    --par $ IO.println (msg rid (by simp; exact RID.is_ep.symm))

    par ( do
      let myMsg := msg rid
      let content := myMsg.un (by simp)
      return ()
    )


    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
