import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Effect

def get_budget := do
  IO.println "enter your budget"
  return (←IO.getLine).toNat!

def get_title := do
    IO.println "enter your title"
    return (←IO.getLine)

def lookup_price title := do
    IO.println "looked up title"
    return  (if (title) == "Faust" then 100 else 200)

def deliveryDate := do
    IO.println "enter the delivery date:"
    return (←IO.getLine)


instance: Role where
  N := 2
  executable
  |0 => inferInstance | 1 => inferInstance
  name | 0 => "buyer" | 1 => "seller"

def buyer: δ := 0
def seller: δ := 1

variable [Endpoint]
variable [MonadLiftT NetEff IO]

def budget:Nat @ [buyer] := Located.wrap 150


def books: Choreo [buyer, seller] cen String:= do

  let title <- buyer° get_title
  let price <- seller° (
    return if title == "Faust" then 100 else 200
  )

  let decision: Bool <- buyer° (
    return (budget.un) >= price
  )

  if decision then
    let date ← seller° deliveryDate
    return date
  else
    return "never"

instance: ChorMain where
  main _ := do
    let res <- books

    buyer~ locally (IO.println s!"delivery date: {res}")
    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
