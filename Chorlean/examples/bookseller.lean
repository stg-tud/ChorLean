import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

open Effect

inductive Location
| buyer | seller
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location



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
  δ := Location

variable [Endpoint]
variable [MonadLiftT NetEff IO]

def budget:Nat @ (· = buyer) := Located.wrap 150


def books: Choreo all c String:= do

  let title <- [buyer]° locally get_title

  let price <- [seller]° (do
    return if title == "Faust" then 100 else 200
  )

  let decision: Bool <- [buyer]° (fun {cen} =>
    return (budget (by revert cen; simp)) >= price
  )

  if decision then
    let date ← [seller]° locally deliveryDate
    return date
  else
    return "never"


variable (p q : Prop)

instance: ChorMain where
  main _ := do
    let res <- books
    [buyer]~ locally $ IO.println s!"delivery date: {res}"
    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
