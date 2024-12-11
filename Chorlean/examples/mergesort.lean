import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.List.Sort
open Effect

variable (n: Nat)

inductive Location
| Master | Worker: Fin n -> Location
deriving Repr

instance: FinEnum (Location n) :=
  FinEnum.ofEquiv _ (proxy_equiv% (Location n)).symm
open Location

abbrev N := 2

instance r_inst: Role where
  δ := Location N
  adj
  | Master, Worker 0, _
  | Worker 0, Master, _
  | Worker _, Worker _, _ => true
  | Worker _, Master, _
  | Master, Worker _, _ => false

variable [ep_inst: Endpoint]

-- takes two sorted lists as an input and produces a sorted list of all numbers
def merge: List Nat -> List Nat -> List Nat
| a::as2, b::bs =>
  if a < b then
    [a] ++ merge as2 ([b] ++ bs)
  else
    [b] ++ merge ([a] ++ as2) bs
| [], [] => []
| as2, [] => as2
| [], bs => bs

abbrev sort_serial': List Nat -> List Nat:=
  List.mergeSort (· < ·)

def par_sort
  (ls:  (List Nat) @ (· = Worker 0))
  : Choreo (· ≠ Master) c ((List Nat)  @ (· = (Worker 0)) ) := do

  let chunks        <- scatterList ls
  let sorted_chunks := (chunks.map sort_serial')
  gatherList (Worker 0) sorted_chunks merge


instance: ChorMain where
  main _args := do
    let data <- [(Worker 0), Master]~
      [Master]° locally do
        let n <- CmdInput.readNat (.some "enter the random List length")
        return (<-generate_random_list n)

    let sorted <- enclave (· ≠ Master)
      (par_sort data.cast)

    let sorted: (List ℕ)@fun x => x = Worker 0 := sorted.flatten.cast

    let sorted' <- [(Worker 0), Master]~
      [Worker 0]°
        (fun {cen} => return (sorted (by revert cen; simp)))


    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
