import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.List.Sort
open Effect

instance r_inst: Role where
  N := 3
  name
  | 0 => "Master" | 1 => "W1" | 2 => "W2"

def Master: Fin 3 := 0
def W0: Fin 3 := 1
def W1: Fin 3 := 2

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
  (ls:  (List Nat) @ (· = W0))
  : Choreo (· ≠ Master) c ((List Nat)  @ (· = W0) ) := do

  let chunks        <- scatterList ls
  let sorted_chunks := (chunks.map sort_serial')
  gatherList W0 sorted_chunks merge


instance: ChorMain where
  main _args := do
    let data <- [W0, Master]~
      [Master]° locally do
        let n <- CmdInput.readNat (.some "enter the random List length")
        return (<-generate_random_list n)

    let sorted <- enclave (· ≠ Master)
      (par_sort data.cast)

    let sorted: (List ℕ)@fun x => x = W0 := sorted.flatten.cast

    let sorted' <- [W0, Master]~
      [W0]°
        (fun {cen} => return (sorted (by revert cen; simp)))


    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
