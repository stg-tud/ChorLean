import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.List.Sort
open Effect

abbrev N := 3


inductive Location
| Worker: Fin N -> Location
deriving Repr

instance: FinEnum (Location) :=
  FinEnum.ofEquiv _ (proxy_equiv% (Location)).symm

open Location

inductive MasterEff: Type -> Type where
| gen:  MasterEff (List Nat)

instance: Signature MasterEff where
  interpretation
  | .gen => do
    let n <- CmdInput.readNat (.some "enter the random List length")
    return (<-generate_random_list n)


instance: Role where
  δ := Location
  sig x := match x with
  | Worker _ =>  EmptyEff

  executable x := match x with
  | Worker _ => inferInstance

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

variable  (r : α → α → Prop) [DecidableRel r]


def ll: List Nat := [1,2,3]
#eval ll[0]'(by trivial)


/-- Implementation of a merge sort algorithm to sort a list. -/
def dmergeSort: Choreo all p Unit := do

  let w0_lst: (List String) @ (·  = (Worker 0)) := Located.wrap ["1","2","3"]
  let w1_lst <- com'' w0_lst (Worker 1)


  
  let f: ∀ h:(ep' = (Worker 0)), (w0_lst h) = ["1","2","3"] := fun cen => by revert w0_lst cen; simp [Located.wrap]; exact fun w1_lst h h_1 => False.elim (h_1 h)

  

  let f2: ∀ h:(ep' = (Worker 0)), (w0_lst h).length = 3 := fun cen => by revert w0_lst cen; simp [Located.wrap]; rfl


  have: [1,2,3].length = 3 := rfl

  let w2_lst <- bcast (Worker 0) w0_lst


  have yy := w2_lst.prop


  locally (Worker 1) (fun {cen} =>
    have xx := (w1_lst (Or.inr cen)).prop
    have qqq: ∀ z: (ep' = (Worker 0)), w2_lst.val = ["1","2","3"] := fun e => by simp [f e, w2_lst.prop e];

    have k: w2_lst.val = ["1","2","3"] := Knowledge2 qqq
    dbg_trace ((w2_lst.val)[1]'(by simp [k];))
    return ()
  )
  return


/-- Implementation of a merge sort algorithm to sort a list. -/
def dmergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    -- Porting note: rewrote to make `mergeSort_cons_cons` proof easier
    let ls := (List.split (a :: b :: l))
    have := List.length_split_fst_le l
    have := List.length_split_snd_le l
    exact List.merge (r · ·) (dmergeSort ls.1) (dmergeSort ls.2)
  termination_by l => List.length l

def sort_serial: List Nat -> List Nat:= List.mergeSort (· < ·)

def par_sort
  (data: (List Nat) @ (· = Worker 0))
  :
  Choreo (· ≠ Master) p ((List Nat)  @ (· = (Worker 0))) := do

  let chunks <- scatterList data

  par (fun a => do
    let x := a.val
    return ()
  )

  let sorted_chunks := chunks.map sort_serial
  gatherList (Worker 0) sorted_chunks merge

instance: ChorMain where
  main _args := do
    have: MonadLiftT MasterEff (MasterEff ⨳ Time ⨳ Sleep) := inferInstance

    let data <- com Master (Worker 0) MasterEff.gen

    let sorted <- enclave (· ≠ Master)
      (par_sort data.cast)

    let sorted: (List Nat) @ (· = Worker 0) := sorted.flatten.cast
    let sorted <- com (Worker 0) Master (fun {cen} => return (sorted cen))

    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
