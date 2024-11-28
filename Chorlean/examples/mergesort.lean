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

inductive MasterEff: Type -> Type where
| gen:  MasterEff (List Nat)

instance: Signature MasterEff where
  interpretation
  | .gen => do
    let n <- CmdInput.readNat (.some "enter the random List length")
    return (<-generate_random_list n)

abbrev N := 2

instance r_inst: Role where
  δ := Location N
  sig x := match x with
  | Master =>  MasterEff ⨳ Time ⨳ Sleep
  | Worker _ =>  Log ⨳ Sleep
  executable x := match x with
    | Master => inferInstance
    | Worker _ => inferInstance
  adj
  | Master, Worker 0, _
  | Worker 0, Master, _
  | Worker _, Worker _, _ => true
  | Worker _, Master, _
  | Master, Worker _, _ => false

#eval Role.adj (Worker 1) (Worker 0) (by decide)

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

partial def sort_serial: List Nat -> List Nat
| [] => []
| x::[] => [x]
| l => do
  let size := l.length
  let pivot := size / 2
  let ls := l.seperate (pivot)
  let l1 := ls.1
  let l2 := ls.2

  let l1_sorted := sort_serial l1
  let l2_sorted := sort_serial l2

  merge l1_sorted l2_sorted


#eval sort_serial [5,2,3,4]


def calc0 (a b: Located (· = Worker 0) Nat): Located (· = Worker 0) Nat := do
  return (<-a) + (<-b)

def par_sort
  (ls:  (List Nat) @ (· = Worker 0))
  : Choreo (· ≠ Master) c ((List Nat)  @ (· = (Worker 0)) ) := do

  -- let data: (List (Nat×Nat)) @ (· = Worker 0) := Located.wrap [⟨1,2⟩, ⟨14,22⟩, ⟨5231,23⟩, ⟨321,23⟩, ⟨231,25⟩, ⟨21,233⟩]
  -- let results <- par_map_list data (fun x => x.1+x.2)


  let chunks        <- scatterList ls
  -- let sorted_chunks <- par ( do
  --   return sort_serial chunks
  -- )
  let sorted_chunks := (chunks.map sort_serial')
  gatherList (Worker 0) sorted_chunks merge

def worker_to_worker (a b: Location N) (neq:a ≠ b ) (not_master: a ≠ Master ∧ b ≠ Master)
  : Role.adj a b (neq) :=
  by revert a b; decide


partial def dist_sort (m: Fin N)
  (ls: (List Nat) @ (· = Worker m))
  (indents: Nat:= 0)
  : Choreo (· ≠ Master) c ((List Nat) @ (· = Worker m)) := do


  let one: Fin N := ⟨1, Nat.one_lt_two⟩
  let w0 := Worker m
  let w1 := Worker (m + one)
  let w2 := Worker (m + one + one)
  have w0_neq_m: w0 ≠ Master:= (by simp only [ne_eq, not_false_eq_true])
  have w1_neq_m: w1 ≠ Master:= (by simp only [ne_eq, not_false_eq_true])
  have w2_neq_m: w2 ≠ Master:= (by simp only [ne_eq, not_false_eq_true])

  let size <- enclave (· = w0) (fun {cen} =>
    return (ls cen).length ) (fun x a => ne_of_eq_of_ne a w0_neq_m) 
  let finished:Bool <- enclave_bcast (· = w0) (fun {cen} =>
    return ((size cen) <= 1)) (by exact fun x a => ne_of_eq_of_ne a w0_neq_m) (by sorry)

  if (finished) then
      return ls
    else
      let pivot <- enclave (· = w0) (fun {cen} => do return (Float.floor ((size cen).toFloat / 2)).toUInt16.toNat) (fun _ a => ne_of_eq_of_ne a w0_neq_m)
      let ls <- enclave (· = w0) (fun {cen} => do return  (ls cen).seperate (pivot cen)) (fun _ a => ne_of_eq_of_ne a w0_neq_m)
        



      let chunk1 <- com w0 w1 (fun {cen} => do
          return (ls cen).fst
        )
        (fun x => worker_to_worker w0 w1 x (by trivial)) (w0_neq_m) (w1_neq_m)
      let chunk2 <- com w0 w2 (fun {cen} => do
          return (ls cen).snd
        )
        (fun x => worker_to_worker w0 w2 x (by trivial)) (w0_neq_m) (w2_neq_m)

      let s_chunk1 <- dist_sort (m+one) (chunk1.cast (by simp)) (indents+1)
      let s_chunk2 <- dist_sort (m+one+one) (chunk2.cast (by simp)) (indents+1)

      let s_chunk1' <- com w1 w0 (fun {cen} => return (s_chunk1 cen))
        (fun x => worker_to_worker w1 w0 x (by trivial))
        w1_neq_m
        w0_neq_m
      let s_chunk2' <- com w2 w0 (fun {cen} => return (s_chunk2 cen))
        (fun x => worker_to_worker w2 w0 x (by trivial))
        w2_neq_m
        w0_neq_m

      let res <- locally w0 (fun {cen} => do return  merge (s_chunk1' (Or.inr cen)) (s_chunk2' (Or.inr cen)))
        w0_neq_m

      dbg_trace s!"{repeat_string "  " indents}merged {res}"
      return res

#eval sort_serial [1,2,5325,5,2,43,623,62,63426,4634,23,5425,325,3]



def testing_ (n:Nat): IO Unit := do
  let data  <- generate_random_list n
  let start <- Time.getTime
  let _serial <- ComputeEff.compute (sort_serial (data))
  Sleep.sleep 2331
  let delta <- Time.getTime

  let delta := delta - start
  Log.info (s!"serial duration: {Time.NanosToSec (delta)} sec.")

#eval testing_ 2000

def test: IO Unit:= do


  return ()



instance: ChorMain where
  main _args := do
    have: MonadLiftT MasterEff (MasterEff ⨳ Time ⨳ Sleep) := inferInstance
    have: MonadLiftT Time (MasterEff ⨳ Time ⨳ Sleep ⨳ Log) := inferInstance
    have: MonadLiftT Log (MasterEff ⨳ Time ⨳ Sleep ⨳ Log) := inferInstance
    let data <- 【(· ∈ [(Worker 0), Master])】
      【(· = Master)】*
        run MasterEff.gen


    -- let sorted <- enclave (· ≠ Master)
    --   (dist_sort 3 0 data.cast 0 (by exact Nat.lt_add_one 2))
    -- let sorted := sorted.flatten

    -- let sorted' <- com (Worker 0) Master (fun {cen} => return (sorted (by simp only [ne_eq, Fin.isValue]; exact And.intro (by sorry) cen)))
    --   (fun _ => rfl)
    --   rfl
    --   rfl

    let sorted <- enclave (· ≠ Master)
      (par_sort data.cast)

    let sorted := sorted.flatten

    let sorted' <- 【(· ∈ [(Worker 0), Master])】
      【(· = (Worker 0))】*
        (fun {cen} => return (sorted (by simp only [ne_eq, Fin.isValue, cen]; exact if_false_left.mp trivial)))


    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
