import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Tactic.DeriveFintype

open Effect

inductive Location
| database | cache | client
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location



instance: Role where
  δ := Location
  sig
  | client => CmdInput
  | _ =>  (Log ⨳ CmdInput)
  executable
  | client => inferInstance
  | database => inferInstance
  | cache =>  inferInstance



variable [ep_inst:Endpoint]
variable [MonadLiftT NetEff IO]


def test : Faceted String
| cache =>  Located.wrap "c"
| client => Located.wrap "c"
| database => Located.wrap "d"

    --  (db | cache) & client
def db {loc: {x // x = database ∨ x = cache}}
  (data: Located (fun x => x = loc.val) String ): Choreo all rfl String := do

  have: MonadLift Log (Log ⨳ CmdInput) := inferInstance

  if h:(loc = database) then
    【(· = database)】 fun {cen} => run do
      let local_data := data (by simp [h, cen];)
      Log.info s!"in database: {local_data}"
    return ""
  else if h2:(loc = cache) then
    【(· = cache)】 fun {cen} => run do
      let local_data := data (by simp [h2, cen];)
      Log.info s!"in cache: {local_data}"
    return ""
  else
    have p := loc.prop
    have q: ¬(↑loc = database ∨ ↑loc = cache) := not_or_intro h h2
    by contradiction


def fac: Nat -> Nat
| 0 => 1
| i+1 => (i+1) * (fac i)


instance: ChorMain where
  main _args := do
    have: MonadLift CmdInput (Log ⨳ CmdInput) := inferInstance

    let data <- 【(· = client)】 λ {cen} => run do (CmdInput.readString "enter data")

    let x: Nat @ (fun x => x = cache) := Located.wrap (2:Nat)


    let gx <- bcast cache x
    --let global_x := global_x'.val
    --have gprop := global_x'.prop

    have qq: ∀ z: (ep' = cache), x z = 2 := by revert x; simp [Located.wrap]; exact fun a _ z h => False.elim (h z)
    have qqq: ∀ z: (ep' = cache), gx.val = 2 := fun e => by
      simp [qq e, gx.prop e];

    have temp := Knowledge qqq

    --have qqq := Knwoledge global_x 2 cache (rfl) (by exact?)


    --let y: Nat :=  (<- bcast' x) (by exact Or.intro_left (ep' = cache) rfl)


    let x <- 【(· ∈ [cache, database])】 par (return 3)
    let y <- gather' client x

    let y_cache <- 【(· = client)】 fun {cen} => return (y cen) ⟨cache, by simp⟩

    --let data <- locally cache (CmdInput.readString "enter data")

    --let answer: String <- race data_db data_cache





    let place_on_cache:Bool <- 【(· = client)】* fun {cen} => run (do
      return <- CmdInput.readBool "enter y to place data in cache"
    )

    let loc: {x // x = database ∨ x = cache} := if place_on_cache then ⟨cache, by trivial⟩  else ⟨database, by trivial⟩

    let data' <- enclave (p':= (· ∈ [client, loc.val])) (imp := fun _ _ => rfl) (do
      let input <- enclave (· = client) (fun {cen} =>  return (data cen)))
        (fun l' _ _ => rfl)
        (List.mem_cons_self client [↑loc])
      return input
    

    let placed_data: String @ (·=loc.val) := Located.cast data' (impl := by simp)
    let res <- db placed_data
    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
