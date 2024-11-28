import Chorlean.Choreo
import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Chorlean.Effects
-- example from: Choral: Object-Oriented Choreographic Programming
-- 3.1 Distributed authentication

inductive Location
| client | service | IP
deriving Repr, Fintype, DecidableEq, Inhabited

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location
open Effect
open Effect.CmdInput


inductive IPEff: Type -> Type
| createToken: IPEff String
| check_hash: String -> IPEff Bool


instance: Signature IPEff where
  interpretation
  | .createToken => return "valid token"
  | .check_hash s => readBool (.some s!"is the hash [{s}] correct? (apply db lookup here)")


open Lean Json ToJson FromJson
structure Credentials where
  username: String
  password: String
deriving ToJson, FromJson, Repr

inductive ClientEff: Type -> Type
| prompt_credentials: ClientEff Credentials


instance: Signature ClientEff where
  interpretation
  | .prompt_credentials => do
    let username <- readString ("enter your username")
    let password <- readString ("enter your password")
    return {username, password}



instance: Role where
  δ := Location
  adj
    | client, IP, _ => true
    | client, service, _ => false
    | service, _, _ => false
    | IP, _, _ => true
  sig
    | client  =>  Log ⨳ ClientEff
    | service =>  Log
    | IP      =>  Log ⨳ IPEff

  executable
    | client =>  inferInstance
    | service =>  inferInstance
    | IP => inferInstance


variable [Endpoint]

instance [(x : δ) → Decidable (c x)] (alone : (List.filter (fun b => decide (c b)) (FinEnum.toList δ)).length = 1 := by decide): MonadLift IO (Choreo c p) where
  monadLift x := run x alone
--instance [(x : δ) → Decidable (c x)] (alone : (List.filter (fun b => decide (c b)) (FinEnum.toList δ)).length = 1 := by decide): Coe (IO α) (Choreo c p (α)) where
--  coe x := run x alone
instance: Coe (Faceted Unit) Unit where
  coe _ := ()

def calcHash (salt: String) (pwd: String): String := (salt ++ pwd).dropRight 1

def add_salt (s:String): String := "salty " ++ s

open Log
open IPEff

variable [MonadLiftT NetEff IO]

abbrev Token := String

--⇹

abbrev ll: List Location := [client, IP]
abbrev ll2 := ll.map (Role.sig)

@[specialize]
abbrev List.foldlInline {α : Type u} {β : Type v} (f : α → β → α) : (init : α) → List β → α
  | a, nil      => a
  | a, cons b l => foldl f (f a b) l

def xx2:Free (Role.sig client ⇹ IO ⇹ Role.sig IP ⇹ Role.sig service) Unit := do
  have: MonadLift Log (Log ⨳ IPEff) := inferInstance
  have: MonadLift Log (Log ⨳ ClientEff) := inferInstance
  Log.info "hello"
  return

#check False

def xx:Free (ll2.foldlInline CoSum IO) Unit := do
  have: MonadLift Log (Log ⨳ IPEff) := inferInstance
  have: MonadLift Log (Log ⨳ ClientEff) := inferInstance
  --Log.info "hello"
  return





def authenticate (creds: Credentials @ (·=client))
  : Choreo all cen ((Option Token)):= do

  have: MonadLift IPEff (Log ⨳ IPEff) := inferInstance
  have: MonadLift Log (Log ⨳ IPEff) := inferInstance
  have: MonadLift Log (Log ⨳ ClientEff) := inferInstance


  let valid:Bool <-      【(· ∈ [client, IP])】* do

    let username <- 【(· = client)】*  (return (creds (by trivial)).username)
    let salt ←      【(· = IP)】*      (return add_salt (username))
    let hash ←      【(· = client)】*  (return calcHash salt ((creds (by trivial)).password))
    【(· = IP)】* run (check_hash hash)

  if valid then
    let token_opt ← 【(· = IP)】*  run (do

      Log.info "AUTHENTICATION SUCCESS"
      return some (<- createToken)
    )
    return token_opt
  else
    【(· = IP)】 par (do
      IO.println ""
      return 3
    )
  return none


def sso_auth: Choreo all rfl ((Option Token) @ (· ∈ [client, service])) := do
  have: MonadLift ClientEff (Log ⨳ ClientEff) := inferInstance
  have ff := Role.executable client


  let creds <- 【(· = client)】 fun {cen} =>  run (
    have: MonadLift ClientEff (Role.sig ep') := match ep', cen with
      | client, _ => inferInstance
      | IP, _ => sorry
      | service, _ => by sorry

    ClientEff.prompt_credentials)




  let res <- authenticate creds


  return Located.wrap res


instance: ChorMain where
  main _args := do
    let _res <- sso_auth
    return Faceted.of 0


unsafe def main := CHOR_ENTRYPOINT
