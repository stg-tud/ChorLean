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
open Lean Json ToJson FromJson Effect CmdInput Log

instance: Role where
  δ := Location
  adj
    | client, IP, _ => true
    | client, service, _ => false
    | service, _, _ => false
    | IP, _, _ => true

variable [Endpoint]
variable [MonadLiftT NetEff IO]

structure Credentials where
  username: String
  password: String
deriving ToJson, FromJson, Repr

abbrev Token := String

def prompt_credentials: IO Credentials := do
  let username <- readString ("enter your username")
  let password <- readString ("enter your password")
  return {username, password}


def createToken: IO Token := pure "valid token"

def check_hash (s:String): IO Bool := readBool (.some s!"is the hash [{s}] correct? (apply db lookup here)")

def calcHash (salt: String) (pwd: String): String := (salt ++ pwd).dropRight 1

def add_salt (s:String): String := "salty " ++ s


def authenticate (creds: Credentials @ (·=client))
  : Choreo (· ∈ [client, IP]) cen ((Option Token)):= do

  let valid:Bool <-   [client, IP]°  do

    let username <-  [client]°  (fun {cen} => return (creds (by revert cen; simp)).username)
    let salt ←       [IP]°      (             return add_salt (username))
    let hash ←       [client]°  (fun {cen} => return calcHash salt ((creds (by revert cen; simp)).password))
    [IP]° locally (check_hash hash)

  if valid then
    let token_opt ← [IP]°  locally (do
      Log.info "AUTHENTICATION SUCCESS"
      return some (<- createToken)
    )
    return token_opt
  else
    par fun _id => Log.warning "Authentication failed"
    return none


instance: ChorMain where
  main _args := do

  let creds <- [client]~ locally prompt_credentials
  let res <-  [client, IP]~ authenticate creds.cast
  let res' <- bcast' res
  return Faceted.of 0


def main := CHOR_ENTRYPOINT
