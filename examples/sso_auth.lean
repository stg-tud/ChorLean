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

open Lean Json ToJson FromJson Effect CmdInput Log

instance: Role where
  N := 3
  name | 0 => "client" | 1 => "service" | 2 => "IP"


abbrev client: δ := 0
abbrev service: δ := 1
abbrev IP: δ := 2

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

def authenticate (creds: Credentials @ [client])
  : Choreo [client, IP] cen ((Option Token)):= do

  let valid <- [client, IP]°°  do

    let username <-  client°  (return (creds.un).username)
    let salt ←       IP°      (return add_salt username)
    let hash ←       client°  (return calcHash salt ((creds.un).password))
    IP° (check_hash hash)

  if valid then
    let token_opt ← IP° (do
      Log.info "AUTHENTICATION SUCCESS"
      return some (<- createToken)
    )
    return token_opt
  else
    return none


instance: ChorMain where
  main _args := do

    par $ IO.println s!"hello from {Role.name rid}"

    let creds <- client~ locally prompt_credentials

    let res <-  [client, IP]~~ authenticate creds.cast
    let res' <- bcast res


    par $ IO.println s!"by with token {res'}"
    return Faceted.of 0


def main := CHOR_ENTRYPOINT
