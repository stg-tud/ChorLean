import Mathlib.Data.List.Sigma
import Chorlean.utils
import Chorlean.Free
import Batteries.Data.Array
import Chorlean.Role
import Chorlean.Effects

variable [Role]
variable {cfg:dbg_cfg}

variable [Role]

/--
Endpoint class. used to propagate the endpoint through the library.
Kept private from library users and only accessible throug the RID class
-/
class Endpoint where
  private mk::
  private endpoint: δ

variable [Endpoint]
private abbrev ep: δ := Endpoint.endpoint
noncomputable abbrev rid'' := ep


/--
Role Identity class.
provides access to the Endpoint class to the user, by an role that is equal to the endpoint identity
-/
class RID where
  id: δ
  is_ep: id = ep

/--
Role IDentity - the role identity, from which perspective the choreography is being run
-/
abbrev rid [RID] := RID.id

/--
Type for located variables.
It is defined by a proposition over a δ Location
and maps a proof of this proposition for the endpoint to a value
-/
def Located (p: List δ) (α: Type) := (ep ∈ p) -> α

-- Notation for located values
notation:max a "@" p  => Located p a


/-- `Faceted`  maps locations to a value that is only located at that location-/
def Faceted α :=  (l:δ) -> α @ [l]

/-- wraps values into `Faceted`.-/
def Faceted.of (v: δ -> α): Faceted α := fun x _ => v x

/-- Coe instance to implicetely facet types -/
instance: Coe α (Faceted α)  where
  coe x := Faceted.of (fun _ => x)


abbrev all := Role.list

-- Coe instance to implicetely unpack Located
instance (p: List δ) (cen: ep ∈ p): CoeOut (α @ p) α where
  coe x := x cen

/-- coerces `Located` Unit types into Unit-/
instance: CoeOut (Located o Unit) Unit where
  coe _ := ()

/-- coerces Unit into `Located` Unit-/
instance: Coe Unit (Located o Unit) where
  coe _ := fun _ => ()

/-- coerces `Faceted` Unit types into Unit-/
instance: Coe (Faceted Unit) Unit where
  coe _ := ()

/-- coerces Unit types into `Faceted` Unit -/
instance: Coe Unit (Faceted Unit)  where
  coe _ := ()

/-- wraps into a `Located` value by deciding over the predicate with access to the endpoint-/
def Located.wrap {p: List δ} (v:α): α @ p :=
  fun _x =>
    if h:(ep ∈ p) then
      v
    else
      by contradiction

def Located.bind {α β : Type} (x: α @p) (f: α → β @p):  β @p  :=
  if h:(ep ∈ p) then
    let v := x h
    f v
  else
    fun y => by contradiction

def Located.map {p: List δ}(f: α -> β) (x: α @ p): β @ p :=
 if h:(ep ∈ p) then
      let v := x h
      fun _ => f v
    else
      fun y => by contradiction

instance: Monad (Located p) where
  pure x := Located.wrap x
  bind := Located.bind
  map := Located.map

def Faceted.map (f: α -> β) (x: Faceted α): Faceted β := f ((x ep) (by simp))

instance: Monad Faceted where
  pure x := Faceted.of (fun _ => x)
  bind x f := f ((x ep) (by simp))
  map := Faceted.map

def Located.owners  {p: List δ}: Located p α -> List δ := fun _ => p.dedup

/-- removes one layer of a nested `Located`-/
def Located.flatten (v: Located p (Located q α)) : Located (p.inter q) α  :=
  fun pq => v (List.mem_of_mem_filter pq) (List.mem_of_mem_inter_right pq)

/-- abbreviation for looking at a `Faceted` from one singular role-/
abbrev Faceted.exclusive {loc:δ} (lf: (Faceted α) @ [loc]): (α @ [loc]) :=
  fun cen => (lf cen) loc cen

/-- ToString instance for distributed values with an ToString instance on the value type.
    "Empty", if the value is not present on the machine-/
instance [ToString μ]: ToString (μ @ p) where
  toString x :=
    if h:(ep ∈ p) then
      let val := x h
      toString val
    else
      "Empty"

/-- maps `Located` into another `Located` by evidence that (p x -> p' x).-/
def Located.cast   (gv:α @ p') (impl: {x:δ}-> (x ∈ p -> x ∈ p') := by decide): (α @ p) :=
  fun c => gv (impl c)


/--Signature for Networked programs.
   allows for sending and receiving messages.
   adheres to adjacency of roles and prohibits self referencing-/
inductive NetEff: Type → Type 1
| send {μ: Type} [Serialize μ] : (r:δ) → (p:ep ≠ r) → μ → NetEff Unit
| recv : (s:δ) → (p:ep ≠ s) →  (μ: Type) → [Serialize μ] → NetEff μ

/-- Channel structure that distributes two sockets over a sender and receiver end-/
structure Channel (sender receiver: δ) where
  recv_sock: Socket @ [receiver]
  send_sock: Socket @ [sender]

/--connects a sender role to an adress-/
def init_sending_channel (sender :δ) (addr: Address):  IO (Socket @ [sender]) := do
  if h:(ep ∈ [sender]) then
    let sock ← addr.connect_to
    return (fun _ => sock)
  else
    return (fun x => by contradiction)

/--listens for a adress-/
def init_receiving_channel  (receiver: δ) (addr: Address):  IO (Socket @ [receiver]) := do
  if h:(ep ∈ [receiver]) then
    let sock ← addr.listen_on
    return (Located.wrap sock)
  else
    return (fun x => by contradiction)

/-- epp for initializing a channel between two locations and printing dbg info to console-/
def init_channel (sender receiver: δ) (addr: Address):  IO (Channel sender receiver) := do

  if(cfg.print_init_sockets ∧ sender = ep) then
    IO.println (s!"<- {Role.name receiver} <-".dye Color.White Color.Purple)
  if(cfg.print_init_sockets ∧ receiver = ep) then
    IO.println (s!"-> {Role.name sender} ->".dye Color.White Color.Blue)
  let recv_sock ← init_receiving_channel receiver addr
  let send_sock ← init_sending_channel sender addr
  return ⟨recv_sock, send_sock⟩

/-- distributed datastructure containing all TCP Sockets-/
structure Network where
  channels: List (Σ (id: δ×δ), Channel id.1 id.2)
  complete: ∀ (k : δ×δ), (ne:k.1 ≠ k.2) → (channels.dlookup k).isSome

/-- helper function to look up channels -/
def Network.getChannel (net: Network) (k:δ×δ) (ne: k.1 ≠ k.2) : Channel k.1 k.2 :=
  (net.channels.dlookup k).get (by simp [net.complete, ne])

/-- calculates unique addresses for location pairs with ascending port numbers, starting at start_port-/
def default_adress (k:δ × δ) (start_port: Nat := 2222):  Address :=
  let port: Nat := start_port + k.1 * (Role.N) + k.2
  .v4  (.mk 127 0 0 1) port.toUInt16

/-- connects all nodes according to adjacency by TCP.
    returns a network-/
def init_network (as:  δ×δ -> Address := default_adress)
  : IO Network := do
  let filtered := ((Fin.list N).product (Fin.list N)).filter (fun k => k.1 ≠ k.2 ∧ (k.1 ≠ k.2))

  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k⟩ )
  let channels_prog: IO (List (Σ (k: δ×δ), Channel k.1 k.2)):= progs.mapM (fun x => do
    let id := x.1
    let chan: Channel id.1 id.2 ←  init_channel id.1 id.2 x.2 (cfg:=cfg)
    return ⟨id, chan⟩ )
  let cs ← channels_prog

  if(cfg.print_init_sockets) then
    let padding := max_name_len * 2 + 19
    IO.println ((repeat_string "-" padding) ++ "\n")
  return {
            channels := cs
            complete := fun k => by
              simp [List.dlookup_isSome, List.keys]
              intro x
              sorry -- TODO mightt be complicated to prove... maybe the function should be stated differently
              done
          }

/-- lifts NetEff into IO by sending and receiving messeges over the TCP Sockets of Network -/
instance NetEPP (net: Network): MonadLiftT NetEff IO where
  monadLift x := match x with
  | NetEff.send r q m=> do
    let ep := ep
    let ch := net.getChannel ⟨ep, r⟩ q
    let sock := ch.send_sock (by simp)
    if cfg.print_net_msgs then
      let send_text := s!"<- {Role.name r} <-".dyeBack Color.Purple
      IO.println s!"{send_text} {Serialize.pretty m}"
    sock.send_val2 m (cfg:=cfg)

  | NetEff.recv s q μ => do
    let ep := ep
    let c := net.getChannel ⟨s, ep⟩ (Ne.symm q)
    let sock := c.recv_sock (by simp)

    let res ← sock.recv_val2
    if cfg.print_net_msgs then
      let recv_text := s!"-> {Role.name s} ->".dyeBack Color.Blue
      IO.println s!"{recv_text} {Serialize.pretty res}"
    return res

variable [MonadLiftT NetEff IO]

/-- auxiliary Effect, coproduct of net_eff and local_eff-/
@[reducible] def LocalProgramEff := NetEff ⨳ IO

/-- A Monad for Local Effects where leff is the Effect Signature-/
@[reducible] def LocalM := Free (LocalProgramEff)


/--
monadic tpye for Choreographies.
Choreographies are parameterized by a predicate over roles and evidence that the predicate holds for ep.
Choreo is built out of 3 core primitives:
- Broadcasting values, results in a replicated value at every location
- Locally runs an IO Program and requires a single role to be present
- Enclave embedds a subchoreography with a smaller set of participants to be embeded into the current choreo

All other functionality builds upon these 3 constructs.
-/
inductive Choreo: (p:List δ) -> ep ∈ p ->  Type → Type 1 where
| Broadcast {μ:Type} [Serialize μ]

  (loc: δ)
  (msg: μ @ q)
  (ex: loc ∈ p)
  (owns: loc ∈ q)
  (next: μ -> Choreo p c α)
  :
  Choreo p c α
| Locally
  [RID]
  (prog: IO β)
  --(prog: Free (Role.sig rid) β)
  (next: β -> Choreo p c α)
  :
  Choreo p c α
| Enclave
  (rs: List δ)
  (subChor: (c': ep ∈ rs) -> Choreo rs c' β)
  (imp:  subRoles ⊆ p)
  (next: (β @ rs) -> Choreo p c α)
  :
  Choreo p c α
| Return
  (v:α):
  Choreo p c α

def Choreo.bind  {α β : Type} : Choreo p c α → (α → Choreo p c β) → Choreo p c β
| Choreo.Locally prog next, cont =>
  Choreo.Locally prog  (fun x => Choreo.bind (next x) cont)

| Choreo.Broadcast v ex ex2 next (loc:=loc), cont =>
  Choreo.Broadcast loc v ex ex2 (fun x => Choreo.bind (next x) cont)

| Choreo.Enclave subRoles subChor imp next, cont =>
  Choreo.Enclave subRoles subChor imp (fun x => Choreo.bind (next x) cont)

| Choreo.Return v, cont =>
  (cont v)

instance: Monad (Choreo p c) where
  pure := Choreo.Return
  bind := Choreo.bind

/-- projects a Chor to a LocalM by adding the neccesarry NetEffects -/
def Choreo.epp': (Choreo p c α) → IO α
| Choreo.Locally prog next => do
  have: Signature (Role.sig rid) := by simp [←RID.is_ep.symm]; exact (Role.executable ep)
  let res <- prog
  (next res).epp'

| Choreo.Broadcast v _ex next (loc:=loc) (μ:= μ) (c:=c) (q:=q) (owns := owns) => do
  if h1:(ep = loc) then

    let v := (v (by simp[h1]; exact owns))

    for x in (Fin.list N) do
      if h3: ¬(x ∈ q) ∧ (x ∈ p) ∧ (ep ≠ x) then
        NetEff.send x h3.right.right v
    (next v).epp'
  else if h2:(ep ∈ q) then
    let v := v h2
    (next v).epp'
  else
    let v ← NetEff.recv loc h1 μ
    (next v).epp'

| Choreo.Enclave subRoles subChor imp next  =>
  if h:(ep ∈ subRoles) then do
    let x := subChor h
    let y <- x.epp'
    (next (fun _ => y)).epp'
  else
    (next (fun _ => by contradiction)).epp'

| Choreo.Return v =>
  return v

/-- lifts Choreo into IO-/
instance EPP
  (net: Network) : MonadLiftT (Choreo p c) IO where
   monadLift x :=
    let _netlift := NetEPP net (cfg:=cfg)
    (Choreo.epp' x)

/--
unwraps a located value in the choreo monad, if the present roles are a subset of owners.
the subset relation is tried to be solved by the trivial tactic by default
-/
def Located.un [r:RID] (v: α @ rs) (knows: rid ∈ rs := by simp only [List.mem_singleton]; trivial):α :=
  (v (by simp [←RID.is_ep]; exact knows))

/--
broadcasts a value from one location to all other locations
-/
def bcast' {μ:Type} [Serialize μ]
  (loc: δ)
  (msg: μ @ q)
  (ex: loc ∈ p := by decide)
  (owns: loc ∈ q := by decide)
  :
  Choreo p c μ
  :=
  Choreo.Broadcast loc msg ex owns (fun x => Choreo.Return x)

/--
broadcasts a value from one location to all other locations
The Broadcaster is the one with lowest id of the intersection between owners and present roles
-/
def bcast {μ:Type} [Serialize μ]
  (msg: μ @ q)
  (ex: (p ∩ q).length > 0 := by decide)
  :
  Choreo p c μ
  :=
  let caster := (p ∩ q)[0]

  have h := List.getElem_mem (p ∩ q) 0 ex
  have h1: caster ∈ p := by simp[List.mem_of_mem_filter h]
  have h2: caster ∈ q := by simp[List.mem_of_mem_inter_right h]

  Choreo.Broadcast caster msg h1 h2 (fun x => Choreo.Return x)


/--
embedding a choreography containing stricly less roles
-/
def enclave
  (rs: List δ)
  (subChor: {c: ep ∈ rs} ->  Choreo rs c α)
  (imp:  rs ⊆ p := by decide)
  :
  Choreo p c (α @ rs)
  :=
  Choreo.Enclave rs (fun _ => subChor) imp (fun x => Choreo.Return x)


/--
embedding a choreography containing only a single role that was present before.
Allows to Access the RID class in the subchoreography, as the identity is known there
(the implicit arguments of subChor help Lean with automatically proving some properties, not really an optimal solution though...)
-/
def enclave'
  (r: δ)
  (subChor: [RID] -> {c: [rid] ⊆ [r]} -> {c2: rid = r} ->  Choreo [rid] (by simp; exact RID.is_ep.symm) α)
  (imp:  r ∈ p := by decide)
  :
  Choreo p c (α @ [r])
  :=
  Choreo.Enclave [r] (fun cen =>
    have: RID := ⟨r, by revert cen; simp; exact fun x => x.symm⟩
    have h: rid = r := by revert cen; simp [RID.is_ep]

    by simp [←h]; exact subChor (c:= by simp; exact h) (c2 := h)) (fun ⦃_⦄ a => a) (fun x => Choreo.Return x)


theorem in_to_eq (p: a ∈ [b]): a = b := by revert p; simp

/--
UNUSED
provides acces to the RID class if only one role is present
-/
def single
  (subChor: [RID] ->  Choreo [rid] (by simp; exact RID.is_ep.symm) α)
  (alone: ∀ (r: δ), r ∈ p -> r =p[0]'(List.length_pos_of_mem c) := by decide)
  :
  Choreo [p[0]'(List.length_pos_of_mem c)] (by refine List.mem_singleton.mpr (alone ep c)) α
  :=
  have: RID := ⟨p[0]'(List.length_pos_of_mem c), (alone ep c).symm⟩
  have h: rid = p[0]'(List.length_pos_of_mem c) := by simp [RID.is_ep]; exact (alone ep c)
  by simp [←h]; exact subChor

/--
Runs code locally at the current RID
-/
def locally
  [RID]
  (prog: Free IO α)
:Choreo p c α
  := do
  Choreo.Locally (prog) (fun x => Choreo.Return x)

/--
lifts programs into the choreo monad by the RID typeclass and locally exectuting programs
-/
instance [RID]: MonadLift IO (Choreo [rid] (by simp; exact RID.is_ep.symm)) where
  monadLift x := locally x


/-- combines enclave with broadcasting-/
def enclave_bcast{μ:Type} [Serialize μ]
  (rs: List δ)
  (subChor: {c: ep ∈ rs} -> Choreo rs c μ)
  (imp:  rs ⊆ p := by simp)
  (ex: (p ∩ rs).length > 0 := by decide)
  :
  Choreo p c μ
  := do
  let temp <- enclave rs subChor imp
  bcast temp ex

/-- combines enclave with a single role with broadcasting-/
def enclave_bcast'{μ:Type} [Serialize μ]
  (r: δ)
  (subChor: [RID] -> {c: [rid] ⊆ [r]} -> {c2: rid = r} -> Choreo [rid] (by simp; exact RID.is_ep.symm) μ)
  (imp:  r ∈ p := by decide)
  :
  Choreo p c μ
  := do
  let temp <- enclave' r (fun {_} {c1} {c2} => subChor (c:=c1) (c2 := c2)) imp
  bcast temp (by simp; sorry)

/-- `a~~b` enclaves a choreography `b` to a list of roles `a`-/
notation:max  a "~~" b  => enclave a b

/-- `a°°b` enclaves a choreography `b` to a list of roles `a` and broadcasts the result to the outer census-/
notation:max  a "°°" b  => enclave_bcast a b

/-- `a~b` enclaves a choreography `b` to a single role `a`-/
notation:max  a "~" b  => enclave' a b

/-- `a°b` enclaves a choreography `b` to a single role `a` and broadcasts the result to the outer census-/
notation:max  a "°" b  => enclave_bcast' a b

abbrev sumAll: (List (Type -> Type)) -> Type -> Type
| [] => IO
| a::as => CoSum a (sumAll as)


@[reducible] def List.inline_map (f : α → β) : List α → List β
| []    => []
| a::as => f a :: inline_map f as

@[reducible] def List.inline_filter (p : α → Bool) : List α → List α
  | [] => []
  | a::as => match p a with
    | true => a :: inline_filter p as
    | false => inline_filter p as

structure CoSum'
  (p:List δ) (α:Type) where
  es: (r:{r:δ // r ∈ p}) -> ((Role.sig r) α)

structure M (ms: List (Type -> Type)) (α:Type) where
  es: (i: Fin ms.length) -> ms[i] α

instance inst (ms: List (Type -> Type)) (eff: Type -> Type)
  [m: ∀ (i: Fin ms.length), MonadLift eff (ms[i])]: MonadLift eff (M ms) where

  monadLift x := {es := fun r => (m r).monadLift x }


instance {r:{x:δ // x ∈ rs}}: MonadLiftT (CoSum' rs) (Role.sig r) where
  monadLift x := x.es r

instance testinst (rs: List δ) (eff:Type -> Type) [m: ∀ (r: {x:δ // x ∈ rs}), MonadLiftT eff (Role.sig r.val)]: MonadLiftT eff (CoSum' rs) where
  monadLift x := {es := fun r => (m r).monadLift x }

/--
runs a program in parallel and grants access to the Role IDentity.
results in a `Faceted` value.
-/
def par
  (prog: [RID] -> IO α)
  :
  Choreo p c (Faceted α)
  := do


  let temp: List ((r:δ) ×  (α @ [r])) <- p.attach.mapM (fun (x:{r:δ // r ∈ p}) => do

    let res <- enclave (rs:=[x]) ( fun {c'} => do

      have: RID := ⟨x,  by revert c'; simp; exact fun {z} => (Eq.symm z)⟩

      have lifter: MonadLiftT (CoSum' p) (Role.sig x) := ⟨fun y => y.es x⟩
      have lifter2: MonadLiftT (Free (CoSum' p)) (Free (Role.sig x)) := inferInstance
      have: RID := ⟨x, by revert c'; simp; exact fun {c'} => id (Eq.symm c')⟩
      locally prog
    )
      (by simp [List.filter, List.of_mem_filter, c]; exact x.prop)
    return ⟨x, res⟩
  )
  return fun x => (temp.dlookup x).get (by sorry)


/--
convenience method that communicates the result of a local program from a sender to a receiver
-/
def com  [Serialize μ]
  (sender receiver: δ)
  (prog: [RID] -> (rid = sender) -> IO μ)
  (ex_sender: sender ∈ p := by decide)
  (ex_receiver: receiver ∈ p := by decide)
  :
  Choreo p c (μ @ [sender, receiver])
  := do
  enclave [sender,receiver] (fun {cen} => do
      let res <- enclave [sender] (fun {cen} =>
          have: RID := ⟨sender, (in_to_eq cen).symm⟩

          have qq: rid = sender := by revert cen; simp; exact fun {cen} => id (Eq.symm (by simp[RID.is_ep]; exact Eq.symm cen))
          locally (prog (qq))
        )
        (by simp)
      let res' <- bcast' sender res (by simp) (by simp)
      return res'
    )
    (by simp; exact ⟨ex_sender, ex_receiver⟩ )

/--
gathers the content of a `Faceted` in one single Role
-/
def gather  [Serialize μ]
  (loc: δ)
  (data: Faceted μ)
  (ex: loc ∈ p := by decide)
  :
  Choreo p c (({l // l ∈ p} -> μ) @ [loc])
  := do
    let mut vals: List ({l // l ∈ p} × (μ @ [loc])) := []


    let temp: List ({l // l ∈ p} × (μ @ [loc])) <- p.attach.mapM (fun (x: {r // r ∈ p}) => do

      let v <- com
        (x.val)
        (loc)
        (fun cen => return (data x (by simp [←RID.is_ep, cen])))
        (x.prop)
        (ex)


      return ⟨x, v.cast (impl := fun a => by exact List.mem_cons_of_mem x.val a)⟩
    )
    return fun a b => ((temp.lookup b).get (sorry)) a

/--
gathers all values of a faceted List in a single location by merging all individual lists.
merging defaults to appending lists
-/
def gatherList  [Serialize μ]
  (loc: δ)
  (data: Faceted (List μ))
  (merge: List μ -> List μ -> List μ := List.append)
  (ex: loc ∈ p := by decide)
  :
  Choreo p c ((List μ) @ [loc])
  := do
  let temp <- gather loc data ex

  enclave [loc] (fun {cen} =>
    have: RID := ⟨loc, (in_to_eq cen).symm⟩
    locally (do
    let mut res: List μ := []
    for x in (Fin.list N) do
      if h: x ∈ p then
        res := merge res ((temp cen) ⟨x, h⟩)
    return res
    )
  ) (by simp; exact ex)

/--
broadcast different role-dependent values of the same type
-/
def scatter  [Serialize μ]
  {loc: δ}
  (data:  {l // l ∈ p.dedup} -> (μ @ [loc]))
  (ex: loc ∈ p := by decide)
  :
  Choreo p c (Faceted μ)
  := do

  let mut lst: List (Σ (owner:{l // l ∈ p}), (μ @ [owner])) := []

  for x in (Fin.list N) do
    if h: (x ∈ p) then


      let lv <- com loc x (fun cen =>do

          dbg_trace s!"SENDING: {data ⟨x, by simp; exact h⟩} to {Role.name x}";

          return (data ⟨x, by simp; exact h⟩) (by simp [←RID.is_ep, cen])
        )
        ex
        h

      lst := lst.concat ⟨⟨x, h⟩, lv.cast (impl := fun {x_1} a => by exact List.mem_cons_of_mem loc a)⟩

  return Faceted.of (fun r => ((lst.dlookup ⟨r, sorry⟩).get (by sorry)) (by sorry))

/--
scatters items of a list evenly across nodes. The first portion of nodes might handle one additional item if there is a rest
-/
def scatterList  [Serialize μ]
  {loc: δ}
  (data:  (List μ) @ [loc])
  (ex: loc ∈ p := by decide)
  :
  Choreo p c (Faceted (List μ))  := do

  let N := p.dedup.length
  let data':  {l // l ∈ p.dedup} -> (List μ) @ [loc] :=
    fun x y =>
      let idx := p.dedup.attach.findIdx (· = x)

      let chunk_size := (data y).length / N
      let rest := (data y).length % N
      let chunk_start := (idx * chunk_size) + (min rest idx)

      let chunk_size :=
        if idx < rest then
          chunk_size + 1
        else
          chunk_size
      (data y).fromTo chunk_start chunk_size

  scatter data' ex (loc := loc)

/--
-- gathers all values of a `Faceted` at a every location
-/
def gatherAll  [Serialize μ]
  (data: Faceted μ)
  :
  Choreo p c ({l // l ∈ p}-> μ)
  := do

  let temp: List ({l // l ∈ p} × μ) <- p.mapM (fun x => do

    have qq: x ∈ p := by sorry

    let temp <- bcast' x (data x) qq (by simp)
    return ⟨⟨x, qq⟩, temp⟩
  )

  return fun a => (temp.lookup a).get sorry

/-- maps strings to values of δ by their `Role.name` -/
private def endpointFromString (s: String): IO (Endpoint) :=
  let ep_opt: Option δ := Role.ofString? s

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    return ⟨ep⟩
  else
    throw (IO.userError s!"{s} is no valid endpoint")


/--
class for a well defined entry point into the library
-/
class ChorMain where
  /--
  choreographic main function. The List of strings corresponds to command line input per node, starting after the endpoint argument.
  The main function starts by including every Role.
  -/
  main: [Endpoint] -> Faceted (List String) -> Choreo all (sorry) (Faceted UInt32)

/--
Main Entry point. users shall call this by:
main := CHOR_ENTRYPOINT
-/
def CHOR_ENTRYPOINT
  [cm: ChorMain]
  (args: List String)
  (cfg: dbg_cfg :=dbg_cfg_default)
  : IO UInt32 := do
  if h:(args.length >= 1) then
    let mode := args[0]'(h)
    let _ep: Endpoint <- endpointFromString mode
    IO.clearTerminal

    if cfg.print_EP then
      IO.println (
        "-> recv ->".dyeBack Color.Blue
        ++ "<- send <-".dyeBack Color.Purple
        ++ "\n"
      )
      IO.println s!"{"init network".dyeFont Color.Yellow}"
      IO.println (s!"<<<{Role.name ep}>>>".dye Color.Black Color.White)

    let net <- init_network (cfg:=cfg)

    IO.println s!"{"start choreo".dyeFont Color.Yellow}"
    IO.println ((s!"<<<{Role.name ep}>>>".dye Color.Black Color.White) ++ "\n")

    let _epp := EPP (net := net) (cfg:=dbg_cfg_default) (p := all)

    let cmain := cm.main (Faceted.of (fun _ => (args.drop 1)))

    let res <- cmain
    IO.println s!"EXIT_CODE: {res ep (by simp)}"
    return res ep (by simp)
  else
    throw (IO.userError s!"no endpoint argument\nenter endpoint as first argument")
