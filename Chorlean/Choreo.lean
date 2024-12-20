import Mathlib.Data.List.Sigma
import Chorlean.utils
import Chorlean.Free
import Batteries.Data.Array
import Chorlean.Role

variable [Role]
variable {cfg:dbg_cfg}

-- A faceted Unit type can trivially be unfaceted for users since there is only a singular value
instance: Coe ( Unit) Unit where
  coe _ := ()

variable [Role]

-- Endpoint class. used to propagate the endpoint through the library
class Endpoint where
  private mk::
  private endpoint: δ

variable [Endpoint]
private abbrev ep: δ := Endpoint.endpoint
noncomputable abbrev ep' := ep

/--
Type for located variables.
It is defined by a proposition over a δ Location
and maps a proof of this proposition for the endpoint to a value
-/
def Located (p: δ -> Prop) (α: Type) := (p ep) -> α

-- Notation for located values
notation:max a "@" p  => Located p a

/-- `Faceted`  maps locations to a value that is only located at that location-/
def Faceted α :=  (l:δ) -> α @ (· = l)

/-- wraps values into `Faceted`.-/
def Faceted.of (v:α): Faceted α := fun _ _ => v

/-- Coe instance to implicetely facet types -/
instance: Coe α (Faceted α)  where
  coe := Faceted.of

/-- function that maps everything to true - "everywhere"-/
notation:max "all"  => (fun _ => true)
/-- function that maps everything to false - "nowhere"-/
notation:max "nobody"  => (fun _ => false)

-- Coe instance to implicetely unpack Located
instance (p: δ -> Prop) (cen: p ep): CoeOut (α @ p) α where
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

/-- wraps into a `Located` value by deciding over the predicate with access to the endpoint-/
def Located.wrap {p: δ -> Prop} (v:α) [Decidable (p ep)]: α @ p :=
  fun _x =>
    if h:(p ep) then
      v
    else
      by contradiction

def Located.bind {α β : Type} [Decidable (p (ep))] (x: α @p) (f: α → β @p):  β @p  :=
  if h:(p ep) then
    let v := x h
    f v
  else
    fun y => by contradiction

def Located.map {p: δ -> Prop} [Decidable (p ep)] (f: α -> β) (x: α @ p): β @ p :=
 if h:(p ep) then
      let v := x h
      fun _ => f v
    else
      fun y => by contradiction

instance {p: δ -> Prop} [Decidable (p ep)]: Monad (Located p) where
  pure x := Located.wrap x
  bind := Located.bind
  map := Located.map

def Faceted.map (f: α -> β) (x: Faceted α): Faceted β := f ((x ep) rfl)

instance: Monad Faceted where
  pure := Faceted.of
  bind x f := f ((x ep) rfl)
  map := Faceted.map

def Located.owners  {p: δ -> Prop} [∀ (x:δ), Decidable (p x)]: Located p α -> List δ :=
  fun _ => (Fin.enumerate N).filter p

/-- removes one layer of a nested `Located`-/
def Located.flatten (v: Located p (Located q α)) : Located (fun x => p x ∧ q x) α  :=
  fun pq => v (And.left pq) (And.right pq)

/-- abbreviation for looking at a `Faceted` from one singular role-/
abbrev Faceted.exclusive {loc:δ} (lf: (Faceted α) @ (· =loc)): (α @ (· =loc)) :=
  fun cen => (lf cen) loc cen

/-- ToString instance for distributed values with an ToString instance on the value type.
    "Empty", if the value is not present on the machine-/
instance [ToString μ] {p: δ -> Prop} [Decidable (p ep)]: ToString (μ @ p) where
  toString x :=
    if h:(p ep) then
      let val := x h
      toString val
    else
      "Empty"

/-- maps `Located` into another `Located` by evidence that (p x -> p' x).-/
def Located.cast {p p': δ -> Prop}  (gv:α @ p') (impl: {x:δ}-> (p x -> p' x) := by decide): (α @ p) :=
  fun c => gv (impl c)

/--Signature for Networked programs.
   allows for sending and receiving messages.
   adheres to adjacency of roles and prohibits self referencing-/
inductive NetEff: Type → Type 1
| send {μ: Type} [Serialize μ] : (r:δ) → (p:ep ≠ r) -> (Role.adj ep r p) → μ → NetEff Unit
| recv : (s:δ) → (p:ep ≠ s) -> (Role.adj s ep p.symm) →  (μ: Type) → [Serialize μ] → NetEff μ

/-- Channel structure that distributes two sockets over a sender and receiver end-/
structure Channel (sender receiver: δ) where
  recv_sock: Socket @ (·=receiver)
  send_sock: Socket @ (·=sender)

/--connects a sender role to an adress-/
def init_sending_channel (sender :δ) (addr: Address):  IO (Socket @ (·=sender)) := do
  if h:(ep = sender) then
    let sock ← addr.connect_to
    return (fun _ => sock)
  else
    return (fun x => by contradiction)

/--listens for a adress-/
def init_receiving_channel  (receiver: δ) (addr: Address):  IO (Socket @ (·=receiver)) := do
  if h:(ep = receiver) then
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
  complete: ∀ (k : δ×δ), (ne:k.1 ≠ k.2) → (Role.adj k.1 k.2 ne) → (channels.dlookup k).isSome

/-- helper function to look up channels -/
def Network.getChannel (net: Network) (k:δ×δ) (ne: k.1 ≠ k.2) (adj: Role.adj k.1 k.2 ne) : Channel k.1 k.2 :=
  (net.channels.dlookup k).get (by simp [net.complete, ne, adj])

/-- calculates unique addresses for location pairs with ascending port numbers, starting at start_port-/
def default_adress (k:δ × δ) (start_port: Nat := 2222):  Address :=
  let port: Nat := start_port + k.1 * (Role.N) + k.2
  .v4  (.mk 127 0 0 1) port.toUInt16

/-- connects all nodes according to adjacency by TCP.
    returns a network-/
def init_network (as:  δ×δ -> Address := default_adress)
  [∀ (a b: δ), (ne: a≠b) -> Decidable (Role.adj a b ne)]
  : IO Network := do
  let filtered := ((Fin.enumerate N).product (Fin.enumerate N)).filter (fun k => k.1 ≠ k.2 ∧ ((ne: k.1 ≠ k.2) -> Role.adj k.1 k.2 ne))

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
              intro x y
              sorry -- TODO mightt be complicated to prove... maybe the function should be stated differently
              done
          }

/-- lifts NetEff into IO by sending and receiving messeges over the TCP Sockets of Network -/
instance NetEPP (net: Network): MonadLiftT NetEff IO where
  monadLift x := match x with
  | NetEff.send r p q m=> do
    let ep := ep
    let ch := net.getChannel ⟨ep, r⟩ p q
    let sock := ch.send_sock (by simp)
    if cfg.print_net_msgs then
      let send_text := s!"<- {Role.name r} <-".dyeBack Color.Purple
      IO.println s!"{send_text} {Serialize.pretty m}"
    sock.send_val2 m (cfg:=cfg)

  | NetEff.recv s p q μ => do
    let ep := ep
    let c := net.getChannel ⟨s, ep⟩ (Ne.symm p) q
    let sock := c.recv_sock (by simp)

    let res ← sock.recv_val2
    if cfg.print_net_msgs then
      let recv_text := s!"-> {Role.name s} ->".dyeBack Color.Blue
      IO.println s!"{recv_text} {Serialize.pretty res}"
    return res

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
inductive Choreo: (p:δ -> Prop) -> (census: p ep) ->  Type → Type 1 where
| Broadcast {μ:Type} [Serialize μ]
  {q: δ -> Prop}
  [∀ x, Decidable (p x)]
  [∀ x, Decidable (q x)]
  (loc: δ)
  (msg: μ @ q)
  (adj:  ∀ (l':δ), p l' -> ¬(q l') -> (ne: loc ≠ l') -> (Role.adj loc l' ne))
  (ex: p loc)
  (owns: q loc)
  (next: μ -> Choreo p c α)
  :
  Choreo p c α
| Locally
  (loc: δ)
  (prog: IO β)
  (alone: (∀ x, p x -> loc = x) := by decide)
  (next: β -> Choreo p c α)
  :
  Choreo p c α
| Enclave
  {p': δ -> Prop} [Decidable (p' ep)]
  (subChor: (c': p' ep) -> Choreo p' c' β)
  (imp: ∀ x,  p' x -> p x)
  (next: (β @ p') -> Choreo p c α)
  :
  Choreo p c α
| Return
  (v:α):
  Choreo p c α

def Choreo.bind {p: δ -> Prop} {c: p ep} {α β : Type} : Choreo p c α → (α → Choreo p c β) → Choreo p c β
| Choreo.Locally l prog alone next (α:=α), cont =>
  Choreo.Locally l prog alone (fun x => Choreo.bind (next x) cont)

| Choreo.Broadcast v adj ex ex2 next (loc:=loc) (p:=p), cont =>
  Choreo.Broadcast loc v adj ex ex2 (fun x => Choreo.bind (next x) cont)

| Choreo.Enclave subChor imp next, cont =>
  Choreo.Enclave subChor imp (fun x => Choreo.bind (next x) cont)

| Choreo.Return v, cont =>
  (cont v)

instance: Monad (Choreo p c) where
  pure := Choreo.Return
  bind := Choreo.bind

/-- projects a Chor to a LocalM by adding the neccesarry NetEffects -/
def Choreo.epp': (Choreo p c α) → Free (LocalM) α
| Choreo.Locally _ prog _ next => do
  let res <-prog
  (next res).epp'

| Choreo.Broadcast v adj _ex next (loc:=loc) (μ:= μ) (p:=p) (q:=q) (owns := owns) => do
  if h1:(ep = loc) then

    let v := (v (cast (congrArg q (id (Eq.symm h1))) owns))

    for x in (Fin.enumerate N) do
      if h3: ¬(q x) ∧ (p x) ∧ (ep ≠ x) then
        NetEff.send x h3.right.right (by simp [h1]; exact (adj x h3.right.left h3.left
          (by simp [h1.symm, h3.right.right]))) v
    (next v).epp'
  else if h2:(q ep) then
    let v := v h2
    (next v).epp'
  else
    let v ← NetEff.recv loc h1 (adj ep c h2 (fun a => h1 a.symm)) μ
    (next v).epp'

| Choreo.Enclave subChor imp next (p' := p') =>
  if h:(p' ep) then do
    let x := subChor h
    let y <- x.epp'
    (next (fun _ => y)).epp'
  else
    (next (fun _ => by contradiction)).epp'

| Choreo.Return v =>
  return v

/-- lifts Choreo into IO-/
instance EPP
  (p: δ -> Prop) {c: p ep}
  (net: Network) : MonadLiftT (Choreo p c) IO where
   monadLift x :=
    let _netlift := NetEPP net (cfg:=cfg)
    (Choreo.epp' x)


/--
broadcasts a value from one location to all other locations
-/
def bcast' {μ:Type} [Serialize μ] [∀ x, Decidable (p x)]
  [∀ (x:δ), Decidable (q x)]
  (loc: δ)
  (msg: μ @ q)
  (adj:  ∀ (l':δ), p l' -> ¬(q l') -> (ne: loc ≠ l') -> (Role.adj loc l' ne) := by decide)
  (ex: p loc := by decide)
  (owns: q loc := by decide)
  :
  Choreo p c μ
  :=
  Choreo.Broadcast loc msg adj ex owns (fun x => Choreo.Return x)

/--
embedding a choreography containing stricly less roles
-/
def enclave
  (p': δ -> Prop) [Decidable (p' ep)]
  (subChor: {c': p' ep} -> Choreo p' c' α)
  (imp: ∀ (x:δ),  p' x -> p x := by decide)
  :
  Choreo p c (α @ p')
  :=
  Choreo.Enclave (fun _ => subChor) imp (fun x => Choreo.Return x)

/--running a program, requiring a single role to be present-/
def locally'
  (loc: δ)
  (prog: IO α)
  (alone: (∀ x, p x -> loc = x) := by decide)
  :
  Choreo p c α
  := do
  Choreo.Locally loc prog alone (fun x => Choreo.Return x)

/--more convenient version of `locally'`, that figures out the role to run on automatically-/
def locally
  {p: δ -> Prop}
  {c: p ep}
  [∀ x, Decidable (p x)]
  (prog: IO α)
  (ex: p ep := by trivial)
  (alone: (∀ x, p x -> (((Fin.enumerate N).filter p)[0]'sorry) = x) := by decide)
:Choreo p c α
  := do
  let loc := ((Fin.enumerate N).filter p)[0]'(by sorry)
  Choreo.Locally loc prog alone (fun x => Choreo.Return x)

/-- returns a list of locations that fullfill 2 predicates, such that the locations are adjecent to every other location that fullills p but not q
  this list consists of every location able to broadcast a value a@q for census p-/
abbrev possible_caster (p q : δ -> Prop)
  [∀ x, Decidable (p x)]
  [∀ x, Decidable (q x)]
  : List δ := ((Fin.enumerate N).filter
  (fun x => q x ∧ p x ∧  ∀ (l':δ), p l' -> ¬(q l') -> (ne: x ≠ l') -> (Role.adj x l' ne)))

/--
Variant of `bcast'` where the broadcaster is infereed automatically.
-/
def bcast   {μ:Type} [Serialize μ]
  [∀ x, Decidable (p x)]
  [∀ (x:δ), Decidable (q x)]
  (msg: μ @ q)
  (castable: (possible_caster p q).length > 0 := by decide)
  :
  Choreo p c μ
  :=
  Choreo.Broadcast ((possible_caster p q)[0]'castable) msg
  (
    have qq: ((possible_caster p q)[0]'castable) ∈ (possible_caster p q) := by exact List.getElem_mem (possible_caster p q) 0 castable
    have q := List.of_mem_filter qq
    by revert q; simp only [ne_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact
      fun _ _ a l' a_1 a_2 ne => a l' a_1 a_2 ne
  )
  (
    have qq: ((possible_caster p q)[0]'castable) ∈ (possible_caster p q) := by exact List.getElem_mem (possible_caster p q) 0 castable
    have q := List.of_mem_filter qq
    by revert q; simp only [ne_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact
      fun _ a _ => a
  )
  (
    have qq: ((possible_caster p q)[0]'castable) ∈ (possible_caster p q) := by exact List.getElem_mem (possible_caster p q) 0 castable
    have q := List.of_mem_filter qq
    by revert q; simp only [ne_eq, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact
      fun a _ _ => a
  ) (fun x => Choreo.Return x)

/-- combines enclave with broadcasting-/
def enclave_bcast{μ:Type} [Serialize μ]
  [∀ x, Decidable (p x)]
  (p': δ -> Prop)
  [∀ (x:δ), Decidable (p' x)]
  (subChor: {c': p' ep} -> Choreo p' c' μ)
  (imp: ∀ (x:δ),  p' x -> p x := by decide)
  (castable: (possible_caster p p').length > 0 := by decide)
  :
  Choreo p c μ
  := do
  let temp <- enclave p' subChor imp
  bcast temp (castable := castable)

notation:max  a "~" b  => enclave (fun x => x ∈ a) b
notation:max  a "°" b  => enclave_bcast (fun x => x ∈ a) b

/--
  runs a program with access to its identity in parallel by iterating over all present roles and running the program there locally.
-/
def par
  [∀ (x:δ), Decidable (p x)]
  (prog: (r:{r:δ // r = ep}) -> IO α)
  :
  Choreo p c (Faceted α)
  := do

  let filtered := (Fin.enumerate N).filter p

  let temp: List ((r:δ) ×  (α @ (· = r))) <- filtered.mapM (fun x => do
    let res <- enclave (· = x) (fun {c'} => locally' x (prog ⟨x, c'.symm⟩) (fun _ a => id (Eq.symm a))) (by simp [List.filter, List.of_mem_filter]; sorry)
    return ⟨x, res⟩
  )
  return fun x => (temp.dlookup x).get (by sorry)

/--
convenience method that communicates the result of a local program from a sender to a receiver
-/
def com  [Serialize μ] [∀ x, Decidable (p x)]
  (sender receiver: δ)
  (prog: (ep = sender) -> IO μ)
  (adj:  (ne: sender ≠ receiver) -> (Role.adj sender receiver ne) := by decide)
  (ex_sender: p sender := by decide)
  (ex_receiver: p receiver := by decide)
  :
  Choreo p c (μ @ fun x => x = sender ∨ x = receiver)
  := do
  enclave (p' := fun x => x = sender ∨ x = receiver)
    (imp := by simp only [forall_eq_or_imp, forall_eq]; exact ⟨ex_sender, ex_receiver⟩) ( do

    let res <- enclave (· = sender) (fun {cen} => locally' sender (prog cen) (by simp)) (by simp)
    let res' <- bcast' sender res (fun x y z => (by simp [←adj]; sorry)) (by simp) (by simp)
    return res'
  )

/--
gathers the content of a `Faceted` in one single Role
-/
def gather  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  (loc: δ)
  (data: Faceted μ)
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: l' ≠ loc) -> (Role.adj l' loc ne) := by decide)
  :
  Choreo p c (({l // p l} -> μ) @ (· = loc))
  := do
    let mut vals: List ({l // p l} × (μ @ (· = loc))) := []
    let filtered := (Fin.enumerate N).filter p

    let temp: List ({l // p l} × (μ @ (· = loc))) <- filtered.mapM (fun x => do
      let xx := List.filter_true vals
      have qq: p x := by sorry

      let v <- com
        (sender:=x)
        (receiver:=loc)
        (ex_sender := qq)
        (ex_receiver:= ex)
        (adj := fun ne => adj x qq ne)
        (fun {cen} => return (data x cen))

      return ⟨⟨x, qq⟩, v.cast (impl := fun a => Or.inr a)⟩
    )
    return fun a b => ((temp.lookup b).get (sorry)) a

/--
gathers all values of a faceted List in a single location by merging all individual lists.
merging defaults to appending lists
-/
def gatherList  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  (loc: δ)
  (data: Faceted (List μ))
  (merge: List μ -> List μ -> List μ := List.append)
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: l' ≠ loc) -> (Role.adj l' loc ne) := by decide)
  :
  Choreo p c ((List μ) @ (· = loc))
  := do
  let temp <- gather loc data ex adj

  enclave (· = loc) ( fun {cen} =>
    locally' loc (do
    let mut res: List μ := []
    for x in (Fin.enumerate N) do
      if h: p x then
        res := merge res ((temp cen) ⟨x, h⟩)
    return res
    ) (by simp)
  ) (by simp; exact ex)

/--
broadcast different role-dependent values of the same type
-/
def scatter  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  {loc: δ}
  (data:  {l // p l} -> (μ @ (· = loc)))
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) := by decide)
  :
  Choreo p c (Faceted μ)
  := do

  let mut lst: List (Σ (owner:{l // p l}), (μ @ (· = owner.val))) := []

  for x in (Fin.enumerate N) do
    if h: (p x) then

      let lv <- com loc x (fun {cen} =>
          return (data ⟨x, h⟩) cen
        )
        (fun ne => adj x h ne)
        ex
        h

      lst := lst.concat ⟨⟨x, h⟩, lv.cast (impl := fun {x_1} a => Or.inr a)⟩
  let res :=  ((lst.dlookup ⟨ep, c⟩).get (by sorry)) (by trivial)
  return Faceted.of res


/--chunk size helper function for scatterList-/
def chunk_size  (r: δ) (data_size: Nat) :=
  let res := data_size % N
  if r < res then
    res + 1
  else
    res


/--
scatters items of a list evenly across nodes. The first portion of nodes might handle one additional item if there is a rest
-/
def scatterList  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  {loc: δ}
  (data:  (List μ) @ (· = loc))
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) := by decide)
  :
  Choreo p c (Faceted (List μ))  := do

  let N := (FinEnum.card {l // p l})
  let data':  {l // p l} -> (List μ) @ (· = loc) :=
    fun x y =>

      let chunk_size := (data y).length / N
      let rest := (data y).length % N
      let chunk_start := (x * chunk_size) + (min rest x)

      let chunk_size :=
        if x < rest then
          chunk_size + 1
        else
          chunk_size
      (data y).fromTo chunk_start chunk_size

  scatter data' ex adj (loc := loc)

/--
-- gathers all values of a `Faceted` at a every location
-/
def gatherAll  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  (data: Faceted μ)
  :
  Choreo p c ({l // p l}-> μ)
  := do
  let filtered := (Fin.enumerate N).filter p

  let temp: List ({l // p l} × μ) <- filtered.mapM (fun x => do

    have qq: p x := by sorry

    let temp <- bcast' x (data x) (sorry) qq rfl
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
  main: [Endpoint] -> Faceted (List String) -> Choreo all rfl (Faceted UInt32)

/--
Main Entry point. users shall call this by:
main := CHOR_ENTRYPOINT
-/
def CHOR_ENTRYPOINT
  [cm: ChorMain ]
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
    let _nepp := NetEPP net (cfg:=cfg)
    let _epp := EPP (p:= fun _ => true) net (cfg:=cfg)

    let cmain: Choreo all rfl (Faceted UInt32) := cm.main (Faceted.of (args.drop 1))

    let res <- cmain
    IO.println s!"EXIT_CODE: {res ep rfl}"
    return res ep rfl
  else
    throw (IO.userError s!"no endpoint argument\nenter endpoint as first argument")
