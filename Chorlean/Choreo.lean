import Mathlib.Data.List.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Chorlean.utils
import Chorlean.Free
import Batteries.Data.Array
import Chorlean.Role
variable [Role]



-- A faceted Unit type can trivially be unfaceted for users since there is only a singular value
instance: Coe ( Unit) Unit where
  coe _ := ()



-- Endpoint class. used to propagate the endpoint through the library

variable [r:Role]
class Endpoint where
  private mk::
  private endpoint: δ

variable [ep_inst: Endpoint]
private abbrev ep: δ := ep_inst.endpoint
noncomputable abbrev ep' := ep

/--
Type for located variables.
It is defined by a proposition over a δ Location
and maps a proof of this proposition for the endpoint to a value
-/
def Located (p: δ -> Prop) (α: Type) := (p ep) -> α
-- Notation for distributed values that depends on a census proposition@֍


notation:max a "@" p  => Located p a

-- sounds like it should make sense to me
axiom Knowledge
  {loc: δ}
  {p: Prop}
  (loc_p:(ep = loc) -> p)
  : p


axiom Knowledge2
  {α:Type}
  {gv: α}
  {value:α}
  {loc: δ}
  (loc_knows:(ep = loc) -> gv = value)
  : gv = value



axiom Knwoledge'
  {α:Type}
  {p:δ->Prop}
  (lv: α @ p)
  (value:α)
  (loc: δ)
  (knows: p loc:=by decide)
  (idk: ∀ z: (ep = loc), lv (by revert knows; simp [z]) = value)
  : ∀ z: (p ep), lv (by revert knows; simp [z]) = value

def Faceted α :=  (l:δ) -> α @ (· = l)

notation:max "💎" a => Faceted a

class Unwrap (p: δ -> Prop) where
   un {q: δ -> Prop}: (α @ q) -> (impl: ∀ x:δ,  p x -> q x := by decide) -> α

-- class to expose faceted values to the user in a controlled environment.
class Unfacet where
   get: δ

instance: Coe (Faceted Unit) Unit where
  coe _ := ()

-- instance {p q:δ -> Prop} (impl: p x -> q x := by decide) [Unwrap p] : CoeOut (α @ q) α where
--   coe x := Unwrap.un x


/--removes nested layers of `faceted`-/
-- def Faceted.flatten: Faceted (Faceted α ) -> Faceted α
-- | x => x

-- users may create faceted values out of normal ones.
-- through the normal constructor users could obtain the underlying value.
def Faceted.of (v:α): Faceted α := fun _ _ => v

-- Coe instance to implicetely facet types
instance: Coe α (Faceted α)  where
  coe := Faceted.of

-- unfacetting a Faceted Value at a location l.
-- since we only look at this value from a single location it is safe to unfacet it.
def Faceted.lookInto (f: Faceted α) (l: δ):  α @ (·=l) :=
 f l

-- all is a function that maps everything to true - "everywhere"
-- nobody is a function that maps everything to false - "nowhere"
notation:max "all"  => (fun _ => true)
notation:max "nobody"  => (fun _ => false)

-- Coe instance to implicetely unpack Located
instance (p: δ -> Prop) (cen: p ep): CoeOut (α @ p) α where
  coe x := x cen

-- coerces Located Unit types into Unit
-- lets you omit variable assignement with let in do notation for Unit Choreos
instance: CoeOut (Located o Unit) Unit where
  coe _ := ()

instance: Coe Unit (Located o Unit) where
  coe _ := fun _ => ()



-- creates a distributed value by deciding over a proposition with access to the endpoint
def Located.wrap {p: δ -> Prop} (v:α) [Decidable (p ep)]: α @ p :=
  fun _x =>
    if h:(p ep) then
      v
    else
      by contradiction

-- unwrapping a located value by a proof of p for the endpoint.
-- function can be omitted but makes the intent more clear in code
abbrev Located.unwrap' {p: δ -> Prop} (census: p ep): (Located p α) -> α
| gv => gv census

def Located.cast {p p': δ -> Prop}  (gv:α @ p') (impl: {x:δ}-> (p x -> p' x) := by decide): (α @ p) :=
  fun c => gv (impl c)

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




def Faceted.map (f: α -> β) (x: 💎α): 💎β := f ((x ep) rfl)

instance: Monad Faceted where
  pure := Faceted.of
  bind x f := f ((x ep) rfl)
  map := Faceted.map





notation:max a "+++" b => Located.combine a b

def Located.owners  {p: δ -> Prop} [∀ (x:δ), Decidable (p x)]: Located p α -> List δ :=
  fun _ => (FinEnum.toList δ).filter p


abbrev Located.flatten (v: Located p (Located q α)) : Located (fun x => p x ∧ q x) α  :=
  fun pq => v (And.left pq) (And.right pq)


abbrev Located.exclusive {loc:δ} (gv: (💎α) @ (· =loc)): (α @ (· =loc)) :=
  fun cen => (gv cen).lookInto loc cen

abbrev Faceted.alone {loc:δ} (lf: (💎α)) (known_ep: ep = loc): α :=
  lf.lookInto loc known_ep

abbrev Faceted.exclusive {loc:δ} (gv: (💎α) @ (· =loc)): (α @ (· =loc)) :=
  fun cen => (gv cen).alone cen

def Faceted.from  (lvs: (l:δ) -> α @ (· = l))  : 💎α  :=
  Faceted.of (lvs ep rfl)

-- ToString instance for distributed values with an ToString instance on the value type.
-- prints "Empty" if the value is not present on the machine
instance [ToString μ] {p: δ -> Prop} [Decidable (p ep)]: ToString (μ @ p) where
  toString x :=
    if h:(p ep) then
      let val := x h
      toString val
    else
      "Empty"

abbrev Faceted.unwrap (f:Faceted α) (ep': {l:δ // ep = l}): α :=
  f.lookInto ep'.val ep'.prop

notation:max  f "🔎" e => Faceted.unwrap f e


def Located.unwrap {p p': δ -> Prop} (gv:α @ p') (cen: p ep) (impl: ∀ x:δ, p x -> p' x := by decide): α :=
  gv (impl ep cen)

-- Signature for Networked programs.
-- allows for sending and receiving messages.
-- adheres to [Arch] and prohibits self referencing
inductive NetEff: Type → Type 1
| send {μ: Type} [Serialize μ] : (r:δ) → (p:ep ≠ r) -> (Role.adj ep r p) → μ → NetEff Unit
| recv : (s:δ) → (p:ep ≠ s) -> (Role.adj s ep p.symm) →  (μ: Type) → [Serialize μ] → NetEff μ

-- more sockets than necessary but eh
structure Channel (sender receiver: δ) where
  recv_sock: Socket @ (·=receiver)
  send_sock: Socket @ (·=sender)

def init_sending_channel (sender :δ) (addr: Address):  IO (Socket @ (·=sender)) := do
  if h:(ep = sender) then
    let sock ← addr.connect_to
    return (fun _ => sock)
  else
    return (fun x => by contradiction)

def init_receiving_channel  (receiver: δ) (addr: Address):  IO (Socket @ (·=receiver)) := do
  if h:(ep = receiver) then
    let sock ← addr.listen_on
    return (Located.wrap sock)
  else
    return (fun x => by contradiction)


-- epp for initializing a channel between two locations and printing dbg info to console
def init_channel' (sender receiver: δ) (r_sock: Socket @ (· = receiver)) (addr: Address):  IO (Channel sender receiver) := do

  let send_sock ← init_sending_channel sender addr
  return ⟨r_sock, send_sock⟩


-- epp for initializing a channel between two locations and printing dbg info to console
def init_channel (sender receiver: δ) (addr: Address):  IO (Channel sender receiver) := do

  if(dbg_print_init_sockets ∧ sender = ep) then
    IO.println (s!"<- {reprName receiver} <-".dye Color.White Color.Purple)
  if(dbg_print_init_sockets ∧ receiver = ep) then
    IO.println (s!"-> {reprName sender} ->".dye Color.White Color.Blue)
  let recv_sock ← init_receiving_channel receiver addr
  let send_sock ← init_sending_channel sender addr
  return ⟨recv_sock, send_sock⟩

-- distributed datastructure containing all TCP Sockets
structure Network where
  channels: List (Σ (id: δ×δ), Channel id.1 id.2)
  complete: ∀ (k : δ×δ), (ne:k.1 ≠ k.2) → (Role.adj k.1 k.2 ne) → (channels.dlookup k).isSome

-- helper function to look up channels
def Network.getChannel (net: Network) (k:δ×δ) (ne: k.1 ≠ k.2) (adj: Role.adj k.1 k.2 ne) : Channel k.1 k.2 :=
  (net.channels.dlookup k).get (by simp [net.complete, ne, adj])

-- calculates unique addresses for location pairs with ascending port numbers, starting at start_port
def default_adress (k:δ × δ) (start_port: Nat := 2222):  Address :=
  let port: Nat := start_port + (FinEnum.equiv k.1) * (FinEnum.card δ) + (FinEnum.equiv k.2)
  .v4  (.mk 127 0 0 1) port.toUInt16

-- connects all nodes according to the [Arch] instance by TCP.
-- returns a network
def init_network (as:  δ×δ -> Address := default_adress)
  [∀ (a b: δ), (ne: a≠b) -> Decidable (Role.adj a b ne)]
  : IO Network := do
  let filtered := (FinEnum.toList (δ×δ)).filter (fun k => k.1 ≠ k.2 ∧ ((ne: k.1 ≠ k.2) -> Role.adj k.1 k.2 ne))

  let progs: List (Σ (k: (δ×δ)), Address)  := filtered.map (fun k => ⟨k, as k⟩ )
  let channels_prog: IO (List (Σ (k: δ×δ), Channel k.1 k.2)):= progs.mapM (fun x => do
    let id := x.1
    let chan: Channel id.1 id.2 ←  init_channel id.1 id.2 x.2
    return ⟨id, chan⟩ )
  let cs ← channels_prog

  if(dbg_print_init_sockets) then
    let padding := (FinEnum.max_name_len (α:= δ)) * 2 + 19
    IO.println ((repeat_string "-" padding) ++ "\n")
  return {
            channels := cs
            complete := fun k => by
              simp [List.dlookup_isSome, List.keys]
              intro x y
              sorry -- TODO might be complicated to prove... maybe the function should be stated differently
              done
          }

-- lifts NetEff into IO by sending and receiving messeges over the TCP Sockets of Network
instance NetEPP (net: Network): MonadLiftT NetEff IO where
  monadLift x := match x with
  | NetEff.send r p q m=> do
    let ep := ep
    let ch := net.getChannel ⟨ep, r⟩ p q
    let sock := ch.send_sock (by simp)
    if dbg_print_net_msgs then
      let send_text := s!"<- {reprName r} <-".dyeBack Color.Purple
      IO.println s!"{send_text} {Serialize.pretty m}"
    sock.send_val2 m

  | NetEff.recv s p q μ => do
    let ep := ep
    let c := net.getChannel ⟨s, ep⟩ (Ne.symm p) q
    let sock := c.recv_sock (by simp)

    let res ← sock.recv_val2
    if dbg_print_net_msgs then
      let recv_text := s!"-> {reprName s} ->".dyeBack Color.Blue
      IO.println s!"{recv_text} {Serialize.pretty res}"
    return res

-- instance {δ:Type} [S: LocTy δ] {p: δ → Prop}: LocTy (Subtype p (α:=δ)) where
--   sig x := match x with
--     | ⟨w, _⟩ => S.sig w
--   executable x := match x with
--      | ⟨w, _⟩ => S.executable w

-- auxiliary Effect, coproduct of net_eff and local_eff
@[reducible] def LocalProgramEff := NetEff ⨳ IO--(Role.sig ep)
--@[reducible] def LocalProgramEff (δ:Type) [sig:LocTy δ] [Endpoint δ]:= (NetEff δ) ⨳ IO

-- A Monad for Local Effects where leff is the Effect Signature
@[reducible] def LocalM := Free (LocalProgramEff)





/--
(currently monad because annoying lean rules... maybe mutual with Free would work)
Signature Type for Choreographies.
Choreographies are parameterized by and cenus, proving a proposition of ep
The signature allows to Broadcast values, resulting in a replicated value at every location
Par starts a IO Program that will run at every endpoint resulting in a Faceted Value
-/
inductive Choreo: (p:δ -> Prop) -> (census: p ep) ->  Type → Type 1 where
| Broadcast {μ:Type} [Serialize μ]
  {q: δ -> Prop}
  [∀ x, Decidable (p x)]
  [∀ x, Decidable (q x)]
  (sender: δ)
  (msg: μ @ q)
  (adj:  ∀ (l':δ), p l' -> ¬(q l') -> (ne: sender ≠ l') -> (Role.adj sender l' ne))
  (ex: p sender)
  (owns: q sender)
  --(next: (μ @ (fun x => p x ∨ q x)) -> Choreo p c α)
  (next: {x:μ // (h:(ep = sender)) -> x = (msg (by simp [owns, h]))} -> Choreo p c α)
  :
  Choreo p c α
| Par
  {c: p ep}
  --(prog: Free (((FinEnum.toList δ).filter p).foldl ) β)
  (prog: IO β)
  --(alone: ((FinEnum.toList δ).filter p).length = 1)
  (next: ((r:δ) -> β @ (· = r)) -> Choreo p c α)
  :
  Choreo p c α
| Enclave
  (p': δ -> Prop) [Decidable (p' ep)]
  (subChor: (c': p' ep) -> Choreo p' c' β)
  (imp: ∀ (x:δ),  p' x -> p x)
  (next: (β @ p') -> Choreo p c α)
  :
  Choreo p c α
| Return
  (v:α):
  Choreo p c α

def Choreo.bind {p: δ -> Prop} {c: p ep} {α β : Type} : Choreo p c α → (α → Choreo p c β) → Choreo p c β
| Choreo.Par prog next (α:=α), cont =>
  Choreo.Par prog (fun x => Choreo.bind (next x) cont)

| Choreo.Broadcast v adj ex ex2 next (sender:=loc) (p:=p), cont =>
  Choreo.Broadcast loc v adj ex ex2 (fun x => Choreo.bind (next x) cont)

| Choreo.Enclave p' subChor imp next, cont =>
  Choreo.Enclave p' subChor imp (fun x => Choreo.bind (next x) cont)

-- | Choreo.Gather loc fv adj next, cont =>
--   Choreo.Gather loc fv adj (fun x => Choreo.bind (next x) cont)

| Choreo.Return v, cont =>
  (cont v)

-- annoyingly its own monad and not re-using Free
instance: Monad (Choreo p c) where
  pure := Choreo.Return
  bind := Choreo.bind


-- projects a Chor to a LocalM by adding the neccesarry NetEffects
def Choreo.epp' {p: δ -> Prop} (c: p ep) {α :Type}: (Choreo p c α) → Free (LocalM) α
| Choreo.Par prog next (β:=β)  (α:=α) => do
  --have unfacet: Unfacet := ⟨fun x => x.lookInto ep rfl⟩
  --have unwrap: Unwrap p := ⟨fun x y => x y⟩
  let res <-prog
  (next (fun _ => Located.wrap res)).epp'

| Choreo.Broadcast v adj ex next (sender:=sender) (μ:= μ) (p:=p) (q:=q) (owns := owns) => do

  if h1:(ep = sender) then

    let v := (v (cast (congrArg q (id (Eq.symm h1))) owns))

    for x in (FinEnum.toList δ) do
      if h3: ¬(q x) ∧ (p x) ∧ (ep ≠ x) then
        NetEff.send x h3.right.right (by simp [h1]; exact (adj x h3.right.left h3.left
          (by simp [h1.symm, h3.right.right]))) v
    (next ⟨v, fun _ => rfl⟩).epp'
  else if h2:(q ep) then
    let v := v h2
    (next ⟨v, (fun x => False.elim (h1 x))⟩).epp'
  else
    let v ← NetEff.recv sender h1 (adj ep c h2 (fun a => h1 a.symm)) μ
    (next ⟨v, (fun x => False.elim (h1 x))⟩).epp'


| Choreo.Enclave p' subChor imp next =>
  if h:(p' ep) then do
    have unwrap: Unwrap p' := ⟨fun x y => x (y ep h)⟩
    let x := subChor h
    let y <- x.epp'
    (next (fun _ => y)).epp'
  else
    (next (fun _ => by contradiction)).epp'

| Choreo.Return v =>
  return v

-- lifts Choreo into IO
instance EPP
  (p: δ -> Prop) {c: p ep}
  (net: Network) : MonadLiftT (Choreo p c) IO where
   monadLift x :=
    let _netlift := NetEPP net
    let _ep_io_lift := Role.executable (ep)
    (Choreo.epp' c x)

/--
runs a program, specified by free Monads, in parallel for all roles.
-/
def par
  (cont: [∀ (x:{y:δ // p y}), MonadLiftT (Free (Role.sig x)) (Free (Role.sig ep))] -> IO α)
  :
  Choreo p c (💎α)
  :=
  have: ∀ (x:{y:δ // p y}), MonadLiftT (Free (Role.sig x)) (Free (Role.sig ep)) := sorry
  Choreo.Par cont (fun x => Choreo.Return x)

/--
runs a program, specified by free Monads, in parallel for all roles.
-/
def par2
  (a b: δ)
  {c: (fun x => x = a ∨ x = b) ep}
  (prog: (Free ((Role.sig a) ⇹ (Role.sig b)) α ))
  :
  Choreo (fun x => x = a ∨ x = b) c (💎α)
  :=
  --Choreo.Par prog (fun x => Choreo.Return x)
  sorry

/--
runs a program, specified by free Monads, in parallel for all roles.
-/
def run
  {p: δ -> Prop}  [∀ x, Decidable (p x)]
  {c: p ep}
  (cont: IO α)
  (alone: ((FinEnum.toList δ).filter p).length = 1 := by decide)
  :
  Choreo p c α
  := do
  let res <- par cont
  let e := ((FinEnum.toList δ).filter p)[0]

  return res.alone (loc := ((FinEnum.toList δ).filter p)[0]) (by sorry)


/--
broadcasts a value from one location to all other locations
-/
def bcast {μ:Type} [Serialize μ] [∀ x, Decidable (p x)]
  [∀ (x:δ), Decidable (q x)]
  (sender: δ)
  (msg: μ @ q)
  (adj:  ∀ (l':δ), p l' -> ¬(q l') -> (ne: sender ≠ l') -> (Role.adj sender l' ne) := by decide)
  (ex: p sender := by decide)
  (owns: q sender := by decide)
  :
  Choreo p c {x:μ // (h:(ep = sender)) -> x = (msg (by simp [owns, h]))}
  :=
  Choreo.Broadcast sender msg adj ex owns (fun x => Choreo.Return x)

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
  Choreo.Enclave p' (fun _ => subChor) imp (fun x => Choreo.Return x)



-- returns a list of locations that fullfill 2 predicates, such that the locations are adjecent to every other location that fullills p but not q
-- this list consists of every location able to broadcast a value a@q for census p
abbrev possible_caster (p q : δ -> Prop)
  [∀ x, Decidable (p x)]
  [∀ x, Decidable (q x)]
  : List δ:= ((FinEnum.toList δ).filter
  (fun x => q x ∧ p x ∧  ∀ (l':δ), p l' -> ¬(q l') -> (ne: x ≠ l') -> (Role.adj x l' ne)))


/--
Variant of bcast where the broadcaster is deduced automatically.
-/
def bcast'   {μ:Type} [Serialize μ]
  [∀ x, Decidable (p x)]
  [∀ (x:δ), Decidable (q x)]
  (msg: μ @ q)
  (castable: (possible_caster p q).length > 0 := by decide)
  :
  Choreo p c {x:μ // (h:(ep = ((possible_caster p q)[0]'castable))) -> x = (msg (by sorry))}
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


/--
embedding a choreography containing stricly less roles
-/
def enclave_bcast {μ:Type} [Serialize μ]
  (p': δ -> Prop) [Decidable (p' ep)]
  [∀ x, Decidable (p x)]
  [∀ (x:δ), Decidable (p' x)]
  (subChor: {c': p' ep} -> Choreo p' c' μ)
  (imp: ∀ (x:δ),  p' x -> p x := by decide)
  (castable: (possible_caster p p').length > 0 := by decide)
  :
  Choreo p c μ
  := do
  let temp <- enclave p' subChor imp
  bcast' temp castable



notation:max "【" a "】" b  => enclave ((a)) b
notation:max "【" a "】*" b  => enclave_bcast a b

-- notation:max "【" a "】" b  => enclave (fun x => x ∈ a) b
-- notation:max "【" a "】*" b  => enclave_bcast (fun x => x ∈ a) b

-- /--
-- convenience method that enclaves a par at a single location and unfacets the resulting value
-- -/
-- def locally
--   (loc: δ)
--   (subChor: {c': ep = loc} -> Free (Role.sig loc) α)
--   (ex: p loc := by decide)
--   :
--   Choreo p c (α @ (·=loc))
--   := do
--   let res <- enclave (·=loc) (fun {cen} => do
--       let res <- par ( fun x =>
--         let prog: Free (Role.sig x.val) α := cast (by simp [cen, x.prop.symm]) (subChor (c':= cen))
--         prog
--       )
--       return res.lookInto loc
--   ) (
--     have q: ∀ (x:δ), (x = loc) -> p x := by simp only [forall_eq]; exact ex
--     fun x y => q x y)
--   return res.flatten.cast (impl:=fun a => ⟨a, a⟩)




-- /--
-- convenience method that broadcasts after locally
-- -/
-- def locally_bcast [Serialize μ] [∀ x, Decidable (p x)]
--   (loc: δ)
--   --(subChor: [Census (@ loc)] -> [Unfacet] -> Free (LocSig.sig loc ) μ)
--   (subChor: {c' :ep = loc} -> Free (Role.sig loc) μ)
--   (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) := by decide)
--   (ex: p loc := by decide)
--   :
--   Choreo p c μ
--   := do
--   let res <- locally loc (fun {cen} => subChor (c' := cen)) ex
--   let res' <-bcast (sender:=loc) res (fun l' a _ ne => adj l' a ne) (ex:=ex) rfl
--   return res'

/--
convenience method that communicates the result of a local program from a sender to a receiver
-/
def com  [Serialize μ] [∀ x, Decidable (p x)]
  (msg: μ @ (· = (sender:δ)))
  (receiver: δ)
  --(subChor: [Census (@ loc)] -> [Unfacet] -> Free (LocSig.sig loc ) μ)
  (adj:  (ne: sender ≠ receiver) -> (Role.adj sender receiver ne) := by decide)
  (ex_sender: p sender := by decide)
  (ex_receiver: p receiver := by decide)
  :
  Choreo p c ({x:μ // (h:(ep = sender)) -> x = msg h} @ fun x => x = sender ∨ x = receiver)

  := do
  enclave (p' := fun x => x = sender ∨ x = receiver)
    (imp := by simp only [forall_eq_or_imp, forall_eq]; exact ⟨ex_sender, ex_receiver⟩) (

    bcast sender msg (by simp; exact fun _ ne => adj ne) (Or.intro_left (sender = receiver) rfl) rfl
  )


-- convenience method that enclaves a locally_bcast for a sender and group of receivers
-- def com'  [Serialize μ]  [∀ x, Decidable (p x)]
--   (sender: δ)
--   (receivers: δ -> Prop) [∀ x, Decidable (receivers x)]
--   --(subChor: [Census (@ loc)] -> [Unfacet] -> Free (LocSig.sig loc ) μ)
--   (subChor: {c' :ep = sender} -> Free (Role.sig sender) μ)
--   (adj: ∀ (x:δ), receivers x -> (ne: sender ≠ x) -> (Role.adj sender x ne) := by decide)
--   (ex_sender: p sender := by decide)
--   (ex_receivers: ∀ (x:δ),  receivers x -> p x := by decide)
--   :
--   Choreo p c (μ @ fun x => x = sender ∨ receivers x)
--   := do
--   enclave (p' := fun x => x = sender ∨ receivers x)
--     (imp := by simp only [forall_eq_or_imp, forall_eq]; exact ⟨ex_sender, ex_receivers⟩) (

--     locally_bcast (loc:=sender)
--       (fun {cen} => subChor (c' := cen))
--       (adj:= by simp only [ne_eq, forall_eq_or_imp, not_true_eq_false, IsEmpty.forall_iff, true_and]; exact fun a a_1 ne => adj a a_1 ne)
--       (ex := by simp)
--   )

/--
-- gathers all values of a faceted value in a single location
-/
def gather'  [Serialize μ]  {p q: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]  [∀ x, Decidable (q x)]
  (loc: δ)
  (data: (💎μ) @ q)
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: l' ≠ loc) -> (Role.adj l' loc ne) := by decide)
  :
  Choreo p c (({l // p l ∧ q l} -> μ) @ (· = loc))
  := do

    let filtered := (FinEnum.toList δ).filter (fun x => p x ∧ q x)

    let temp: List ({l // p l ∧ q l} × (μ @ (· = loc))) <- filtered.mapM (fun x => do
      let xx := List.filter_true filtered

      have qq: p x := by sorry
      have qq': q x := by sorry


      let v <- com
        (sender:=x)
        (receiver:=loc)
        (ex_sender := qq)
        (ex_receiver:= ex)
        (adj := fun ne => adj x qq ne)
        (
          fun {cen'} =>
          let temp_res: (💎μ) @ (· = x) := fun {cen} => (data (by simp [cen]; exact qq'))
          let res := Faceted.exclusive temp_res
          Faceted.exclusive temp_res cen'
        )

      return ⟨⟨x, qq, qq'⟩, v.cast (impl := fun a => Or.inr a)⟩
    )
    return fun a b => ((temp.lookup b).get (sorry)) a


/--
-- gathers all values of a `Faceted` at a single location
-/
def gather  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  (loc: δ)
  (data: 💎μ)
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: l' ≠ loc) -> (Role.adj l' loc ne) := by decide)
  :
  Choreo p c (({l // p l} -> μ) @ (· = loc))
  := do
    let mut vals: List ({l // p l} × (μ @ (· = loc))) := []
    let filtered := (FinEnum.toList δ).filter p

    let temp: List ({l // p l} × (μ @ (· = loc))) <- filtered.mapM (fun x => do
      let xx := List.filter_true vals

      --have h : x ∈ List.filter p (FinEnum.toList δ) := by simp; trivial

      --have h: x ∈ filtered := by simp [List.filterM]
      --let q := List.of_mem_filter h
      have qq: p x := by sorry
      --let xxx := List.of_mem_filter h
      --have qq: x ∈ (FinEnum.toList δ).filter p := by refine List.mem_filter_of_mem (by exact FinEnum.mem_toList x) (by simp [List.of_mem_filter]; )


      let v <- com
        (sender:=x)
        (receiver:=loc)
        (ex_sender := qq)
        (ex_receiver:= ex)
        (adj := fun ne => adj x qq ne)
        (fun {cen} => (data.lookInto x cen))

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

  enclave (· = loc) (fun {cen} => do
    let mut res: List μ := []
    for x in (FinEnum.toList δ) do
      if h: p x then
        res := merge res ((temp cen) ⟨x, h⟩)
    return res
    )
    (by simp; exact ex)



/--
broadcast different values of the same type
-/

def scatter  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  {loc: δ} [Decidable (ep = loc)]
  (data:  ({l // p l} -> μ) @ (· = loc))
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) := by decide)
  :
  Choreo p c (Faceted μ)
  := do

  let mut lst: List (Σ (owner:{l // p l}), (μ @ (· = owner.val))) := []

  for x in (FinEnum.toList δ) do
    if h: (p x) then

      let lv <- com (data.map (fun y => y ⟨x, h⟩)) x (fun ne => adj x h ne) ex h
      lst := lst.concat ⟨⟨x, h⟩, lv.cast (impl := fun {x_1} a => Or.inr a)⟩
  let res :=  ((lst.dlookup ⟨ep, c⟩).get (by sorry)) (by trivial)
  return Faceted.of res



def chunk_size  (l: δ) (data_size: Nat) :=
  let id := FinEnum.equiv l
  let res := data_size % (FinEnum.card δ)
  if id < res then
    res + 1
  else
    res

/--
scatters items of a list evenly across nodes. The first portion of nodes might handle one additional item if there is a rest
-/
def scatterList  [Serialize μ]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
  {loc: δ} [Decidable (ep = loc)]
  (data:  (List μ) @ (· = loc)) [Decidable (p loc)]
  (ex: p loc := by decide)
  (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) := by decide)
  :
  Choreo p c (Faceted (List μ))  := do

  let N := (FinEnum.card {l // p l})
  let data':  ({l // p l} -> List μ) @ (· = loc) :=
    fun x y  =>

      let id := FinEnum.equiv y
      let chunk_size := (data x).length / N
      let rest := (data x).length % N
      let chunk_start := (id.val * chunk_size) + (min rest id.val)

      let chunk_size :=
        if id < rest then
          chunk_size + 1
        else
          chunk_size
      (data x).fromTo chunk_start chunk_size

  scatter data' ex adj

-- def par_map  [Serialize α] [Serialize β]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
--   {loc: δ} [Decidable (ep = loc)]
--   (data:  ({l // p l} -> α) @ (· = loc))
--   (f: α -> β)
--   (ex: p loc := by decide)
--   (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) ∧ (Role.adj l' loc ne.symm) := by decide)
--   :
--   Choreo p c (({l // p l} -> β) @ (· = loc)) := do

--   let chunks  <- scatter data ex (fun l ex ne => (adj l ex ne).left)
--   gather loc (chunks.map f) ex (fun l ex ne => (adj l ex ne.symm).right)

-- def par_map_list  [Serialize α] [Serialize β]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
--   {loc: δ} [Decidable (ep = loc)]
--   (data:  (List α) @ (· = loc))
--   (f: α -> β)
--   (merge: List β -> List β -> List β := List.append)
--   (ex: p loc := by decide)
--   (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) ∧ (Role.adj l' loc ne.symm) := by decide)
--   :
--   Choreo p c ((List β) @ (· = loc)) := do

--   let chunks  <- scatterList data ex (fun l ex ne => (adj l ex ne).left)
--   gatherList loc (chunks.map (fun x => x.map f)) merge ex (fun l ex ne => (adj l ex ne.symm).right)

-- def par_mapM  [Serialize α] [Serialize β]  {p: δ -> Prop} {c: p ep} [∀ x, Decidable (p x)]
--   {loc: δ} [Decidable (ep = loc)]
--   (data:  ({l // p l} -> α) @ (· = loc))
--   (f: α ->  Free (Role.sig ep) β)
--   (ex: p loc := by decide)
--   (adj:  ∀ (l':δ), p l' -> (ne: loc ≠ l') -> (Role.adj loc l' ne) ∧ (Role.adj l' loc ne.symm) := by decide)
--   :
--   Choreo p c (({l // p l} -> β) @ (· = loc)) := do

--   let chunks  <- scatter data ex (fun l ex ne => (adj l ex ne).left)
--   let res <- par (fun eep => f (chunks🔎eep ))
--   gather loc res ex (fun l ex ne => (adj l ex ne.symm).right)


-- maps strings to values of δ.
-- this works by Repr wich uses the actual declaration names of a type
private def endpointFromString (s: String): IO (Endpoint) :=
  let ep_opt: Option δ := FinEnum.ofString? s

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
  : IO UInt32 := do
  if h:(args.length >= 1) then
    let mode := args[0]'(h)
    let _ep: Endpoint <- endpointFromString mode
    IO.clearTerminal

    if dbg_print_EP then
      IO.println (
        "-> recv ->".dyeBack Color.Blue
        ++ "<- send <-".dyeBack Color.Purple
        ++ "\n"
      )
      IO.println s!"{"init network".dyeFont Color.Yellow}"
      IO.println (s!"<<<{reprName ep}>>>".dye Color.Black Color.White)

    let net <- init_network

    IO.println s!"{"start choreo".dyeFont Color.Yellow}"
    IO.println ((s!"<<<{reprName ep}>>>".dye Color.Black Color.White) ++ "\n")
    let _nepp := NetEPP net
    let _epp := EPP (p:= fun _ => true) net

    let cmain: Choreo all rfl (ep_inst := _ep)  (Faceted UInt32) := cm.main (Faceted.of (args.drop 1))
    --let cmain: Choreo all rfl (ep_inst := _ep)  (Faceted UInt32) := sorry

    let res <- cmain
    IO.println s!"EXIT_CODE: {res.lookInto ep rfl}"
    return res.lookInto ep rfl
  else
    throw (IO.userError s!"no endpoint argument\nenter endpoint as first argument")
