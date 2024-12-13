import Socket
import Mathlib.Data.FinEnum
import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Chorlean.utils.Colors


structure dbg_cfg where
    --prints the endpoint at program start
  print_EP := true
  --prints sent and received network bytes
  print_net_msgs := true
  --print info when waiting for connecting to a location
  print_init_sockets := true
  -- print sent and received bytes
  print_net_bytes := false


def dbg_cfg_default: dbg_cfg :=  {}


variable {cfg:dbg_cfg}

-- millis to wait for resend after a failed send try
def send_timeout_duration: UInt32 := 200



def String.toBool?: String -> Option Bool
| "false" => some false
| "true" => some true
| _ => none

def list_to_string_seperated_by (l: List String) (s: String): String :=
  match l with
  |   a::b::as => a ++ s ++ (list_to_string_seperated_by (b::as) s)
  |   a::[] => a
  |   [] => ""

def list_to_continuos_string (l: List String): String :=
  list_to_string_seperated_by l ""

def repeat_string (s: String) (n: Nat): String :=
  if n > 0 then
    repeat_string s (n -1) ++ s
  else
    ""

def newLine (i: Nat): String :=
  "\n" ++ repeat_string "  " i

def pad_until (s: String) (i: Nat): String :=
  s ++ repeat_string " " (i - s.length)


def to_bytes_t (α) := α -> ByteArray
def from_bytes_t (α) := ByteArray -> Except String α

class Serialize (μ: Type) extends ToString μ where
  to_bytes: μ -> ByteArray
  from_bytes: ByteArray -> Except String μ
  type_name: String := "type"
  pretty: μ -> String := fun x => s!"{(ToString.toString x).dyeFont Color.Cyan}: {type_name}"
  toString _ := "-"

variable {μ: Type} [Serialize μ]  -- mu wegen msg Type


def String.byte_count (s:String): Nat :=
  s.toUTF8.size
def String.to_bytes: to_bytes_t String := fun s => s.toUTF8
def String.from_bytes: from_bytes_t String := fun bs => return (String.fromUTF8! bs)


def t1:UInt16 := 600
def t2: UInt8 := t1.toUInt8
def t3: UInt8 := (t1.shiftRight 8).toUInt8

def Bool.to_bytes: to_bytes_t Bool := fun x => (toString x).to_bytes

def Bool.from_bytes: from_bytes_t Bool := fun bs => do
  let str <- String.from_bytes bs
  let bool_opt := String.toBool? str
  match bool_opt with
  | some b =>
    return b
  | none => throw "received unconvertable nat"

def Option.to_bytes [Serialize α]: to_bytes_t (Option α) := fun x => match x with
  | some v =>   [(1:UInt8)].toByteArray ++ (Serialize.to_bytes v)
  | none => [(0:UInt8)].toByteArray

def Option.from_bytes [Serialize μ]: from_bytes_t (Option μ) := fun bs => do
  let uint8_opt := bs.data.get? 0
  match uint8_opt with
  | some v => match v with
    | 1 =>
      let r <- (Serialize.from_bytes (μ:=μ) (bs.extract 1 bs.size))
      return Option.some r
    | _ => return Option.none
  | none => throw "received unconvertable Option"


def UInt8.to_bytes: to_bytes_t UInt8 := fun x =>
  (ByteArray.mkEmpty 1).push x

def UInt8.from_bytes: from_bytes_t UInt8 := fun bs => do
  let uint8_opt := bs.data.get? 0
  match uint8_opt with
  | some v =>
    return v
  | none => throw "received unconvertable UInt8"

def UInt16.to_bytes: to_bytes_t UInt16 := fun x =>
  let lower: UInt8 := x.toUInt8
  let upper: UInt8 := (x.shiftRight 8).toUInt8
  ((ByteArray.mkEmpty 2).push lower).push upper

def UInt16.from_bytes: from_bytes_t UInt16 := fun bs => do
  let lower_opt := bs.data.get? 0
  let upper_opt := bs.data.get? 1
  match lower_opt with
  | some lower =>
     match upper_opt with
    | some upper =>
      return lower.toUInt16 + ((upper).toUInt16.shiftLeft 8)
    | none => throw "received unconvertable UInt16"
  | none => throw "received unconvertable UInt16"

def UInt32.to_bytes: to_bytes_t UInt32 := fun x =>
  let b1: UInt8 := x.toUInt8
  let b2: UInt8 := (x.shiftRight 8).toUInt8
  let b3: UInt8 := (x.shiftRight 16).toUInt8
  let b4: UInt8 := (x.shiftRight 24).toUInt8
  ((((ByteArray.mkEmpty 4).push b1).push b2).push b3).push b4

def UInt32.from_bytes: from_bytes_t UInt32 := fun bs => do
  let b1_opt := bs.data.get? 0
  let b2_opt := bs.data.get? 1
  let b3_opt := bs.data.get? 2
  let b4_opt := bs.data.get? 3

  let b: Option UInt32 := do
    let b1 := (<- b1_opt).toUInt32
    let b2 := (<- b2_opt).toUInt32
    let b3 := (<- b3_opt).toUInt32
    let b4 := (<- b4_opt).toUInt32
    return b1 + b2.shiftLeft 8 +  b3.shiftLeft 16 + b4.shiftLeft 24

  match b with
  | some v =>
    return v
  | none => throw "received unconvertable UInt32"

def UInt64.to_bytes: to_bytes_t UInt64 := fun x =>
  let b1: UInt8 := x.toUInt8
  let b2: UInt8 := (x.shiftRight 8).toUInt8
  let b3: UInt8 := (x.shiftRight 16).toUInt8
  let b4: UInt8 := (x.shiftRight 24).toUInt8
  let b5: UInt8 := (x.shiftRight 32).toUInt8
  let b6: UInt8 := (x.shiftRight 40).toUInt8
  let b7: UInt8 := (x.shiftRight 48).toUInt8
  let b8: UInt8 := (x.shiftRight 56).toUInt8
  ((((((((ByteArray.mkEmpty 8).push b1).push b2).push b3).push b4).push b5).push b6).push b7).push b8

def UInt64.from_bytes: from_bytes_t UInt64 := fun bs => do
  let b1_opt := bs.data.get? 0
  let b2_opt := bs.data.get? 1
  let b3_opt := bs.data.get? 2
  let b4_opt := bs.data.get? 3
  let b5_opt := bs.data.get? 4
  let b6_opt := bs.data.get? 5
  let b7_opt := bs.data.get? 6
  let b8_opt := bs.data.get? 7

  let b: Option UInt64 := do
    let b1 := (<- b1_opt).toUInt64
    let b2 := (<- b2_opt).toUInt64
    let b3 := (<- b3_opt).toUInt64
    let b4 := (<- b4_opt).toUInt64
    let b5 := (<- b5_opt).toUInt64
    let b6 := (<- b6_opt).toUInt64
    let b7 := (<- b7_opt).toUInt64
    let b8 := (<- b8_opt).toUInt64
    return b1 + b2.shiftLeft 8 +  b3.shiftLeft 16 + b4.shiftLeft 24 +
      b5.shiftLeft 32 + b6.shiftLeft 40 + b7.shiftLeft 48 + b8.shiftLeft 56

  match b with
  | some v =>
    return v
  | none => throw "received unconvertable UInt64"



def HEADER_NAT_UINT8: UInt8 := 0
def HEADER_NAT_UINT16: UInt8 := 1
def HEADER_NAT_UINT32: UInt8 := 2
def HEADER_NAT_UINT64: UInt8 := 3
def HEADER_NAT_STRING: UInt8 := 4

def Nat.to_bytes: to_bytes_t Nat := fun n =>
  if n < UInt8.size then
    (ByteArray.mk #[HEADER_NAT_UINT8]) ++ UInt8.to_bytes n.toUInt8
  else if n < UInt16.size then
    (ByteArray.mk #[HEADER_NAT_UINT16]) ++ UInt16.to_bytes n.toUInt16
  else if n < UInt32.size then
    (ByteArray.mk #[HEADER_NAT_UINT32]) ++ UInt32.to_bytes n.toUInt32
  else if n < UInt64.size then
    (ByteArray.mk #[HEADER_NAT_UINT64]) ++ UInt64.to_bytes n.toUInt64
  else
    String.to_bytes (toString n)


def Nat.from_bytes: from_bytes_t Nat:= fun bs => do
  if h:(bs.size > 0) then
    let header := bs.get ⟨0, h⟩
    let payload := bs.extract 1 bs.size
    if header = HEADER_NAT_UINT8 then
      return (<- UInt8.from_bytes payload).toNat
    else if header = HEADER_NAT_UINT16 then
      return (<- UInt16.from_bytes payload).toNat
    else if header = HEADER_NAT_UINT32 then
      return (<- UInt32.from_bytes payload).toNat
    else if header = HEADER_NAT_UINT64 then
      return (<- UInt64.from_bytes payload).toNat
    else
      let str <- String.from_bytes bs
      let nat_opt := String.toNat? str
      match nat_opt with
      | some nat =>
        return nat
      | none => throw "received unconvertable nat"
  else
    throw "received unconvertable nat"

def JoinByteArrayList: List ByteArray -> ByteArray
| [] => ByteArray.mkEmpty 0
| a::as => a ++ JoinByteArrayList as

def List.to_bytes [Serialize a]: to_bytes_t (List a)
| l =>
  let list_size := l.length.toUInt16
  let data := l.map (fun x =>
    let bytes := Serialize.to_bytes x
    let len := bytes.size.toUInt16
    (len.to_bytes ++ bytes)
  )
  let res_byte_array := JoinByteArrayList data
  list_size.to_bytes ++ res_byte_array

def List.from_bytes_rec [Serialize μ]: Nat -> from_bytes_t (List μ)
| 0, bs => .ok []
| x+1, bs => do
  let len <- UInt16.from_bytes (bs.extract 0 2)
  --dbg_trace s!"len: {len}"

  let data <- Serialize.from_bytes (μ:=μ) (bs.extract 2 (2+(len.toNat)))
  let rest <- List.from_bytes_rec (x) (bs.extract (2+(len.toNat)) bs.data.size)
  return [data] ++ rest

def List.from_bytes [Serialize a]: from_bytes_t (List a) := fun bs => do
  let list_size_bytes := bs.extract 0 2
  let list_data_bytes := bs.extract 2 bs.size
  let list_size <- (UInt16.from_bytes (list_size_bytes))
  List.from_bytes_rec list_size.toNat list_data_bytes


open Lean Json ToJson FromJson




instance: Serialize UInt8 where
  from_bytes := UInt8.from_bytes
  to_bytes := UInt8.to_bytes
  type_name := "UInt8"

instance: Serialize UInt16 where
  from_bytes := UInt16.from_bytes
  to_bytes := UInt16.to_bytes
  type_name := "UInt16"

instance: Serialize UInt32 where
  from_bytes := UInt32.from_bytes
  to_bytes := UInt32.to_bytes
  type_name := "UInt32"

instance: Serialize UInt64 where
  from_bytes := UInt64.from_bytes
  to_bytes := UInt64.to_bytes
  type_name := "Nat"

instance: Serialize Nat where
  from_bytes := Nat.from_bytes
  to_bytes := Nat.to_bytes
  type_name := "Nat"


instance: Serialize Bool where
  from_bytes := Bool.from_bytes
  to_bytes := Bool.to_bytes
  type_name := "Bool"

instance: Serialize Unit where
  from_bytes := fun _ => return ()
  to_bytes := fun _ => ByteArray.empty
  type_name := "Unit"


instance [ToString A] [ToJson A] [FromJson A]: Serialize A where
  from_bytes x := do
    let s <- (String.from_bytes x)
    let j <- Json.parse s
    let o <- FromJson.fromJson? j
    return o
  to_bytes x := String.to_bytes (ToJson.toJson x).compress
  type_name := "JsonType"
  toString := ToString.toString


instance: Serialize String where
  from_bytes := String.from_bytes
  to_bytes := String.to_bytes
  type_name := "String"

instance {μ} [Serialize μ]: Serialize (Option μ) where
  from_bytes := Option.from_bytes
  to_bytes := Option.to_bytes
  type_name := s!"Option {Serialize.type_name μ}"

instance (a:Type) [Serialize a]: Serialize (List a) where
  from_bytes := List.from_bytes
  to_bytes := List.to_bytes
  type_name := s!"List ({Serialize.type_name a})"

def test_bytes1 := UInt16.to_bytes 4444

def empty_nats: List Nat:= []

def test_bytes := ["hellö", "world","shrt", "longer text"].to_bytes

def test_bytes2:= empty_nats.to_bytes

abbrev Address := Socket.SockAddr4

instance: ToString Address where
  toString x := s!"{x.addr}@{x.port}"

def Socket.send_val2 (sock: Socket) (msg: μ): IO Unit := do
  let payload := Serialize.to_bytes msg
  if payload.size >= UInt32.size then
    panic! s!"cannot send payloads with more than UInt32 bytes size"
  let size_info := payload.size.toUInt32.to_bytes
  let packet := size_info ++ payload
  let sz ← sock.send packet

  if cfg.print_net_bytes then
    IO.println s!"send bytes {packet}"
  assert! sz == packet.size.toUSize

def Socket.SockAddr4.connect_to (addr: Address): IO Socket := do
  let sock ← Socket.mk .inet .stream
  repeat
    try
      sock.connect addr
      break
    catch _ =>
      IO.sleep send_timeout_duration
  return sock

def Socket.SockAddr4.listen_on (addr: Address): IO Socket := do
  let sock ← Socket.mk .inet .stream
  sock.bind addr
  sock.listen 1
  let (client, _sa) ← sock.accept
  return client


def Socket.recv_val (sock: Socket) (max: USize := 4096) [Serialize t]: IO t := do
  let recv ← sock.recv max
  IO.println s!"recv bytes: {recv}"
  if recv.size == 0 then throw (IO.Error.otherError 2 "received msg with 0 bytes")


  let msg := Serialize.from_bytes recv
  match msg with
  | .ok val =>
    return val
  | .error e => throw (IO.Error.userError e)

def Socket.recv_val2 (sock: Socket) [Serialize t]: IO t := do
  let size_info_opt := UInt32.from_bytes (<- sock.recv 4)
  match size_info_opt with
  | .ok size_info =>
    let payload <- sock.recv (USize.ofNat size_info.toNat)
    if payload.size != size_info.toNat then throw (IO.Error.otherError 2 s!"payload size [{size_info}] does not match up with received [{payload.size}]")
    let msg := Serialize.from_bytes payload
    match msg with
    | .ok val => return val
    | .error e => throw (IO.Error.userError e)
  | .error e => throw (IO.Error.userError e)



def IO.getLine: IO String := do
  let stdin <- IO.getStdin
  return (<-stdin.getLine).dropRight 1

def IO.getBool: IO Bool := do
  let str <- IO.getLine
  return str == "y"

def IO.getNat: IO Nat := do
  let str <- IO.getLine
  return str.toNat!

def List.seperate (l: List a) (n: Nat):  (List a × List a) :=
 let l1 := l.drop n
 let l2 := (l.reverse.drop (l.length - n)).reverse
 (l2, l1)

def List.fromTo (l: List a) (i i': Nat) : List a :=
  let r := l.drop i
  let r :=  (r.reverse.drop (r.length - i')).reverse
  r


-- returns a List where the first n elements are removed from a list and appended to the end
-- examples [1,2,3].shuffle 1 => [2,3,1]
-- examples [1,2,3].shuffle 2 => [3,1,2]

def List.shuffle (l: List a) (n: Nat := 1):  List a :=
  let pre := (l.reverse.drop (l.length - n)).reverse
  l.drop n ++ pre

#eval [1,2,3,4,5,6].shuffle 2


def IO.clearTerminal: IO Unit :=
  IO.println (repeat_string "\n" 40)

def longest_string: List String -> Nat
| [] => 0
| a::as => max a.length (longest_string as)


-- returns shortend version of reprString after the dot
def reprName' (v:α) [ToString α]: String :=
  let rs := toString v
  (rs.dropWhile (fun x => x != '.')).drop 1

-- reprName and padding every string to the maximum length string length
def reprName (v:α) [ToString α] [FinEnum α]: String :=
  let rn := reprName' v
  let longest := longest_string ((FinEnum.toList α).map (fun x => reprName' x))
  let padded := rn ++ (repeat_string " " (longest - rn.length))
  padded



-- def FinEnum.ofString! (s:String) [FinEnum α][ToString α] [Inhabited α]:  α :=
--   let opt := FinEnum.ofString? s
--   match opt with
--   | some v => v
--   | none => Inhabited.default



def List.even_chunks(ls: List α) (n:Nat): {l: List (List α) // l.length = n} :=

  let res := Fin.list n
  let chunk_size := ls.length / n
  let chunks := res.map (fun x =>
    let rest := ls.length % n

    let chunk_start := (x * chunk_size) + (min rest x)

    let chunk_size :=
      if x < rest then
        chunk_size + 1
      else
        chunk_size
    ls.fromTo chunk_start chunk_size
  )
  have q: res.length = n := by exact Fin.length_list n

  ⟨chunks, by sorry⟩


  #eval [1,23,4,5,6,7,34].toChunks 4


instance [Repr t]: ToString t where
  toString := reprStr
