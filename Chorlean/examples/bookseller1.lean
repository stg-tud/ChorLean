import Chorlean.Choreo
import Chorlean.Effects
import Mathlib.Tactic.DeriveFintype

open Effect

inductive Location
| buyer | seller | friend
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location


inductive BuyerEff: Type -> Type
| get_budget: BuyerEff Nat
| get_title: BuyerEff String
| print2: String -> BuyerEff Unit

open BuyerEff

instance: Signature BuyerEff where
  interpretation
  | .get_budget => do
    IO.println "enter your budget"
    return (←IO.getLine).toNat!
  | .get_title => do
    IO.println "enter your title"
    return (←IO.getLine)
  | .print2 s => do
    IO.print s



inductive SellerEff: Type -> Type
| lookup_price: String -> SellerEff Nat
| deliveryDate:  SellerEff String
open SellerEff

open Effect.Log


instance: Signature SellerEff where
  interpretation
  | .lookup_price title => do
    IO.println "looked up title"
    return  (if (title) == "Faust" then 100 else 200)
  | .deliveryDate => do
    IO.println "enter the delivery date:"
    return (←IO.getLine)


instance: Role where
  δ := Location
  sig
  | buyer =>  BuyerEff ⨳ Log
  | seller =>  SellerEff ⨳ Log
  | friend =>   Log
  executable x := match x with
    | buyer =>   inferInstance
    | seller =>  inferInstance
    | friend =>  inferInstance
  adj
  | friend, buyer, _ => false
  | _, _, _ => true

variable [Endpoint]
variable [MonadLiftT NetEff IO]

--set_option trace.Meta.synthInstance true

def budget := 20

def books: Choreo all c String:= do
  have: MonadLift BuyerEff (BuyerEff ⨳ Log) := inferInstance
  have: MonadLift Log (BuyerEff ⨳ Log) := inferInstance
  have: MonadLift SellerEff (SellerEff ⨳ Log) := inferInstance
  have: MonadLift Log (SellerEff ⨳ Log) := inferInstance

  -- let data:  ({l // all l} -> (List Nat)) @ (· = buyer) := Located.wrap (fun x => match x.val with
  --   | buyer  => [1,2,3]
  --   | seller => [4,5,6]
  --   | friend =>[7,8]
  -- )

  -- let dist_data <- scatter buyer data

  -- let collected <- gather friend dist_data

  -- par (
  --   dbg_trace s!"my data: {Unfacet.get dist_data}"
  --   return ()
  -- )

  -- locally friend ( fun {cen} =>
  --   let x := collected cen

  --   dbg_trace s!"buyer  data: {x ⟨buyer, by trivial⟩}"
  --   dbg_trace s!"seller data: {x ⟨seller, by trivial⟩}"
  --   dbg_trace s!"friend data: {x ⟨friend, by trivial⟩}"
  --   return ()
  -- )

  let data:  (List Nat) @ (· = buyer) := Located.wrap [1,2,3,4,5,6,7]

  let dist_data <- scatterList buyer data

  let collected <- gather friend dist_data

  par (
    dbg_trace s!"my data: {dist_data.lookInto ep'}"
    return ()
  )

  locally friend ( fun {cen} =>
    let x := collected cen

    dbg_trace s!"buyer  data: {x ⟨buyer, by decide⟩}"
    --dbg_trace s!"seller data: {x }"
    --dbg_trace s!"friend data: {x }"
    return ()
  )

  return "hello"
  -- let temp <- par (do
  --   let name := reprName (Unfacet.get (Endpoint.endpoint (δ:=Location)))
  --   --have lifter: MonadLift Log (Free (LocSig.sig ep))  := inferInstance
  --   --let x <- lifter.monadLift (Log.info s!"hello from {name}")
  --   return 2
  -- )


  -- let title <- locally_bcast buyer (
  --   BuyerEff.get_title
  -- )

  -- let price:Nat <- locally_bcast seller (do
  --   return if title' == "Faust" then 100 else 200
  -- )

  -- let local_decision: Bool <- locally_bcast buyer ( do
  --   return budget >= price
  -- )

  -- if local_decision then
  --   let date ← locally_bcast seller SellerEff.deliveryDate
  --   return date
  -- else
  --   return "never"






  -- if d then
  --   let date ← deliveryDate § seller ~> @buyer
  --   par (
  --     IO.print s!"final date: {date}"
  --   )
  -- else

  --   (warning s!"the customer declined the purchase") § seller ~> @@ []

  --   (error s!"price of {price} exceeding your budget of {budget}!") § buyer ~> @@ []
  --   return ()

  -- let sending:= enclave (c:=by simp) (p:= all) (p':= @@ [buyer, friend]) (fun {cen} => do
  --     let comp: ChoreoSig (p:= @@ [buyer, friend]) cen (Faceted String):= ChoreoSig.Par (
  --       do
  --       IO.println "enter your title"
  --       return (←IO.getLine)
  --     ) (δ:=Location)
  --     let comp_res <- comp
  --     let comp_res' := comp_res.lookInto buyer
  --     let bcast :=
  --       ChoreoSig.Broadcast (p:= @@ [buyer, friend]) (gv:=comp_res') ( adj := by exact rfl)
  --     let bcast_res <- bcast
  --     return bcast_res
  --   )
  -- let sending_res <- sending

  -- let print2: ChoreoSig (p:=fun _ => true) rfl (Faceted Unit)  := ChoreoSig.Par (
  --   do
  --   IO.println s!"buyer title was: {(tt)} {sending_res}"
  -- ) (δ:=Location)
  -- print2




variable (p q : Prop)

instance: ChorMain where
  main _ := do
    let res <- books
    return Faceted.of 0


 def main := CHOR_ENTRYPOINT
