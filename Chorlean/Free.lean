-- class EffectHandler (eff: Type u → Type v) (m: Type u → Type v) [Monad m] where
--   run: eff α → m α

inductive Free (Eff:Type u → Type v) (α:Type) where
| Do: Eff β → (β → Free Eff α) → Free Eff α
| Return: α → Free Eff α

def Free.lift  {m: Type → Type} [Monad m] [MonadLift eff m]: Free eff α → m α
| .Return v => return v
| .Do e cont => do
  let res <- MonadLift.monadLift e
  Free.lift (cont res)

@[reducible] def Free.toFree {α: Type} {Eff: Type → Type v} (e: Eff α): Free Eff α :=
  .Do e (fun x =>  .Return x)

-- Lift instance that lifts an Effect into Free tha only does this single effect
instance: MonadLift (Eff) (Free Eff) where
  monadLift e := Free.Do e (fun x =>  .Return x)


def Free.bind {α β : Type} : Free Eff α → (α → Free Eff β) → Free Eff β
| Return v, next => next v
| Do eff cont, next =>
  Free.Do eff (fun  x => bind (cont x) next)

instance: Monad (Free Eff) where
  pure x := .Return x
  bind := Free.bind

def Free.monadLift {α : Type}  [Monad m] [MonadLiftT eff m]:  Free eff α → m α
| .Do e cont => do
  let res <- MonadLiftT.monadLift e
  Free.monadLift (cont res)
| .Return v => do return v

variable (p q : Prop)

-- the Free eff Lift instance for a Effect eff with existing Lifting instance (transitive)
instance [MonadLiftT eff m] [Monad m]: MonadLiftT (Free eff) m where
  monadLift := Free.monadLift

-- Coproduct
inductive CoProd
  (inl: Type u → Type v1) (inr: Type u → Type v2) (α:Type u) where
| l: inl α → CoProd inl inr α
| r: inr α → CoProd inl inr α

-- Coproduct
structure CoSum
  (inl: Type u → Type v1) (inr: Type u → Type v2) (α:Type u) where
  l: inl α
  r: inr α




instance [m1: MonadLiftT eff eff1] [m2: MonadLiftT eff eff2]: MonadLiftT eff (CoSum eff1 eff2) where
  monadLift x := {l := m1.monadLift x, r := m2.monadLift x}



instance: MonadLiftT (CoSum eff1 eff2) eff1 where
  monadLift x := x.l
instance: MonadLiftT (CoSum eff1 eff2) eff2 where
  monadLift x := x.r

-- Lifts the first Effect alternative into an CoProd
instance: MonadLift eff1 (CoProd eff1 eff2) where
  monadLift x := CoProd.l x

-- Lifts the second Effect alternative into an CoProd
instance: MonadLift eff2 (CoProd eff1 eff2) where
  monadLift x := CoProd.r x

-- transitively lifts an coproduct Effect into a Monad (or Effect) m if both Effect Signatures can be lifted into m
instance [MonadLiftT eff1 m] [MonadLiftT eff2 m]: MonadLiftT (CoProd eff1 eff2) m where
  monadLift x := match x with
    | .l e1 => MonadLiftT.monadLift e1
    | .r e2 => MonadLiftT.monadLift e2

-- short notation for CoProds
infixl:65 "⨳" => CoProd
infixl:65 "⇹" => CoSum

--- Examples

inductive PrintEff: Type → Type
| Print1: String → PrintEff Unit


abbrev memPrinter := Free (CoProd PrintEff (StateM String))


inductive LogEff1: Type → Type
| Print2: Nat → LogEff1 Unit

inductive LogEff2: Type → Type
| Print3: Nat → LogEff2 Unit

@[reducible] def LogPrintEff := Free (CoProd PrintEff LogEff1)
@[reducible] def LogPrintEff2 := Free (CoProd LogPrintEff LogEff2)


@[reducible] def LogPrintEff3 := Free (CoSum PrintEff LogEff1)

open PrintEff
open LogEff1

instance seee {s:Type} (v: s): MonadLiftT (StateM s) IO where
  monadLift x :=do
    return x.run' v

instance: MonadLift PrintEff IO where
  monadLift x := match x with
    | .Print1 s => IO.println s

instance: MonadLift LogEff1 IO where
  monadLift x := match x with
    | .Print2 s => IO.println ("n: " ++ toString s)

instance: MonadLift LogEff2 IO where
  monadLift x := match x with
    | .Print3 s => IO.println ("n: " ++ toString s)


def memprog: memPrinter Nat :=do
  let temp <- get
  set "XXX"
  Print1 temp
  Print1 "a"
  return 3

def memprog2: memPrinter Nat :=do
  set "YYYY"
  let temp <- get
  Print1 temp
  Print1 "a"
  return 3


def prog: Free PrintEff Unit :=do
  Print1 "Hello"
  Print1 "a"
  return ()

def prog1: Free LogPrintEff Unit :=do
  Print1 "Hello"
  Print2 23
  return ()

def prog2: Free LogPrintEff2 Unit :=do
  Print1 "Hello"
  (LogEff1.Print2 23)
  LogEff2.Print3 23
  return ()

@[reducible]
def coSumAll: (List (Type -> Type)) -> Type -> Type
| [] => IO
| a::as => CoSum a (coSumAll as)

@[reducible]
def bla := IO

def prog3: Free (coSumAll [PrintEff, IO, bla, IO]) Unit :=do
  Print1 "Hello"
  return ()


def Main: IO Unit := do
  MonadLiftT.monadLift prog1
  prog1
  prog2
  let _temp <- (Print1 "e e vvvve e")
  have := seee "hello instanceee"
  let _temp <- memprog
  let _temp <- memprog2
  return ()
