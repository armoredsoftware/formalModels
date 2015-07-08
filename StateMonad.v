(**
 [StateMonad] type class definition

 Provides a simple type class for defining structures to be of the form
 of a state monad.

 TODO:
 + add state monad laws for put and get
 + prove state monad laws for get
 + rework get to use the standard form by adding a unit operator for the
   [A] type.  Should be easy to do with typeclass parameters.
*)

Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Monad.

(** Extend the [Monad] typeclass to implement a [StateMonad] typeclass.  Note
  that [StateMonad S] is the monad, not just [StateMonad].  This will be
  important when we instantiate the [Monad] typeclass.  *)

(** [State] is the classic definition of the state monad type.  Note that
  although its name is [State] its really a next state function.  Keeping
  the tradition name here. *)
Definition State (S A:Type) := S -> A * S.

(** Extend the [Monad] class with [put] and [get].  Still need to add the
  state monad laws for [get]:

<<
  put s >> put s'            = put s'
  put s >> get               = put s >> return s
  get  >>= put               = return ()
  get  >>= λs → get >>= k s = get >>= λs → k s s
>>

All the laws are now proved for the StateMonadEx2 version that is explicitly
parameterized over the arbitrary output [a:A] for the definition of [get].
This corresponds with the [()] value above that is explicit and must be of
the type of [A].

*)

Class StateMonad (S A:Type) (a:A) `(Monad (State S)) :Type :=
{
  get: State S S
  ; put: S -> (State S A)
  ; put1: forall (s s':S), put s >> put s' = put s'
  ; put2: forall (s:S), put s >> get = put s >> unit s
  ; get1: forall (s:S), get >>= put = unit a
  ; get2: forall (s:S) (k:S->S->State S A),
            get >>= (fun s => get >>= k s) = get >>= (fun s => (k s) s)
}.

(** Create an instance of [Monad] from [(State S)] and prove the monad laws.
  [StateMonadI] is of type [Monad (State S)] and can now be used to
  instantiate the third parameter if [StateMonad] that requires [(State S)]
  to be an instance of [Monad] *)
Instance StateMonadI (S:Type) : Monad (State S) :=
{
  unit A x := (fun s => (x,s))
  ; bind A B m f := (fun s0 =>
                       match (m s0) with
                         | (a,s1) => (f a) s1
                       end)
  ; sequence A B m1 m2 := (fun s0 =>
                             match (m1 s0) with
                               | (a,s1) => m2 s1
                             end)
}.
Proof.
  intros. extensionality x. reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
  intros. extensionality x. reflexivity.  
Defined.

(** Create an instance of [StateMonad] using [State] as the type constructor
  and [StateMonadI] as a witness to something being of type [(Monad (State S))]   called [StateMonadX].  Note that PVS would have done some of the type-foo
  automatically.
Instance StateMonadEx {S A:Type} {a:A} : StateMonad S A a (StateMonadI S) :=
{
  put := (fun (s:S) => (fun (_:S) => (a,s)))
  ; get := (fun (s:S) => (s,s))
}.
Proof.
  intros. unfold sequence. simpl. extensionality x. reflexivity.
  intros. unfold sequence. simpl. extensionality x. reflexivity.
  intros. unfold bind. simpl. extensionality x. reflexivity.
  intros. unfold bind. simpl. extensionality x. reflexivity.
Defined.
*)

Instance StateMonadEx2 : StateMonad nat nat 0 (StateMonadI nat) :=
{
  put := (fun (s:nat) => (fun (_:nat) => (0,s)))
  ; get := (fun (s:nat) => (s,s))
}.
Proof.
  intros. unfold sequence. simpl. extensionality x. reflexivity.
  intros. unfold sequence. simpl. extensionality x. reflexivity.
  intros. unfold bind. simpl. extensionality x. reflexivity.
  intros. unfold bind. simpl. extensionality x. reflexivity.
Defined.

Example unit_ex1 : ((unit 0) 1) = (0,1).
Proof.
  unfold unit.
  simpl.
  reflexivity.
Qed.

(** Examples and proofs *)

(** [incState] is a simple [f] that increments a state value consisting of 
  a natural numnber. *)

Definition incState:nat->(State nat nat) := (fun _ => (fun s => (0, (s+1)))).

(** [incStateCurry] is a [State] resuting from currying [f]. *)

Definition incStateCurry:(State nat nat) := (incState 0).

Example bind_ex1: ((unit 0) >>= incState) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex1: ((unit 0) >> incStateCurry) 0 = (0,1).
Proof.
  unfold sequence. reflexivity.
Qed.

Example bind_ex2 :
  ((unit 0) >>= incState >>= incState) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex2 : ((unit 0) >> incStateCurry >> incStateCurry) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

(** [addInput] is a simple [f] that adds the result of a previous execution
  to the current state.  Note this function cannot use [sequence] and must
  use [bind] due to the dependence on a previous result *)

Definition addInput:(nat -> (State nat nat)) :=
  (fun a => (fun s => (a,(a+s)))).

Example bind_ex3 :
  ((unit 1) >>= addInput >>= addInput) 0 = (1,2).
Proof.
  unfold bind. reflexivity.
Qed.

Example put_ex1 : (((unit 1) >> (put 10) >> get) 8) = (10,10).
Proof.
  unfold sequence, put. simpl.
  reflexivity.
Qed.

Example get_ex1 : ((unit 0) >> get) 10 = (10,10).
Proof.
  unfold sequence. simpl. unfold get. reflexivity.
Qed.
