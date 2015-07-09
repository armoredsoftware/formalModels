Require Export StateMonad.
Require Export FunctionalExtensionality.

Definition C := Type.
Definition ID := Type.

(**
- [send] - Send a message of type [A] to [ID] over channel [C] and result in a [State] to be evaluated locally.
- [receive] - Receive a message of type [A] from [ID] on channel [C] and result in a [State] to be evaluated locally.
- [vtpm] - Communicate with the vTPM with result [A] and [State] for evaluation
locally
- [ifM] - Evaluate [Prop] locally and return the appropriate next state.  Note
this is an if statement, not an if expression.
- [mapM] - _Definition is pending_
- [foldM] - _Definition is pending_
- [bundle] - _Definition is pending_
*)

Class ProtocolMonad {S A:Type} `(StateMonad) : Type :=
{
  send : C -> ID -> A -> (State S A)
  ; receive : C -> ID -> A -> (State S A)
  ; vtpm : A -> (State S A)                              
  ; ifM : bool -> (State S A) -> (State S A) -> (State S A)
  ; mapM : (State S A)
  ; foldM : (State S A)
  ; bundle : A -> (State S A)
}.

(** Make the [ProtocolMonad] an instance of [StateMonad] by giving values
  to [put] and [get] and proving the state monad laws. This instance is
  paramaterized over [S], [A] and [a], thus it can be used when creating
  an instance of [ProtocolMonad]. *)

Instance ProtocolMonadAsState (S A:Type) (a:A) :
  StateMonad S A a StateAsMonad :=
{
  put := (fun (s:S) => (fun (_:S) => (a,s)))
  ; get := (fun (s:S) => (s,s))
}.
Proof.
  intros. simpl. extensionality x. reflexivity.
  intros. simpl. extensionality x. reflexivity.
  intros. simpl. extensionality x. reflexivity.
  intros. simpl. extensionality x. reflexivity.
Defined.

(** Create an instnce of [ProtocolModad] using [nat] for the type of both [S]
  and [A] and using [0] as the defuault result. This should be doable for
  any types, not just [nat]. Right now there are no protocol monad laws, thus
  one need only specify values for the elements of [ProtocolMonad] that
  that define the specific instance. *)

Instance ProtocolMonadInstance :
  ProtocolMonad (ProtocolMonadAsState nat nat 0) :=
{
  send := (fun (_:C) => (fun (_:ID) => (fun (a:nat) => (fun (s:nat) => (a,s)))))
  ; receive := (fun (_:C) => (fun (_:ID) => (fun (a:nat) => (fun (s:nat) => (a,s)))))
  ; ifM := (fun (p:bool) => (fun (t:(State nat nat)) => (fun (f:(State nat nat)) => if p then t else f)))
  ; mapM := (fun (s:nat) => (0,s))
  ; foldM := (fun (s:nat) => (0,s))
  ; vtpm := (fun (a:nat) => (fun (s:nat) => (a,s)))
  ; bundle := (fun (a:nat) => (fun (s:nat) => (a,s)))
}.