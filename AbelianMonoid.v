Require Import Arith.

(** Example using subclasses from web discussion.  Start with a Semigroup
and buid up an Abelian Monoid.  This is currently not used in the specs,
but serves as a pretty good example of defining typeclasses and instantiating
the result. *)

(** A semigroup is a set ([A]) with an associative operator ([op]) *)

Class Semigroup {A : Type} (op : A -> A -> A) : Type := {
  op_associative : forall x y z : A, op x (op y z) = op (op x y) z
}.

(** A monoid is a semigroup with left and right identity values *)
Class Monoid `(M : Semigroup) (id : A) : Type := {
  id_ident_left  : forall x : A, op id x = x;
  id_ident_right : forall x : A, op x id = x
}.

(** An abelian monoid is a monoid whose operator is commutative *)
Class AbelianMonoid `(M : Monoid) : Type := {
  op_commutative : forall x y : A, op x y = op y x
}.

(** Let's explore multiplication as a semigroup, monoid and abelian monoid.
  First, we'll show that multiplication is a semigroup by creating an instance
  of [Semigroup] named [MultAsSemigroup]. *)

Instance MultAsSemigroup : (Semigroup mult) := {
}.
Proof.
  intros. apply mult_assoc.
Defined.

Instance MultAsMoioid2 : (Monoid (Semigroup mult) 1) := {
}.

Instance MultAsMonoid : (Monoid MultAsSemigroup 1) := {
}.
Proof.
  intros. apply mult_1_l.
  intros. apply mult_1_r.
Defined.

Instance MultAsAbelianMonoid : (AbelianMonoid MultAsMonoid) :=
{
}.
Proof.
  intros. apply mult_comm.
Defined.

Quit.