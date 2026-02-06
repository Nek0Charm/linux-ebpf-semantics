From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.

Section Nondeterminism.

(* Type parameter *) (*
Hypothesis Aeq_dec : forall {A : Set} (x y:A), {x = y} + {x <> y}. *)

(* The nondeterminism monad: *)
Polymorphic Inductive t (A : Set) : Type :=
  | ND : list A -> t A.

Arguments ND {A} _.

(* val mzero: forall 'a. t 'a *)
Definition mzero {A : Set} : t A :=
  ND [].

(* val return: forall 'a. 'a -> t 'a *)
Definition return_ {A : Set} (a : A) : t A :=
  ND [a].

(* val pick: forall 'a. string -> list 'a -> t 'a *)
Definition pick {A : Set} (msg : string) (l : list A) : t A :=
  ND l.

(* val forget: forall 'a. t 'a -> list 'a *)
Definition forget {A : Set} (m : t A) : list A :=
  match m with
  | ND l => l
  end.

Inductive kill_reason : Type :=
  | Error : string -> kill_reason
  | Other : string -> kill_reason.

(* val kill: forall 'a. kill_reason -> t 'a *)
Definition kill {A : Set} (reason : kill_reason) : t A :=
  mzero.

(* val guard: bool -> kill_reason -> t unit *)
Definition guard (b : bool) (reason : kill_reason) : t unit :=
  if b then return_ tt else kill reason.

(* val mplus: forall 'a. t 'a -> t 'a -> t 'a *)
Definition mplus {A : Set} (m1 m2 : t A) : t A :=
  match m1, m2 with
  | ND l1, ND l2 => ND (l1 ++ l2)
  end.

(* val msum: forall 'a. list (t 'a) -> t 'a *)
Fixpoint msum {A : Set} (l : list (t A)) : t A :=
  match l with
  | [] => mzero
  | h :: t => mplus h (msum t)
  end.

(* val bindExhaustive: forall 'a 'b. t 'a -> ('a -> t 'b) -> t 'b *)
Definition bindExhaustive {A B} (m : t A) (f : A -> t B) : t B :=
  msum (map f (forget m)).

(* val bind: forall 'a 'b. t 'a -> ('a -> t 'b) -> t 'b *)
Definition bind {A B : Set} := @bindExhaustive A B.

(* val mem : forall 'a. Eq 'a => 'a -> t 'a -> bool *)
Definition mem {A : Set} (Aeq_b: A -> A -> bool) (x : A) (m : t A) : bool :=
  existsb (fun y => if Aeq_b x y then true else false) (forget m).

End Nondeterminism.