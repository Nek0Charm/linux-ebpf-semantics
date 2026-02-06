From Coq Require Import Bool.

Section GlobalSem.
Parameter state : Type. (* Global state of all threads *)
Parameter id    : Type. (* Thread id *)
Parameter trace : Type. (* Event trance *)
Parameter e0    : trace. (* Event trance *)
Parameter addr  : Type. (* Addresses *)
Parameter step : id -> state -> trace -> state -> Prop. (* Thread indexed transition relation *)

Parameter is_atomic    : id -> state -> bool.  (* Is the current instruction atomic *)
Parameter read_address : id -> state -> (addr -> Prop). (* Address that are about to be read by current instruction*)
Parameter write_address : id -> state -> (addr -> Prop). (* Address that are about to be written by current instruction *)

Definition has_race (s:state) (tid1:id) (tid2:id) :=
 (* (is_atomic tid1 s && is_atomic tid2 s = false) /\ (* not both are atomic *) *)
    (
      (exists a, write_address tid1 s a /\ write_address tid2 s a) (* concurrent write *)
      \/
        (exists a, write_address tid1 s a /\ read_address tid2 s a) (* concurrent read/write *)
      \/
        (exists a, read_address tid1 s a /\ write_address tid2 s a)) (* concurrent read/write *)
      .

Inductive State :=
| Normal (s:state)
| Stuck  (tid:id) (s:state) (* thread [tid] is racy for state [s] *).

Inductive estep : State -> trace -> State -> Prop :=
| Atomic_step : forall tid s e s',
    is_atomic tid s = true -> (* the thread performs an atomic access (if there is a race, the other thread will generate an error) *)
    step tid s e s' ->
    estep (Normal s) e (Normal s')
| NAtomic_step : forall tid s e s',
    is_atomic tid s = false -> (* the thread do NOT perform an atomic access *)
    (forall tid', tid <> tid' -> not (has_race s tid' tid)) -> (* but there is no race. *)
    step tid s e s' ->
      estep (Normal s) e (Normal s')
| Error_step : forall tid s,
    is_atomic tid s = false -> (* theres is a non-atomic racy access *)
    (exists tid', tid' <> tid /\ has_race s tid tid') ->
    estep (Normal s) e0 (Stuck tid s).

(* With this semantics, if we reach Error, we cannot prove anything about the program behaviour. *) 
End GlobalSem.