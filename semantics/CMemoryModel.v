From Coq Require Import List String ListSet.
Import ListNotations.
Open Scope string_scope.

Inductive memory_order : Type :=
  | NA
  | Seq_cst
  | Relaxed
  | Release
  | Acquire
  | Consume
  | Acq_rel.

Definition aid := string.
Definition program := nat.
Definition tid := nat.
Definition location := nat.
Definition cvalue := nat.

Inductive lock_outcome : Type := Locked | Blocked.

Inductive action : Type :=
  | Lock (a : aid) (t : tid) (l : location) (o : lock_outcome)
  | Unlock (a : aid) (t : tid) (l : location)
  | Load (a : aid) (t : tid) (mo : memory_order) (l : location) (v : cvalue)
  | Store (a : aid) (t : tid) (mo : memory_order) (l : location) (v : cvalue)
  | RMW (a : aid) (t : tid) (mo : memory_order) (l : location) (v1 v2 : cvalue)
  | Fence (a : aid) (t : tid) (mo : memory_order)
  | Blocked_rmw (a : aid) (t : tid) (l : location)
  | Alloc (a : aid) (t : tid) (l : location)
  | Dealloc (a : aid) (t : tid) (l : location).

Inductive location_kind : Type := Mutex | Non_Atomic | Atomic.

