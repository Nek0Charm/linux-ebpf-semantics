From Coq Require Import List String ListSet.

From bpf.ebpf Require Import Nondeterminism.
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

Record pre_execution : Type :=
  Build_pre_execution {
    actions0 : list action;
    threads : list tid;
    lk : location -> location_kind;
    sb : list (action * action);
    asw : list (action * action);
    dd : list (action * action)
  }.

Record execution_witness : Type :=
  Build_execution_witness {
    rf : list (action * action);
    mo : list (action * action);
    sc : list (action * action);
    lo : list (action * action);
    tot : list (action * action)
  }.

Definition empty_witness : execution_witness :=
  Build_execution_witness [] [] [] [] [].

Record incState : Type :=
  Build_incState {
    incWit : execution_witness;
    incCommitted : list action
  }.

Definition is_seq_cst (act : action) : bool :=
  match act with
  | Load _ _ Seq_cst _ _ => true
  | Store _ _ Seq_cst _ _ => true
  | RMW _ _ Seq_cst _ _ _ => true
  | Fence _ _ Seq_cst => true
  | _ => false
  end.

Definition loc_of (a : action) : option location :=
  match a with
  | Lock _ _ l _ => Some l
  | Unlock _ _ l => Some l
  | Load _ _ _ l _ => Some l
  | Store _ _ _ l _ => Some l
  | RMW _ _ _ l _ _ => Some l
  | Fence _ _ _ => None
  | Blocked_rmw _ _ l => Some l
  | Alloc _ _ l => Some l
  | Dealloc _ _ l => Some l
  end.

Definition is_at_atomic_location (lk1 : location -> location_kind) (a : action) : bool :=
  match loc_of a with
  | Some l => 
      match lk1 l with
      | Atomic => true
      | _ => false
      end
  | None => false
  end.

Definition string_eqb (x y : string) : bool :=
  if string_dec x y then true else false.

Definition memory_order_eqb (x y : memory_order) : bool :=
  match x, y with
  | NA, NA => true
  | Seq_cst, Seq_cst => true
  | Relaxed, Relaxed => true
  | Release, Release => true
  | Acquire, Acquire => true
  | Consume, Consume => true
  | Acq_rel, Acq_rel => true
  | _, _ => false
  end.

Definition lock_outcome_eqb (x y : lock_outcome) : bool :=
  match x, y with
  | Locked, Locked => true
  | Blocked, Blocked => true
  | _, _ => false
  end.

Definition action_eqb (x y : action) : bool :=
  match x, y with
  (* Lock *)
  | Lock a1 t1 l1 o1, Lock a2 t2 l2 o2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && Nat.eqb l1 l2 && lock_outcome_eqb o1 o2
  
  (* Unlock *)
  | Unlock a1 t1 l1, Unlock a2 t2 l2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && Nat.eqb l1 l2
  
  (* Load *)
  | Load a1 t1 mo1 l1 v1, Load a2 t2 mo2 l2 v2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && memory_order_eqb mo1 mo2 
      && Nat.eqb l1 l2 && Nat.eqb v1 v2
  
  (* Store *)
  | Store a1 t1 mo1 l1 v1, Store a2 t2 mo2 l2 v2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && memory_order_eqb mo1 mo2 
      && Nat.eqb l1 l2 && Nat.eqb v1 v2
  
  (* RMW *)
  | RMW a1 t1 mo1 l1 v11 v12, RMW a2 t2 mo2 l2 v21 v22 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && memory_order_eqb mo1 mo2 
      && Nat.eqb l1 l2 && Nat.eqb v11 v21 && Nat.eqb v12 v22
  
  (* Fence *)
  | Fence a1 t1 mo1, Fence a2 t2 mo2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && memory_order_eqb mo1 mo2
  
  (* Blocked_rmw *)
  | Blocked_rmw a1 t1 l1, Blocked_rmw a2 t2 l2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && Nat.eqb l1 l2
  
  | Alloc a1 t1 l1, Alloc a2 t2 l2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && Nat.eqb l1 l2
  
  | Dealloc a1 t1 l1, Dealloc a2 t2 l2 =>
      string_eqb a1 a2 && Nat.eqb t1 t2 && Nat.eqb l1 l2
  
  | _, _ => false
  end.

Section CMM.

Variable exeAddToLo : pre_execution -> action -> incState -> 
                     Nondeterminism.t (list (action * action)).

Variable exeAddToSc : pre_execution -> action -> incState -> 
                     Nondeterminism.t (list (action * action)).

Variable exeAddToRfLoad : pre_execution -> action -> incState -> 
                         Nondeterminism.t (list (action * action)).
Variable exeAddToMo : pre_execution -> action -> incState -> 
                     Nondeterminism.t (list (action * action)).

Variable exeAddToRfRmw : pre_execution -> action -> incState -> 
                        Nondeterminism.t (list (action * action)).

Variable preRestrict : pre_execution -> list action -> pre_execution.

Variable standard_relations : pre_execution -> execution_witness -> 
                            (pre_execution * execution_witness).

Variable exeCheckConsistency : pre_execution * execution_witness * 
                              (pre_execution * execution_witness) -> 
                              Nondeterminism.t unit.
Variable exeCheckWitRestrict : execution_witness -> list action -> 
                              execution_witness -> Nondeterminism.t unit.
Variable exeCheckCommitmentOrder : pre_execution -> execution_witness -> 
                                  list action -> action -> Nondeterminism.t unit.

Variable well_formed_threads_opsem : pre_execution * execution_witness * 
                                     list (action * incState) -> Prop.

Variable incState_eqb: incState -> incState -> bool.

Definition action_inc_eq (p1 p2 : action * incState) : bool :=
  let (a1, s1) := p1 in
  let (a2, s2) := p2 in
  action_eqb a1 a2 && incState_eqb s1 s2.

Definition exePerformLock (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  Nondeterminism.bindExhaustive 
    (exeAddToLo pre1 a s) 
    (fun (new_lo : list (action * action)) =>
      Nondeterminism.return_ 
        (Build_execution_witness
          (rf (incWit s))
          (mo (incWit s))
          (sc (incWit s))
          new_lo
          (tot (incWit s)))).

Definition exePerformUnlock (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  Nondeterminism.bindExhaustive 
    (exeAddToLo pre1 a s) (fun (new_lo : list (action * action)) =>
      Nondeterminism.return_ 
        (Build_execution_witness
          (rf (incWit s))
          (mo (incWit s))
          (sc (incWit s))
          new_lo
          (tot (incWit s)))).

Definition exePerformLoad (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  Nondeterminism.bindExhaustive
    (if is_seq_cst a then
       exeAddToSc pre1 a s
     else
       Nondeterminism.return_ (sc (incWit s))) 
    (fun (new_sc : list (action * action)) =>
      Nondeterminism.bindExhaustive  
        (exeAddToRfLoad pre1 a s) 
        (fun (new_rf : list (action * action)) =>
          Nondeterminism.return_ 
            (Build_execution_witness
              new_rf
              (mo (incWit s))
              new_sc
              (lo (incWit s))
              (tot (incWit s))))).

Definition exePerformStore (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  Nondeterminism.bindExhaustive
    (if is_seq_cst a then
       exeAddToSc pre1 a s
     else
       Nondeterminism.return_ (sc (incWit s))) 
    (fun (new_sc : list (action * action)) =>
      Nondeterminism.bindExhaustive
        (if is_at_atomic_location (lk pre1) a then
           exeAddToMo pre1 a s
         else
           Nondeterminism.return_ (mo (incWit s))) 
        (fun (new_mo : list (action * action)) =>
          Nondeterminism.return_ 
            (Build_execution_witness
              (rf (incWit s))
              new_mo
              new_sc
              (lo (incWit s))
              (tot (incWit s))))).

Definition exePerformRmw (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  Nondeterminism.bindExhaustive
    (if is_seq_cst a then
       exeAddToSc pre1 a s
     else
       Nondeterminism.return_ (sc (incWit s))) 
    (fun (new_sc : list (action * action)) =>
      Nondeterminism.bindExhaustive  
        (exeAddToRfRmw pre1 a s) 
        (fun (new_rf : list (action * action)) =>
          Nondeterminism.bindExhaustive  
            (exeAddToMo pre1 a s) 
            (fun (new_mo : list (action * action)) =>
              Nondeterminism.return_ 
                (Build_execution_witness
                  new_rf
                  new_mo
                  new_sc
                  (lo (incWit s))
                  (tot (incWit s)))))).

Definition exePerformFence (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  Nondeterminism.bindExhaustive
    (if is_seq_cst a then
       exeAddToSc pre1 a s
     else
       Nondeterminism.return_ (sc (incWit s))) 
    (fun (new_sc : list (action * action)) =>
      Nondeterminism.return_ 
        (Build_execution_witness
          (rf (incWit s))
          (mo (incWit s))
          new_sc
          (lo (incWit s))
          (tot (incWit s)))).

Definition exePerformAction (pre1 : pre_execution) (s : incState) (a : action) :
  Nondeterminism.t execution_witness :=
  match a with
  | Lock _ _ _ _      => exePerformLock pre1 s a
  | Unlock _ _ _      => exePerformUnlock pre1 s a
  | Load _ _ _ _ _    => exePerformLoad pre1 s a
  | Store _ _ _ _ _   => exePerformStore pre1 s a
  | RMW _ _ _ _ _ _   => exePerformRmw pre1 s a
  | Fence _ _ _       => exePerformFence pre1 s a
  | Blocked_rmw _ _ _ => Nondeterminism.return_ (incWit s)
  | Alloc _ _ _       => Nondeterminism.return_ (incWit s)
  | Dealloc _ _ _     => Nondeterminism.return_ (incWit s)
  end.

Definition exeStep (pre1 : pre_execution) (s : incState) :
  Nondeterminism.t (action * incState) :=
  let uncommitted_actions :=
    fold_right 
      (fun a acc => 
        if existsb (fun x => if action_eqb a x then true else false) (incCommitted s)
        then acc
        else a :: acc)
      []
      (actions0 pre1) in
  Nondeterminism.bindExhaustive  
    (Nondeterminism.pick "exeStep" uncommitted_actions)
    (fun a =>
      Nondeterminism.bindExhaustive
        (exePerformAction pre1 s a) 
        (fun new_wit =>
          let new_committed := a :: (incCommitted s) in
          let new_pre := preRestrict pre1 new_committed in
          let new_ex := (new_pre, new_wit, standard_relations new_pre new_wit) in
          Nondeterminism.bindExhaustive 
            (Nondeterminism.bindExhaustive
              (Nondeterminism.bindExhaustive 
                (exeCheckConsistency new_ex)
                (fun _ => exeCheckWitRestrict new_wit 
                           (incCommitted s) (incWit s)))
              (fun _ => exeCheckCommitmentOrder pre1 new_wit 
                         (incCommitted s) a))
            (fun _ => 
              let new_state := Build_incState new_wit new_committed in
              Nondeterminism.return_ (a, new_state)))).

Inductive exeTrace : pre_execution -> incState -> incState -> Prop :=
(* exeReflexiveTrace *)
| exeReflexiveTrace : forall (pre0 : pre_execution) (s : incState),
    well_formed_threads_opsem (pre0, empty_witness, []) ->
    exeTrace pre0 s s

(* exeStepTrace *)
| exeStepTrace : forall (pre0 : pre_execution) (x y z : incState) (a : action),
    exeTrace pre0 x y ->
    Nondeterminism.mem action_inc_eq (a, z) (exeStep pre0 y) = true ->
    exeTrace pre0 x z.

End CMM.