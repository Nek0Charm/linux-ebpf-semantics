From Coq Require Import Setoid List Lists.Streams.
From compcert Require Import Coqlib Errors Values AST Globalenvs.
(*
Require Import Footprint GMemory MemAux. *)


(** * Interaction Semantics *)

(** This file defines abstract module languages as interaction semantics. *)

(** An interaction semantics has these interfaces:
- [F], [V], [G]: 
types of function definition, variable information (e.g. Clight types), and global envirionment
- [comp_unit]: type of compilation unit
- [core]: type of internal "core" state
- [init_core]: initialize runtime core w.r.t. an entry and arguments, used on thread creation or external calls
- [halt]: core halts, a returning value is also required for supporting external calls
- [step]: internal steps of the core
- [at_external]: generates events (EntAtom/ExtAtom/Print or an external callwith arguments) and yield control
The EnvAtom/ExtAtom/Print events are encoded as special external functions with fixed function idents defined in GAST.v
- [after_external]: get back control, a returning value is required for supporting external calls
- [internal_fn]: generate a function table (for generaing function-module mapping), we need an interface for internal function list 
- [init_genv], [init_gmem]: Because we do not instantiate a concrete initial state or symbol binding, we give language extensional checkings for proper initial genv and memory
    
 *)

Record Language :=
  { 
    F: Type;
    V: Type;
    G: Type;
    comp_unit: Type;

    core: Type;

    gmem: Type;
    
    init_core: G -> ident -> list val -> option core;
    step: G -> (*freelist -> *) core -> gmem -> (*FP.t -> *) core -> gmem -> Prop;
    at_external: G -> core -> option (ident * signature * list val);
    after_external: core -> option val -> option core;
    halt: core -> option val;
    
    internal_fn: comp_unit -> list ident;
    init_genv: comp_unit -> Genv.t F V -> G -> Prop;
    init_gmem: Genv.t F V -> gmem -> Prop;
  }.

(*
Record CoreSemantics {G C M : Type} : Type :=
  { 
    initial_core : G -> val -> list val -> option C;
    at_external : C -> option (external_function * signature * list val);
    after_external : option val -> C -> option C;
    halted : C -> option val;
    corestep : G -> C -> M -> C -> M -> Prop;
    
    corestep_not_at_external: 
      forall ge m q m' q', corestep ge q m q' m' -> at_external q = None;
    corestep_not_halted: 
      forall ge m q m' q', corestep ge q m q' m' -> halted q = None;
    at_external_halted_excl: 
      forall q, at_external q = None \/ halted q = None
  }.*)