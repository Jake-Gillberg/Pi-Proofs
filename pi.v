(* Definition 1.1.1 *)
Require Import Coq.Strings.String.
(* Todo: restrict to lower-case letters. *)
Inductive Name : Type := String.

Inductive Prefix : Type :=
| send : Name -> Name -> Prefix
| receive : Name -> Name -> Prefix
| unobservable : Prefix
| conditional : Name -> Name -> Prefix -> Prefix.

Inductive Process : Type :=
| summation : Summation -> Process
| composition : Process -> Process -> Process
| restriction : Name -> Process -> Process
| replication : Process -> Process

with Summation : Type :=
| inaction : Summation
| prefix : Prefix -> Process -> Summation
| sum : Summation -> Summation -> Summation.

(* Definition 1.1.2 *)
Require Import Coq.Sets.Ensembles.
Fixpoint n_pi (pi:Prefix) : Ensemble Name :=
  match pi with
  | send x y => Couple Name x y
  | receive x z => Couple Name x z
  | unobservable => Empty_set Name
  | conditional x y pi' => Union Name (n_pi pi') (Couple Name x y)
  end.

Fixpoint fn_pi (pi:Prefix) : Ensemble Name :=
  match pi with
  | send x y => Couple Name x y
  | receive x z => Singleton Name x
  | unobservable => Empty_set Name
  | conditional x y pi' => Union Name (fn_pi pi') (Couple Name x y)
  end.

Definition bn_pi (pi:Prefix) : Ensemble Name :=
  Setminus Name (n_pi pi) (fn_pi pi).

Fixpoint fn (p:Process) : Ensemble Name :=
  match p with
  | summation (prefix pi p') =>
      Union Name (Setminus Name (fn p') (bn_pi pi)) (fn_pi pi)
  | summation (sum m m') =>
      Union Name (fn (summation m)) (fn (summation m'))
  | summation inaction =>
      Empty_set Name
  | composition p' p'' =>
      Union Name (fn p') (fn p'')
  | restriction z p' =>
      Subtract Name (fn p') z
  | replication p' =>
      fn p'
  end.
