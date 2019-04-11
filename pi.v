(* Definition 1.1.1 *)
(* TODO: limit to lower-case? Finite set ranged over? *)
Require Import Coq.Strings.String.
Inductive Name : Type := str : string -> Name.

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

Definition summation_in_process (s:Summation) : Process := summation s.
Coercion summation_in_process : Summation >-> Process.

Declare Custom Entry proc.
Declare Custom Entry prefix.
Declare Custom Entry name.

Notation "[ P ]" := P (P custom proc at level 3, only parsing).

Notation "P | P'" := (composition P P') (in custom proc at level 2, left associativity, only parsing).
Notation "M + M'" := (sum M M') (in custom proc at level 3, left associativity, only parsing).
Notation "pi , P" := (prefix pi P)
  (in custom proc at level 1, pi custom prefix at level 2, right associativity, only parsing).
Notation "'ν' z P" :=
  (restriction z P) (in custom proc at level 1, z custom name at level 2, right associativity, only parsing).
Notation "! P" := (replication P) (in custom proc at level 1, only parsing).
Notation "∅" := (inaction) (in custom proc at level 0, only parsing).
Notation "( P )" := P (in custom proc at level 3).
Notation "P" := P (in custom proc at level 0, P ident).

Notation "{ x ! y }" := (send x y)
  (in custom prefix at level 0, x custom name at level 2, y custom name at level 2, only parsing).
Notation "{ x ( z ) }" := (receive x z)
  (in custom prefix at level 0, x custom name at level 2, z custom name at level 2, only parsing).
Notation "{ [ x = y ] pi }":= (conditional x y pi)
  (in custom prefix at level 1, x custom name at level 2, y custom name at level 2, right associativity, only parsing).
Notation "{ 'τ' }" := (unobservable) (in custom prefix at level 0).
Notation "{ pi }" := pi (in custom prefix at level 0, pi ident).

Notation "x" := (str x%string) (in custom name at level 1, x constr at level 1).
Notation "< x >" := x (in custom name at level 0, x constr at level 1).

(* 0 *)
Example p12_1: Process := [∅].
Print p12_1.
(* π.P *)
Example p12_2 (π: Prefix) (P: Process): Process := [{π},P].
Print p12_2.
(* x̅y.P *)
Example p12_3 (P: Process): Process := [{"x"!"y"},P].
Print p12_3.
(* x(z).P *)
Example p12_4 (P: Process): Process := [{"x"("z")},P].
Print p12_4.
(* x(z).y̅z.0 *)
Example p12_5: Process := [{"x"("z")},{"y"!"z"},∅].
Print p12_5.
(* x(z).z̅y.0 *)
Example p12_6: Process := [{"x"("z")},{"z"!"y"},∅].
Print p12_6.
(* τ.P *)
Example p12_7 (P: Process) : Process := [{τ},P].
Print p12_7.
(* [x=y]π.P *)
Example p12_8 (π: Prefix) (P: Process) := [{["x"="y"]{π}},P].
Print p12_8.
(* x(z).[z=y]z̅w.0 *)
Example p12_9: Process := [{"x"("z")},{["z"="y"]{"z"!"w"}},∅].
Print p12_9.
(* x(z).y(w).[z=w]v̅u.0 *)
Example p12_10: Process := [{"x"("z")},{"y"("w")},{["z"="w"]{"v"!"u"}},∅].
Print p12_10.
(* P + P' *)
Example p12_11 (P:Summation) (P':Summation) : Process := [P + P'].
Print p12_11.
(* x(z).z̅y.0 + w̅v.0 *)
Example p12_12: Process := [{"x"("z")},{"z"!"y"},∅ + {"w"!"v"},∅].
Print p12_12.
(* P | P' *)
Example p12_13 (P:Process) (P':Process) : Process := [P | P'].
Print p12_13.
(* (x(z).z̅y.0 + w̅v.0) | x̅u.0 *)
Example p12_14 : Process := [({"x"("z")},{"z"!"y"},∅ + {"w"!"v"},∅) | {"x"!"u"},∅].
Print p12_14.
(* νz P *)
Example p12_15 (z:Name) (P:Process) : Process := [ν <z> P].
Print p12_15.
(* νx((x(z).z̅y.0 + w̅v.0) |  x̅u.0) *)
Example p12_16 : Process := [ν "x" (({"x"("z")},{"z"!"y"},∅ + {"w"!"v"},∅) | {"x"!"u"},∅)].
Print p12_16.
(* !P *)
Example p13_1 (P:Process) : Process := [!P].
Print p13_1.
(* !x(z).!y̅z.0 *)
Example p13_2 : Process := [!{"x"("z")},!{"y"!"z"},∅].
Print p13_2.

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
  let fix fn_sum(s:Summation) : Ensemble Name :=
    match s with
    | prefix pi p' => Union Name (Setminus Name (fn p') (bn_pi pi)) (fn_pi pi)
    | sum m m' => Union Name (fn_sum m) (fn_sum m')
    | inaction => Empty_set Name
    end
  in
  match p with
  | summation m => fn_sum m
  | composition p' p'' => Union Name (fn p') (fn p'')
  | restriction z p' => Subtract Name (fn p') z
  | replication p' => fn p'
  end.

Fixpoint n (p:Process) : Ensemble Name :=
  let fix n_sum(s:Summation) : Ensemble Name :=
    match s with
    | prefix pi p' => Union Name (n p') (n_pi pi)
    | sum m m' => Union Name (n_sum m) (n_sum m')
    | inaction => Empty_set Name
    end
  in
  match p with
  | summation m => n_sum m
  | composition p' p'' => Union Name (n p') (n p'')
  | restriction z p' => Add Name (n p') z
  | replication p' => n p'
  end.

Definition bn (p:Process) : Ensemble Name :=
  Setminus Name (n p) (fn p).

(* fn((z̅y.0 + w̅v.0) | x̅u.0) = {z,y,w,v,x,u} *)
Example p13_3 : Same_set Name (Singleton Name (str "x")) (Singleton Name (str "x")).
Proof.
  auto with *.
  Qed.

Require Import Coq.Sets.Powerset_facts.
Example p13_4_simpl:
  Same_set Name
    ( fn([ {"x"!"y"},∅ ]) )
    ( Couple Name (str "x") (str "y") ).
Proof.
  simpl.
  unfold bn_pi.
  unfold n_pi, fn_pi.
  rewrite -> Setminus_Included_empty.
  auto with *.
  auto with *.
  Qed.

Example p13_4:
  Same_set Name
    ( fn([ ({"z"!"y"},∅ + {"w"!"v"},∅) | {"x"!"u"},∅ ]) )
    ( Union Name
       (Triple Name (str "z") (str "y") (str "w"))
       (Triple Name (str "v") (str "x") (str "u")) ).
Proof.
  simpl.
  unfold bn_pi, n_pi, fn_pi.
  rewrite -> Setminus_Included_empty.
  rewrite -> Setminus_Included_empty.
  rewrite -> Setminus_Included_empty.
  rewrite -> Empty_set_zero.
  rewrite -> Empty_set_zero.
  rewrite -> Empty_set_zero.
  rewrite <- Couple_as_union.
  rewrite <- Couple_as_union.
  rewrite <- Couple_as_union.
  rewrite <- Triple_as_union.
  rewrite <- Triple_as_union.
  rewrite -> Union_associative.
  rewrite -> Union_associative.
  rewrite -> Union_associative.
  rewrite -> Union_associative.
  rewrite -> Union_associative.
  rewrite -> Union_associative.
  auto with *.
  auto with *.
  auto with *.
  auto with *.
  Qed.

(* Definition 1.1.3 *)
Require Import Coq.Sets.Finite_sets.
Definition substitution (f:Name -> Name) :=
  exists2 X: Ensemble Name, Finite Name X &
   forall x, In Name X x -> f x <> x /\ ~ In Name X x -> f x = x.

(* Notation 1.1.4 *)
