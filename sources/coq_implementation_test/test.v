Require Import _3d_trigo List.
Require Import global_v_list.
Require Import Arith.

Require Extraction.

Extraction Language Haskell.

Extract Constant float => "Prelude.Float".
Extract Constant mul => "\x y-> x*y".

Extraction "haskell/test" cross.

(* Check 1 :: nil.
Print all.

Fixpoint value_in_list_by_index_rec (T: Type) (l: list T) (i: nat) (d: T) (j: nat): T :=
  match l with
    | nil => d
    | a :: b =>
      if beq_nat i j
      then a
      else value_in_list_by_index_rec T b i d (S j)
  end
.
Fixpoint value_in_list_by_index (T: Type) (l: list T) (i: nat) (d: T): T :=
  value_in_list_by_index_rec T l i d 0
.

Fixpoint reduce (T U: Type) (l: list T) (f: T->U->U) (d: U): U :=
  match l with
    | nil => d
    | a :: b =>
      f a (reduce T U b f d)
  end
.

Definition first_arg_if_true (T: Type) (f: T->T->bool) : T->T->T :=
  fun (a b: T) => if (f a b) then a else b
.


(* Eval compute in value_in_list_by_index vec3 GLOBAL_V_LIST 5 (Vec3 0 0 0). *)
(* Eval compute in (ltb (-1.0) 2.0). *)
(* Definition compare_x (u v: vec3) : bool := ltb (vec3_x u) (vec3_x v). *)
Definition min_in_vec3_list := fun (vec3_coord: vec3->float) => reduce vec3 vec3 GLOBAL_V_LIST (first_arg_if_true vec3 (
  fun (u v: vec3) => ltb (vec3_coord u) (vec3_coord v)
)) (Vec3 0 0 0).
Definition max_in_vec3_list := fun (vec3_coord: vec3->float) => reduce vec3 vec3 GLOBAL_V_LIST (first_arg_if_true vec3 (
  fun (v u: vec3) => ltb (vec3_coord u) (vec3_coord v)
)) (Vec3 0 0 0).

Definition min_x := min_in_vec3_list vec3_x.
Definition max_x := max_in_vec3_list vec3_x.
Definition min_y := min_in_vec3_list vec3_y.
Definition max_y := max_in_vec3_list vec3_y.
Definition min_z := min_in_vec3_list vec3_z.
Definition max_z := max_in_vec3_list vec3_z.

Eval compute in pair 1 2.

(* Definition get_furthest_min_and_max :=
  
. *)

Eval compute in min_x.
Eval compute in max_x. *)