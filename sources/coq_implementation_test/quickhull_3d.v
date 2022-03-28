Require Import trigo_3d other_structures.

Definition V (l: list vec3) (index: nat): vec3 :=
	value_in_list_by_index vec3 l index (Vec3 0 0 0)
.

Definition get_furthest_min_and_max (gbl: list vec3) (vertex_list: list nat): nat :=
	let min_x :=
		reduce_list nat nat vertex_list 
		(first_arg_if_true nat (fun (a b: nat) => ltb (vec3_x (V gbl a)) (vec3_x (V gbl b))))
		(hd 0 vertex_list) in
	min_x
.

(* reduce_list 

Fixpoint reduce_list (A B: Set) (l: list A) (action_on_reduce: A->B->B) (default: B): B := *)




(* Definition first_arg_if_true (T: Type) (f: T->T->bool) : T->T->T :=
	fun (a b: T) => if (f a b) then a else b
. *)

(* first_arg_if_true nat   *)