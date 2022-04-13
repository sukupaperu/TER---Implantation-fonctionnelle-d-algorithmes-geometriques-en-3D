Require Import trigo_3d dcel_structures other_structures tupple.

(* Definition globalVertexList := (Vec3 0 0 0) :: nil. *)

Definition reduce_to_find_extreme_point_on_axis (const_vec3_list: list vec3) (vertex_list: list nat) (axis_selector: vec3->float) (extreme_operator: float->float->bool): nat :=
	reduce_list
		vertex_list 
		(first_arg_if_true (fun (a b: nat) => extreme_operator (axis_selector (V const_vec3_list a)) (axis_selector (V const_vec3_list b))))
		(hd 0 vertex_list)
.

Definition difference_on_axis (const_vec3_list: list vec3) (axis_selector: vec3->float) (index_a index_b: nat) : float :=
	axis_selector (V const_vec3_list index_a) - axis_selector (V const_vec3_list index_b)
.

Definition get_furthest_min_and_max (const_vec3_list: list vec3) (vertex_list: list nat): tupple nat nat :=
	let min_x := reduce_to_find_extreme_point_on_axis const_vec3_list vertex_list vec3_x (fun (a b: float) => ltb a b) in
	let max_x := reduce_to_find_extreme_point_on_axis const_vec3_list vertex_list vec3_x (fun (a b: float) => ltb b a) in
	let min_y := reduce_to_find_extreme_point_on_axis const_vec3_list vertex_list vec3_y (fun (a b: float) => ltb a b) in
	let max_y := reduce_to_find_extreme_point_on_axis const_vec3_list vertex_list vec3_y (fun (a b: float) => ltb b a) in
	let min_z := reduce_to_find_extreme_point_on_axis const_vec3_list vertex_list vec3_z (fun (a b: float) => ltb a b) in
	let max_z := reduce_to_find_extreme_point_on_axis const_vec3_list vertex_list vec3_z (fun (a b: float) => ltb b a) in

	let diff_x := difference_on_axis const_vec3_list vec3_x max_x min_x in
	let diff_y := difference_on_axis const_vec3_list vec3_y max_y min_y in
	let diff_z := difference_on_axis const_vec3_list vec3_z max_z min_z in

	if ltb diff_y diff_x then
		if ltb diff_z diff_x then
			Tupple nat nat min_x max_x
		else
			Tupple nat nat min_z max_z
	else
		if ltb diff_z diff_y then
			Tupple nat nat min_y max_y
		else
			Tupple nat nat min_z max_z
.

Definition reduce_to_find_furthest_point_from_segment (const_vec3_list: list vec3) (vertex_list: list nat) (v_a v_b: nat) : nat :=
	reduce_list
		vertex_list
		(first_arg_if_true (
		fun	(kept_vertex current_vertex: nat) =>
			ltb
			(dist_from_3d_segment const_vec3_list current_vertex v_a v_b)
			(dist_from_3d_segment const_vec3_list kept_vertex v_a v_b) 
		))
		0
.

Definition reduce_to_find_furthest_point_from_plane (const_vec3_list: list vec3) (vertex_list: list nat) (v_a v_b v_c: nat) : nat :=
	reduce_list
		vertex_list
		(first_arg_if_true (
		fun	(kept_vertex current_vertex: nat) =>
			ltb
			(absolute_dist_from_plane const_vec3_list current_vertex v_a v_b v_c)
			(absolute_dist_from_plane const_vec3_list kept_vertex v_a v_b v_c) 
		))
		0
.

Require Import Nat Bool.

Definition get_initial_hull (const_vec3_list: list vec3) (vertex_list: list nat) :=
	let v_a_b := get_furthest_min_and_max const_vec3_list vertex_list in
	let v_a := tupple_first v_a_b in
	let v_b := tupple_second v_a_b in
	let vertex_list := filter_list vertex_list (fun (vertex: nat) => negb ((v_a =? vertex) && (v_b =? vertex))) in

	let v_c := reduce_to_find_furthest_point_from_segment const_vec3_list vertex_list v_a v_b in
	let vertex_list := filter_list vertex_list (fun (vertex: nat) => negb (v_c =? vertex)) in

	let v_d := reduce_to_find_furthest_point_from_plane const_vec3_list vertex_list v_a v_b v_c in
	let vertex_list := filter_list vertex_list (fun (vertex: nat) => negb (v_d =? vertex)) in
	
	(* if vertex_is_above_plane v_d v_a v_b v_c then *)
	v_d
.