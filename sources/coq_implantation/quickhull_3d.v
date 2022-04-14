Require Import trigo_3d dcel_structures other_structures tupple.

(* Definition globalVertexList := (Vec3 0 0 0) :: nil. *)

Definition reduceToFindExtremePointOnAxis (const_vec3_list: list vec3) (vertex_list: list nat) (axis_selector: vec3->float) (extreme_operator: float->float->bool): nat :=
	reduceList
		vertex_list 
		(firstArgIfTrue (fun (a b: nat) => extreme_operator (axis_selector (V const_vec3_list a)) (axis_selector (V const_vec3_list b))))
		(hd 0 vertex_list)
.

Definition differenceOnAxis (const_vec3_list: list vec3) (axis_selector: vec3->float) (index_a index_b: nat) : float :=
	axis_selector (V const_vec3_list index_a) - axis_selector (V const_vec3_list index_b)
.

Definition getFurthestMinAndMax (const_vec3_list: list vec3) (vertex_list: list nat): tupple nat nat :=
	let min_x := reduceToFindExtremePointOnAxis const_vec3_list vertex_list vec3x (fun (a b: float) => ltb a b) in
	let max_x := reduceToFindExtremePointOnAxis const_vec3_list vertex_list vec3x (fun (a b: float) => ltb b a) in
	let min_y := reduceToFindExtremePointOnAxis const_vec3_list vertex_list vec3y (fun (a b: float) => ltb a b) in
	let max_y := reduceToFindExtremePointOnAxis const_vec3_list vertex_list vec3y (fun (a b: float) => ltb b a) in
	let min_z := reduceToFindExtremePointOnAxis const_vec3_list vertex_list vec3z (fun (a b: float) => ltb a b) in
	let max_z := reduceToFindExtremePointOnAxis const_vec3_list vertex_list vec3z (fun (a b: float) => ltb b a) in

	let diff_x := differenceOnAxis const_vec3_list vec3x max_x min_x in
	let diff_y := differenceOnAxis const_vec3_list vec3y max_y min_y in
	let diff_z := differenceOnAxis const_vec3_list vec3z max_z min_z in

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

Definition reduceToFindFurthestPointFromSegment (const_vec3_list: list vec3) (vertex_list: list nat) (v_a v_b: nat) : nat :=
	reduceList
		vertex_list
		(firstArgIfTrue (
		fun	(kept_vertex current_vertex: nat) =>
			ltb
			(distFrom3dSegment const_vec3_list current_vertex v_a v_b)
			(distFrom3dSegment const_vec3_list kept_vertex v_a v_b) 
		))
		0
.

Definition reduceToFindFurthestPointFromPlane (const_vec3_list: list vec3) (vertex_list: list nat) (v_a v_b v_c: nat) : nat :=
	reduceList
		vertex_list
		(firstArgIfTrue (
		fun	(kept_vertex current_vertex: nat) =>
			ltb
			(absoluteDistFromPlane const_vec3_list current_vertex v_a v_b v_c)
			(absoluteDistFromPlane const_vec3_list kept_vertex v_a v_b v_c) 
		))
		0
.

Require Import Nat Bool.

Definition getInitialHull (const_vec3_list: list vec3) (vertex_list: list nat) :=
	let v_a_b := getFurthestMinAndMax const_vec3_list vertex_list in
	let v_a := tuppleFirst v_a_b in
	let v_b := tuppleSecond v_a_b in
	let vertex_list := filterList vertex_list (fun (vertex: nat) => negb (v_a =? vertex)) in
	let vertex_list := filterList vertex_list (fun (vertex: nat) => negb (v_b =? vertex)) in

	let v_c := reduceToFindFurthestPointFromSegment const_vec3_list vertex_list v_a v_b in
	let vertex_list := filterList vertex_list (fun (vertex: nat) => negb (v_c =? vertex)) in

	let v_d := reduceToFindFurthestPointFromPlane const_vec3_list vertex_list v_a v_b v_c in
	let vertex_list := filterList vertex_list (fun (vertex: nat) => negb (v_d =? vertex)) in
	
	(* if vertexIsAbovePlane v_d v_a v_b v_c then *)
	(* v_d + v_c + v_b + v_a *)
	listLength vertex_list
.