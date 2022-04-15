Require Import trigo_3d dcel_structures other_structures.

Definition getVec3InListFunctor (l: list vec3): nat->option vec3 :=
	fun (index: nat) => valueInListByIndex l index
.

Definition reduceToFindExtremePointOnAxis (getVec3: nat->option vec3) (vertex_list: list nat) (axis_selector: vec3->float) (operator: float->float->bool): option nat :=
	reduceListSimpleOption
		vertex_list 
		(fun (a b: nat) => 
			match (getVec3 a), (getVec3 b) with
			| Some v_a, Some v_b => Some (if operator (axis_selector v_a) (axis_selector v_b) then a else b)
			| _, _ => None
			end
		)
.

Definition differenceOnAxis (getVec3: nat->option vec3) (axis_selector: vec3->float) (a b: nat) : option float :=
	match (getVec3 a), (getVec3 b) with
	| Some v_a, Some v_b => Some (abs1 (sub (axis_selector v_a) (axis_selector v_b)))
	| _, _ => None
	end
.

Definition getFurthestMinAndMax (getVec3: nat->option vec3) (vertex_list: list nat): option (nat*nat) :=
	match
		reduceToFindExtremePointOnAxis getVec3 vertex_list vec3x (fun (a b: float) => ltb a b),
		reduceToFindExtremePointOnAxis getVec3 vertex_list vec3x (fun (a b: float) => ltb b a),
		reduceToFindExtremePointOnAxis getVec3 vertex_list vec3y (fun (a b: float) => ltb a b),
		reduceToFindExtremePointOnAxis getVec3 vertex_list vec3y (fun (a b: float) => ltb b a),
		reduceToFindExtremePointOnAxis getVec3 vertex_list vec3z (fun (a b: float) => ltb a b),
		reduceToFindExtremePointOnAxis getVec3 vertex_list vec3z (fun (a b: float) => ltb b a)
	with
	| Some min_x, Some max_x, Some min_y, Some max_y, Some min_z, Some max_z =>
		match
			differenceOnAxis getVec3 vec3x min_x max_x,
			differenceOnAxis getVec3 vec3y min_y max_y,
			differenceOnAxis getVec3 vec3z min_z max_z
		with
		| Some x_diff, Some y_diff, Some z_diff =>
			if ltb y_diff x_diff then
				if ltb z_diff x_diff then Some (min_x, max_x) else Some (min_z, max_z)
			else
				if ltb z_diff y_diff then Some (min_y, max_y) else Some (min_z, max_z)
		| _, _, _ => None
		end
	| _, _, _, _, _, _ => None
	end
.

Definition reduceToFindFurthestPointFromSegment (getVec3: nat->option vec3) (vertex_list: list nat) (a b: nat) : option nat :=
	match (getVec3 a), (getVec3 b) with
	| Some v_a, Some v_b =>
		reduceListSimpleOption
			vertex_list
			(fun (c d: nat) => 
				match (getVec3 c), (getVec3 d) with
				| Some v_c, Some v_d => Some (if ltb (distFrom3dSegment v_c v_a v_b) (distFrom3dSegment v_d v_a v_b) then d else c)
				| _, _ => None
				end
			)
	| _, _ => None
	end
.

Definition reduceToFindFurthestPointFromPlane (getVec3: nat->option vec3) (vertex_list: list nat) (a b c: nat) : option nat :=
	match (getVec3 a), (getVec3 b), (getVec3 c) with
	| Some v_a, Some v_b, Some v_c =>
		reduceListSimpleOption
			vertex_list
			(fun (d e: nat) => 
				match (getVec3 d), (getVec3 e) with
				| Some v_d, Some v_e => Some (if ltb (absoluteDistFromPlane v_d v_a v_b v_c) (absoluteDistFromPlane v_e v_a v_b v_c) then e else d)
				| _, _ => None
				end
			)
	| _, _, _ => None
	end
.

Require Import Nat Bool.

Definition getInitialHull (getVec3: nat->option vec3) (vertex_list: list nat) :=
	match getFurthestMinAndMax getVec3 vertex_list with
	| Some (v_a, v_b) =>
		let vertex_list := filter (fun (vertex: nat) => negb (v_a =? vertex)) vertex_list in
		let vertex_list := filter (fun (vertex: nat) => negb (v_b =? vertex)) vertex_list in

		match reduceToFindFurthestPointFromSegment getVec3 vertex_list v_a v_b with
		| Some v_c =>
			let vertex_list := filter (fun (vertex: nat) => negb (v_c =? vertex)) vertex_list in

			match reduceToFindFurthestPointFromPlane getVec3 vertex_list v_a v_b v_c with
			| Some v_d => 
				let vertex_list := filter (fun (vertex: nat) => negb (v_d =? vertex)) vertex_list in

				match getVec3 v_a, getVec3 v_b, getVec3 v_c, getVec3 v_d with
				| Some a, Some b, Some c, Some d =>
					let tetrahedron_hull :=
						if vertexIsAbovePlane d a b c then
							addFace (addFace (addFace (addFace emptyDcel v_a v_c v_b) v_b v_c v_d) v_c v_a v_d) v_a v_b v_d
						else
							addFace (addFace (addFace (addFace emptyDcel v_a v_c v_b) v_b v_c v_d) v_c v_a v_d) v_a v_b v_d
						in
					Some tetrahedron_hull
				| _, _, _, _ => None
				end
				(* Some (length vertex_list) *)
			| _ => None
			end
		| None => None
		end
	| None => None
	end
.