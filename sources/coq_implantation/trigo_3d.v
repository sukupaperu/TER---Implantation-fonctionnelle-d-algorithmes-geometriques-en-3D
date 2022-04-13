Require Import Floats other_structures.
Require Export Floats.

Open Scope float_scope.

Inductive vec3 :=
	Vec3 : float -> float -> float -> vec3
.

Definition vec3_x (v: vec3) : float :=
	match v with
		Vec3 x _ _ => x
	end
.

Definition vec3_y (v: vec3) : float :=
	match v with
		Vec3 _ y _ => y
	end
.

Definition vec3_z (v: vec3) : float :=
	match v with
		Vec3 _ _ z => z
	end
.

Definition dot3 (u v: vec3) : float :=
	match u, v with
		Vec3 x1 y1 z1, Vec3 x2 y2 z2 =>
			x1*x2 + y1*y2 + z1*z2
	end
.

Definition cross (u v: vec3) : vec3 :=
	match u, v with
		Vec3 x1 y1 z1, Vec3 x2 y2 z2 =>
			Vec3 (y1*z2 - z1*y2) (z1*x2 - x1*z2) (x1*y2 - y1*x2)
	end
.

Definition minus3 (u v: vec3) : vec3 :=
	match u, v with
		Vec3 x1 y1 z1, Vec3 x2 y2 z2 =>
		Vec3 (x1 - x2) (y1 - y2) (z1 - z2)
	end
.

Definition multiply3_1 (u: vec3) (s: float) : vec3 :=
	match u, s with
		Vec3 x y z, s => Vec3 (x*s) (y*s) (z*s)
	end
.

Definition clamp1 (x a b: float) : float :=
	if ltb x a then a
	else
		if ltb b x then b else x
.

Definition V (l: list vec3) (index: nat): vec3 :=
	value_in_list_by_index l index (Vec3 0 0 0)
.

Definition dist_from_3d_segment (const_vec3_list: list vec3) (v_p v_a v_b: nat) : float :=
	let p := V const_vec3_list v_p in
	let a := V const_vec3_list v_a in
	let b := V const_vec3_list v_b in
	let pa := minus3 p a in
	let ba := minus3 b a in
	let h := clamp1 ((dot3 pa ba) / (dot3 ba ba)) 0 1 in
	let pa_bah := minus3 pa (multiply3_1 ba h) in
	dot3 pa_bah pa_bah
.

Definition signed_dist_from_plane (const_vec3_list: list vec3) (v_p v_a v_b v_c: nat) : float :=
	let p := V const_vec3_list v_p in
	let a := V const_vec3_list v_a in
	let b := V const_vec3_list v_b in
	let c := V const_vec3_list v_c in
	dot3 (minus3 p a) (cross (minus3 b a) (minus3 c a))
.

Definition absolute_dist_from_plane (const_vec3_list: list vec3) (v_p v_a v_b v_c: nat) : float :=
	abs (signed_dist_from_plane const_vec3_list v_p v_a v_b v_c)
.

Definition vertex_is_above_plane (const_vec3_list: list vec3) (v_p v_a v_b v_c: nat) : bool :=
	ltb (signed_dist_from_plane const_vec3_list v_p v_a v_b v_c) 0.0
.

Close Scope float_scope.