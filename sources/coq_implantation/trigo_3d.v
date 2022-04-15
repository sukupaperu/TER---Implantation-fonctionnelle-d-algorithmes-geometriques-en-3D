Require Import Floats other_structures.
Require Export Floats.

Open Scope float_scope.

Inductive vec3 :=
	Vec3 : float -> float -> float -> vec3
.

Definition vec3x (v: vec3) : float :=
	match v with
		Vec3 x _ _ => x
	end
.

Definition vec3y (v: vec3) : float :=
	match v with
		Vec3 _ y _ => y
	end
.

Definition vec3z (v: vec3) : float :=
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

Definition abs1 (x: float) : float :=
	if ltb x zero then -x else x
.

Definition distFrom3dSegment (p a b: vec3) : float :=
	let pa := minus3 p a in
	let ba := minus3 b a in
	let h := clamp1 ((dot3 pa ba) / (dot3 ba ba)) zero one in
	let pa_bah := minus3 pa (multiply3_1 ba h) in
	dot3 pa_bah pa_bah
.

Definition signedDistFromPlane (p a b c: vec3) : float :=
	dot3 (minus3 p a) (cross (minus3 b a) (minus3 c a))
.

Definition absoluteDistFromPlane (p a b c: vec3) : float :=
	abs1 (signedDistFromPlane p a b c)
.

Definition vertexIsAbovePlane (p a b c: vec3) : bool :=
	ltb (signedDistFromPlane p a b c) zero
.

Close Scope float_scope.