Require Import Floats.
Require Export Floats.

Open Scope float_scope.

Inductive vec3 :=
  Vec3 : float -> float -> float -> vec3
.

Definition vec3_x (v: vec3) := match v with
    Vec3 x _ _ => x
end.

Definition vec3_y (v: vec3) := match v with
    Vec3 _ y _ => y
end.

Definition vec3_z (v: vec3) := match v with
    Vec3 _ _ z => z
end.

Definition dot3 (u v: vec3) := match u, v with
    Vec3 x1 y1 z1, Vec3 x2 y2 z2 =>
      x1*x2 + y1*y2 + z1*z2
end.

Definition cross (u v: vec3) := match u, v with
    Vec3 x1 y1 z1, Vec3 x2 y2 z2 =>
      Vec3 (y1*z2 - z1*y2) (z1*x2 - x1*z2) (x1*y2 - y1*x2)
end.

Definition minus3 (u v: vec3) := match u, v with
    Vec3 x1 y1 z1, Vec3 x2 y2 z2 =>
      Vec3 (x1 - x2) (y1 - y2) (z1 - z2)
end.

Definition multiply3_1 (u: vec3) (s: float) := match u, s with
  Vec3 x y z, s => Vec3 (x*s) (y*s) (z*s)
end.