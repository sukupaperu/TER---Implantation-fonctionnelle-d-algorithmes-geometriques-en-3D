"use strict";

// ---- Fonctions trigonométriques et géométriques ----

// scalar -> scalar -> scalar -> vec3
const vec3 = (x, y, z) =>
    ({
        x:x,
        y:y,
        z:z
    })
;

// vec3 -> vec3 -> scalar
const dot3 = (u, v) =>
    u.x*v.x + u.y*v.y + u.z*v.z
;

// vec3 -> vec3 -> vec3
const cross = (u, v) =>
    vec3(
        (u.y*v.z - u.z*v.y),
        (u.z*v.x - u.x*v.z),
        (u.x*v.y - u.y*v.x),
    )
;

// vec3 -> vec3 -> vec3
const minus3 = (u, v) =>
    vec3(u.x - v.x, u.y - v.y, u.z - v.z)
;

// vec3 -> scalar
const norm3 = (u) =>
    Math.sqrt(u.x*u.x + u.y*u.y + u.z*u.z)
;

// vec3 -> vec3
const normalize3 = (u) =>
    divide3_1(u, norm3(u))
;

// vec3 -> scalar -> vec3
const divide3_1 = (u, s) =>
    vec3(u.x/s, u.y/s, u.z/s)
;

// vec3 -> scalar -> vec3
const multiply3_1 = (u, s) =>
    vec3(u.x*s, u.y*s, u.z*s)
;

// vec3 -> scalar -> vec3
const minus3_1 = (u, s) =>
    vec3(u.x - s, u.y - s, u.z - s)
;

// scalar -> scalar -> scalar -> scalar
const clamp1 = (v, a, b) =>
    v < a
        ? a
        : v > b
            ? b
            : v
;

// scalar -> scalar
const abs1 = (a) =>
    Math.abs(a)
;

// int -> int -> int -> scalar
// original function from : https://iquilezles.org/www/articles/distfunctions/distfunctions.htm
const dist_from_3d_segment = (v_p, v_a, v_b) =>
    {
        const p = V(v_p), a = V(v_a), b = V(v_b);
        const pa = minus3(p, a), ba = minus3(b, a);
        const h = clamp1(dot3(pa, ba)/dot3(ba, ba), 0, 1);
        const pa_bah = minus3(pa, multiply3_1(ba, h));
        return dot3(pa_bah, pa_bah);
    }
;

// int -> int -> int -> int -> scalar
const signed_dist_from_plane = (v_p, v_a, v_b, v_c) =>
    {
        const p = V(v_p), a = V(v_a), b = V(v_b), c = V(v_c);
        return dot3(
            minus3(p, a),
            cross(minus3(b, a), minus3(c, a))
        );
    }
;

// int -> int -> int -> int -> scalar
const absolute_dist_from_plane = (v_p, v_a, v_b, v_c) =>
    abs1(signed_dist_from_plane(v_p, v_a, v_b, v_c))
;

// int -> int -> int -> int -> bool
const vertex_is_above_plane = (v_p, v_a, v_b, v_c) =>
    signed_dist_from_plane(v_p, v_a, v_b, v_c) >= 0
;

// int -> dcel -> he -> scalar
const signed_dist_from_face_plane = (v_p, dcel, he_of_face) =>
    absolute_dist_from_plane(
        v_p,
        source_vertex_of_he(he_of_face),
        destination_vertex_of_he(dcel, he_of_face),
        destination_vertex_of_he(dcel, next_he(dcel, he_of_face))
    )
;

// int -> dcel -> he -> bool
const vertex_is_above_face_plane = (v_p, dcel, he_of_face) => 
    vertex_is_above_plane(
        v_p,
        source_vertex_of_he(he_of_face),
        destination_vertex_of_he(dcel, he_of_face),
        destination_vertex_of_he(dcel, next_he(dcel, he_of_face))
    )
;