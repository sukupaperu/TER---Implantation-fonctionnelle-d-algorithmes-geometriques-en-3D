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

// vec3 -> vec3 -> vec3 -> scalar
// original function from : https://iquilezles.org/www/articles/distfunctions/distfunctions.htm
const dist_from_3d_segment_vertices = (p, a, b) =>
    {
        const pa = minus3(p, a);
        const ba = minus3(b, a);
        const h = clamp1(dot3(pa, ba)/dot3(ba, ba), 0, 1);
        const pa_bah = minus3(pa, multiply3_1(ba, h));
        return dot3(pa_bah, pa_bah);
    }
;

// vec3 -> int list (2) -> scalar
const dist_from_3d_segment = (p, edge_vertex_index_list) =>
    dist_from_3d_segment_vertices(
        V(p),
        V(value_in_list_by_index(edge_vertex_index_list, 0)),
        V(value_in_list_by_index(edge_vertex_index_list, 1))
    )
;

// vec3 -> vec3 -> vec3 -> vec3 -> scalar
const signed_dist_from_3d_plane_vertices = (p, a, b, c) =>
    dot3(minus3(p, a), cross(minus3(b, a), minus3(c, a)))
;

// vec3 -> int list (3) -> scalar
const signed_dist_from_3d_plane = (p, face_vertex_index_list) =>
    signed_dist_from_3d_plane_vertices(
        V(p),
        V(value_in_list_by_index(face_vertex_index_list, 0)),
        V(value_in_list_by_index(face_vertex_index_list, 1)),
        V(value_in_list_by_index(face_vertex_index_list, 2))
    )
;

// vec3 -> int list (3) -> scalar
const dist_from_3d_plane = (p, face_vertex_index_list) =>
    abs1(signed_dist_from_3d_plane(p, face_vertex_index_list))
;

// vec3 -> int list (3) -> bool
const is_above_3d_plane = (p, face_vertex_index_list) =>
    signed_dist_from_3d_plane(p, face_vertex_index_list) >= 0
;

// vec3 -> dcel -> he -> scalar
const signed_dist_between_vertex_and_plane = (p, dcel, he) =>
    signed_dist_from_3d_plane(p, vertex_index_list_from_face(dcel, he))
;

// vec3 -> dcel -> he -> bool
const vertex_is_above_plane = (p, dcel, he) => 
    is_above_3d_plane(p, vertex_index_list_from_face(dcel, he))
;