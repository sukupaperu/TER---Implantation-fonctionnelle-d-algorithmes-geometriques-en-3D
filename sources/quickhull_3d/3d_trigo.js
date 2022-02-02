"use strict";

const dot3 = (u,v) => u.x*v.x + u.y*v.y + u.z*v.z;
const cross = (u,v) => vec3(
	(u.y*v.z - u.z*v.y),
	(u.z*v.x - u.x*v.z),
	(u.x*v.y - u.y*v.x),
);
const minus3 = (u,v) => vec3(u.x - v.x, u.y - v.y, u.z - v.z);
const norm3 = (u) => Math.sqrt(u.x**2 + u.y**2 + u.z**2);
const normalize3 = (u) => divide3_1(u, norm3(u));

const divide3_1 = (u,s) => vec3(u.x/s, u.y/s, u.z/s);
const multiply3_1 = (u,s) => vec3(u.x*s, u.y*s, u.z*s);
const minus3_1 = (u,s) => vec3(u.x - s, u.y - s, u.z - s);

const clamp = (v,a,b) => v < a ? a : v > b ? b : v;
const abs = (a) => Math.abs(a);

// from : https://iquilezles.org/www/articles/distfunctions/distfunctions.htm
const dist_from_3d_segment_vertices = (p,a,b) =>
    {
        const pa = minus3(p, a);
        const ba = minus3(b, a);
        const h = clamp(dot3(pa, ba)/dot3(ba, ba), 0, 1);
        const pa_bah = minus3(pa, multiply3_1(ba, h));
        return dot3(pa_bah, pa_bah);
    }
;
const dist_from_3d_segment = (p,edge) => dist_from_3d_segment_vertices(V(p), V(edge[0]), V(edge[1]));

const signed_dist_from_3d_plane_vertices = (p,a,b,c) => dot3(minus3(p, a), cross(minus3(b, a), minus3(c, a)));
const dist_from_3d_plane_vertices = (p,a,b,c) => abs(signed_dist_from_3d_plane_vertices(p,a,b,c));

const dist_from_3d_plane = (p,tri) => dist_from_3d_plane_vertices(V(p), V(tri[0]), V(tri[1]), V(tri[2]));
const is_above_3d_plane = (p,tri) => signed_dist_from_3d_plane_vertices(V(p), V(tri[0]), V(tri[1]), V(tri[2])) >= 0;
const he_is_above_3d_plane = (p,he_l,he) => signed_dist_from_3d_plane_vertices(V(p), V(he_from_vert(he)), V(he_to_vert(he_l, he)), V(he_to_vert(he_l, he_next(he_l, he)))) >= 0;