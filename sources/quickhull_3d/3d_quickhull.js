"use strict";

const get_min_max = (V, v_index_list) =>
{
	const min_max_x = [
		reduce_list(v_index_list, bool_reducer((u,v) => V(u).x < V(v).x)),
		reduce_list(v_index_list, bool_reducer((u,v) => V(u).x > V(v).x))
	];
	if(min_max_x[0] !== min_max_x[1]) return min_max_x;

	const min_max_y = [
		reduce_list(v_index_list, bool_reducer((u,v) => V(u).y < V(v).y)),
		reduce_list(v_index_list, bool_reducer((u,v) => V(u).y > V(v).y))
	];
	if(min_max_y[0] !== min_max_y[1]) return min_max_y;
	
	const min_max_z = [
		reduce_list(v_index_list, bool_reducer((u,v) => V(u).y < V(v).y)),
		reduce_list(v_index_list, bool_reducer((u,v) => V(u).y > V(v).y))
	];
	if(min_max_z[0] !== min_max_z[1]) return min_max_z;

	console.error("ne devrait pas arriver");
};

const get_initial_simplex = (vert_l, disp) =>
{
	const v_index_list = new_ordered_int_list(vert_l.length);
	const V = (index) => vert_l[index];

	const edge_ab = get_min_max(V, v_index_list);
	const tri_abc = edge_ab.concat(
			reduce_list(
			v_index_list,
			bool_reducer(
				(v_c1,v_c2) =>
					dist_from_3d_segment(V, v_c1, edge_ab)
					> dist_from_3d_segment(V, v_c2, edge_ab)
			)
		)
	);
	const v_d = reduce_list(
		v_index_list,
		bool_reducer(
			(v_c1,v_c2) =>
				dist_from_3d_plane(V, v_c1, tri_abc)
				> dist_from_3d_plane(V, v_c2, tri_abc)
		)
	);

	const face_base = 
		is_above_3d_plane(V, v_d, tri_abc)
			? [tri_abc[0], tri_abc[2], tri_abc[1]]
			: tri_abc
	;
	const face_a = [face_base[2], face_base[1], v_d];
	const face_b = [face_base[1], face_base[0], v_d];
	const face_c = [face_base[0], face_base[2], v_d];

	return concat_face(concat_face(concat_face(concat_face([], face_base), face_a), face_b), face_c);
}


/*let HE_LIST = [];
HE_LIST = concat_face(HE_LIST, 0, 1, 2);
HE_LIST = concat_face(HE_LIST, 3, 2, 1);
HE_LIST = concat_face(HE_LIST, 4, 3, 1);
HE_LIST = concat_face(HE_LIST, 5, 4, 1);
HE_LIST = concat_face(HE_LIST, 0, 5, 1);

console.table(HE_LIST);*/


// console.log(
// 	dist_from_abc(
// 		vec3(0,0,0),
// 		vec3(1,0,0),
// 		vec3(0,1,0),
// 		vec3(0,0,1)
// 	)
// );
// console.log(
// 	dist_from_abc(
// 		vec3(0,0,0),
// 		vec3(0,0,1),
// 		vec3(1,0,0),
// 		vec3(0,1,0)
// 	)
// );
// console.log(
// 	dist_from_abc(
// 		vec3(0,0,0),
// 		vec3(0,1,0),
// 		vec3(0,0,1),
// 		vec3(1,0,0)
// 	)
// );
