"use strict";

const get_min_max = (v_l) =>
{
	const min_max_list =
		v_l.reduce(
			(res, v) =>
				[
					[
						V(v).x < V(res[0][0]).x ? v : res[0][0],
						V(v).x > V(res[0][1]).x ? v : res[0][1]
					],
					[
						V(v).y < V(res[1][0]).y ? v : res[1][0],
						V(v).y > V(res[1][1]).y ? v : res[1][1]
					],
					[
						V(v).z < V(res[2][0]).z ? v : res[2][0],
						V(v).z > V(res[2][1]).z ? v : res[2][1]
					]
				]
			,
			[[0, 0], [0, 0], [0, 0],]
		);
	
	const min_max_x = min_max_list[0];
	const min_max_y = min_max_list[1];
	const min_max_z = min_max_list[2];

	const diff_x = min_max_x[1] - min_max_x[0];
	const diff_y = min_max_y[1] - min_max_y[0];
	const diff_z = min_max_z[1] - min_max_z[0];
	
	return diff_x > diff_y
		? diff_x > diff_z
			? min_max_x
			: min_max_z
		: diff_y > diff_z
			? min_max_y
			: min_max_z;
};

const get_initial_simplex = (v_index_list) =>
{
	const edge_ab = get_min_max(v_index_list);
	
	const v_c = v_index_list.reduce(
		bool_reducer(
			(v_c1,v_c2) =>
				dist_from_3d_segment(v_c1, edge_ab) > dist_from_3d_segment(v_c2, edge_ab)
		)
	);

	const tri_abc = edge_ab.concat(v_c);
	
	const v_d = v_index_list.reduce(
		bool_reducer(
			(v_c1,v_c2) =>
				dist_from_3d_plane(v_c1, tri_abc) > dist_from_3d_plane(v_c2, tri_abc)
		)
	);

	const face_base = 
		is_above_3d_plane(v_d, tri_abc)
			? [tri_abc[0], tri_abc[2], tri_abc[1]]
			: tri_abc
	;
	const face_a = [face_base[2], face_base[1], v_d];
	const face_b = [face_base[1], face_base[0], v_d];
	const face_c = [face_base[0], face_base[2], v_d];

	return [
		concat_face(concat_face(concat_face(concat_face([], face_base), face_a), face_b), face_c),
		tri_abc.concat(v_d)
	];
}

const explore_and_remove_visible_faces_from_p = (he_l, he, p) =>
{
	const explore_and_remove_2 = (he_l, he_index, p) =>
	{
		if(he_index == -1)
		    return he_l;

		const he = he_l[he_index];

		if(!he_is_above_3d_plane(p, he_l, he))
			return he_l;

		const he_left = he_prev(he_l, he);
		const he_right = he_next(he_l, he);

		const he_left_opposite_index = he_opposite_index(he_left);
		const he_right_opposite_index = he_opposite_index(he_right);

		const new_he_l = remove_face(he_l, he);
		const left_he_l = explore_and_remove_2(new_he_l, he_left_opposite_index, p);
		const right_he_l = explore_and_remove_2(left_he_l, he_right_opposite_index, p);

		return right_he_l;
	}

	const he_left = he_prev(he_l, he);
    const he_right = he_next(he_l, he);

	const he_left_opposite_index = he_opposite_index(he_left);
	const he_curr_opposite_index = he_opposite_index(he);
	const he_right_opposite_index = he_opposite_index(he_right);

	const new_he_l = remove_face(he_l, he);
	const left_he_l = explore_and_remove_2(new_he_l, he_left_opposite_index, p);
	const curr_he_l = explore_and_remove_2(left_he_l, he_curr_opposite_index, p);
	const right_he_l = explore_and_remove_2(curr_he_l, he_right_opposite_index, p);

	return right_he_l;
}

const quick_hull_3d_2 = (he_l_hull, curr_face_index, v_l) =>
{
	const he_curr_face = he_by_face_index(he_l_hull, curr_face_index);

	const v_furthest = v_l.reduce(
		bool_reducer(
			(v_a, v_b) =>
				he_signed_dist_from_3d_plane(v_a, he_l_hull, he_curr_face)
				> he_signed_dist_from_3d_plane(v_b, he_l_hull, he_curr_face)
		)
	);

	if(!he_is_above_3d_plane(v_furthest, he_l_hull, he_curr_face))
		return he_l_hull;

	const he_l_temp_hull = explore_and_remove_visible_faces_from_p(he_l_hull, he_curr_face, v_furthest);

	const he_border_index_l = he_l_temp_hull.filter(
		(he) => he_is_boundary(he)
	);

	const he_l_final_hull = he_border_index_l.reduce(
		(he_l_hull, he) =>
			concat_face(
				he_l_hull, 
				[
					he_to_vert(he_l_hull, he),
					he_from_vert(he),
					v_furthest
				]
			)
		,
		he_l_temp_hull
	);
}

const quick_hull_3d = (v_vec3_l) =>
{
	const v_l = new_ordered_int_list(v_vec3_l.length);
	
	const [he_l_initial_simplex, v_l_initial_simplex] = get_initial_simplex(v_l);

	const v_l_filtered = v_l.filter(
		(v_index) =>
			!is_defined(v_l_initial_simplex.find(
				(v_index_in) => v_index_in === v_index
			))
			&& is_defined(he_l_initial_simplex.find(
				(he_face) => he_is_above_3d_plane(v_index, he_l_initial_simplex, he_face)
			))
	);

	quick_hull_3d_2(he_l_initial_simplex, 0, v_l_filtered);

	return he_l_initial_simplex;
}