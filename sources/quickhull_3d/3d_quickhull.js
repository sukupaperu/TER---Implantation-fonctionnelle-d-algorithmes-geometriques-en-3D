"use strict";

const get_min_max = (v_l) =>
{
	const [min_max_x, min_max_y, min_max_z] = v_l.reduce(
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
			[[0, 0], [0, 0], [0, 0]]
		)
	;

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

const get_initial_simplex = (v_l) =>
{
	// liste de sommets du segment ab
	const edge_ab = get_min_max(v_l);
	
	// sommet c, le plus éloigné du segment ab parmi v_l
	const v_c = v_l.reduce(
		bool_reducer(
			(v_c1,v_c2) =>
				dist_from_3d_segment(v_c1, edge_ab) > dist_from_3d_segment(v_c2, edge_ab)
		)
	);
	
	// liste de sommets du triangle abc
	const tri_abc = edge_ab.concat(v_c);
	
	// sommet d, le plus éloigné du plan formé par le triangle abc
	const v_d = v_l.reduce(
		bool_reducer(
			(v_c1,v_c2) =>
				dist_from_3d_plane(v_c1, tri_abc) > dist_from_3d_plane(v_c2, tri_abc)
		)
	);
	
	// liste de sommets
	// la liste (triangle abc) est réordonnée pour correctement orienter la face
	const face_base_abc = 
		is_above_3d_plane(v_d, tri_abc)
			? [tri_abc[0], tri_abc[2], tri_abc[1]]
			: tri_abc
	;
	// listes de sommets
	// on construit les autres faces
	const face_A = [face_base_abc[2], face_base_abc[1], v_d];
	const face_B = [face_base_abc[1], face_base_abc[0], v_d];
	const face_C = [face_base_abc[0], face_base_abc[2], v_d];
	
	// liste de sommets du tétrahèdre abcd
	const tetrahedron_abcd = tri_abc.concat(v_d);
	// liste de sommets
	// ensemble de sommets v_l mais sans les sommets du tétrahèdre abcd
	const v_l_wo_initial_simplex_vertices = v_l.filter(
		(v_curr) =>
			!is_defined(tetrahedron_abcd.find(
				(v_tetrahedron) => v_tetrahedron === v_curr
			))
	);

	return [
		// construction du tétrahèdre
		concat_face(concat_face(concat_face(concat_face([], face_base_abc), face_A), face_B), face_C),
		v_l_wo_initial_simplex_vertices
	]
}

const explore_and_remove_visible_faces_from_p = (he_l, he, p) =>
{
	const explore_and_remove_2 = ([he_l, he_l_deleted], he_index, p) =>
	{
		if(he_index == -1)
		    return [he_l, he_l_deleted];

		const he = he_l[he_index];

		if(!he_is_above_3d_plane(p, he_l, he))
			return [he_l, he_l_deleted];

		const he_left = he_prev(he_l, he);
		const he_right = he_next(he_l, he);

		const he_left_opposite_index = he_opposite_index(he_left);
		const he_right_opposite_index = he_opposite_index(he_right);

		// const he_l_deleted_updated = he_concat_face(he_l_deleted, he_l, he);
		const he_l_deleted_updated = he_l_deleted.concat(he);
		//he_concat_face(he_l_deleted, he_l, he);
		const new_he_l = remove_face(he_l, he);
		const left_res = explore_and_remove_2([new_he_l, he_l_deleted_updated], he_left_opposite_index, p);
		const right_res = explore_and_remove_2(left_res, he_right_opposite_index, p);

		return right_res;
	}

	const he_left = he_prev(he_l, he);
    const he_right = he_next(he_l, he);

	const he_left_opposite_index = he_opposite_index(he_left);
	const he_curr_opposite_index = he_opposite_index(he);
	const he_right_opposite_index = he_opposite_index(he_right);

	// const he_l_deleted = he_concat_face([], he_l, he);
	const he_l_deleted = [].concat(he);
	const new_he_l = remove_face(he_l, he);
	const left_res = explore_and_remove_2([new_he_l, he_l_deleted], he_left_opposite_index, p);
	const middle_res = explore_and_remove_2(left_res, he_curr_opposite_index, p);
	const right_res = explore_and_remove_2(middle_res, he_right_opposite_index, p);

	return right_res;
}

const quick_hull_3d_2 = (he_l_hull, v_l_set_per_face) =>
{
	const he_face_index_found = v_l_set_per_face.findIndex(
		(v_l_subset) => !list_is_empty(v_l_subset)
	);

	if(he_face_index_found === -1)
		return he_l_hull;

	const v_l_curr_set = v_l_set_per_face[he_face_index_found];
	const he_curr_face = he_by_face_index(he_l_hull, he_face_index_found);
	
	const v_furthest = v_l_curr_set.reduce(
		bool_reducer(
			(v_a, v_b) =>
				he_signed_dist_from_3d_plane(v_a, he_l_hull, he_curr_face)
				> he_signed_dist_from_3d_plane(v_b, he_l_hull, he_curr_face)
		)
	);

	const [he_l_opened_hull, he_l_faces_deleted] = explore_and_remove_visible_faces_from_p(he_l_hull, he_curr_face, v_furthest);

	const he_l_boundary = he_l_opened_hull.filter(
		(he) => he_is_boundary(he)
	);

	const [he_l_final_hull, he_l_faces_added] = he_l_boundary.reduce(
		([he_l_hull, he_l_face_added], he_opposite) =>
			[
				concat_face(
					he_l_hull, 
					[
						he_to_vert(he_l_hull, he_opposite),
						he_from_vert(he_opposite),
						v_furthest
					]
				),
				he_l_face_added.concat(he_last_face_added(he_l_hull))
			]
		,
		[he_l_opened_hull, []]
	);

	/*console.table(he_l_faces_deleted);
	console.table(he_l_faces_added);*/

	/*pour chaque face f_a ajoutée:
		pour chaque face f_s supprimée:
			pour chaque point p_out de outside_set(f_s):
				si p_out est au-dessus de f_a:
					[]*/
	
	/*const v_l_set_per_face_updated = he_l_faces_added.reduce(
		(v_l_set_per_face_temp, he_face_added) => 
			v_l_set_per_face_temp.map(
				(sub_set, index) =>
					he_2_face_index(he_face_added) === index
					? he_l_faces_deleted.reduce(
						(v_l_temp, he_face_deleted) => 
							v_l_temp.concat(
								v_l_set_per_face[he_2_face_index(he_face_deleted)].reduce(
									(v_l_temp_2, v_curr) =>
									{
										return he_is_above_3d_plane(v_curr, he_l_final_hull, he_face_added)
										? v_l_temp_2.concat(v_curr)
										: v_l_temp_2
									}
									,
									[]
								)
							)
						,
						[]
					)
					: sub_set
			)
		,
		v_l_set_per_face
			.concat(new_ordered_int_list(he_l_faces_added.length).map(() => []))
	);*/
	
	/*console.table(he_l_faces_deleted)
	console.table(he_l_faces_added)

	console.table(v_l_set_per_face)
	console.table(v_l_set_per_face_updated)*/
	//console.log(he_is_above_3d_plane_for_deleted(0, he_l_faces_deleted, 0))
}

const quick_hull_3d = (v_vec3_l) =>
{
	// liste de sommets
	// ensemble de points initial
	const v_l_initial_set = new_ordered_int_list(v_vec3_l.length);
	
	// [liste de demi-arêtes, liste de sommets]
	const [he_l_initial_simplex, v_l_initial_set_updated] = get_initial_simplex(v_l_initial_set);

	// liste (indexée par face) de listes de sommets
	const v_l_set_per_face = v_l_initial_set_updated.reduce(
		(v_l_set_per_face_temp, v_curr) =>
		{
			// cherche la demi-arête d'une face pour laquelle le sommet v_curr est visible
			const he_found = he_find_in_face(
				he_l_initial_simplex,
				(he_face) => he_is_above_3d_plane(v_curr, he_l_initial_simplex, he_face)
			);
			return is_defined(he_found)
				? v_l_set_per_face_temp.map(
					(sub_set, index) =>
						he_2_face_index(he_found) === index
						? sub_set.concat(v_curr)
						: sub_set
				)
				: v_l_set_per_face_temp
		},
		new_ordered_int_list(he_nb_faces(he_l_initial_simplex)).map(() => [])
	);

	quick_hull_3d_2(he_l_initial_simplex, v_l_set_per_face);

	//console.table(he_l_initial_simplex)

	return he_l_initial_simplex;
}