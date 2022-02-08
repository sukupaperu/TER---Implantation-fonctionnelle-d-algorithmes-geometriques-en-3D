"use strict";

// int list -> (int, int)
const get_min_max = (vertex_index_list) =>
{
	const [min_max_x, min_max_y, min_max_z] = vertex_index_list.reduce(
			(res, vert) =>
				{
					const curr_vert = V(vert);
					return [
						[
							curr_vert.x < V(res[0][0]).x ? vert : res[0][0],
							curr_vert.x > V(res[0][1]).x ? vert : res[0][1]
						],
						[
							curr_vert.y < V(res[1][0]).y ? vert : res[1][0],
							curr_vert.y > V(res[1][1]).y ? vert : res[1][1]
						],
						[
							curr_vert.z < V(res[2][0]).z ? vert : res[2][0],
							curr_vert.z > V(res[2][1]).z ? vert : res[2][1]
						]
					];
				}
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

// int list -> (dcel, int list)
const get_initial_hull = (outside_set) =>
{
	// liste de sommets du segment ab
	const edge_ab = get_min_max(outside_set);
	
	// sommet c, le plus éloigné du segment ab parmi 'outside_set'
	const v_c = outside_set.reduce(
		first_arg_if_true(
			(vertex_index_kept, vertex_index_to_test) =>
				dist_from_3d_segment(vertex_index_kept, edge_ab)
				> dist_from_3d_segment(vertex_index_to_test, edge_ab)
		)
	);
	
	// liste de sommets du triangle abc
	const tri_abc = edge_ab.concat(v_c);
	
	// sommet d, le plus éloigné du plan formé par le triangle abc
	const v_d = outside_set.reduce(
		first_arg_if_true(
			(vertex_index_kept, vertex_index_to_test) =>
				dist_from_3d_plane(vertex_index_kept, tri_abc)
				> dist_from_3d_plane(vertex_index_to_test, tri_abc)
		)
	);
	
	// liste d'indices de sommets
	// la liste (triangle abc) est réordonnée pour correctement orienter la face
	const face_base_abc = 
		is_above_3d_plane(v_d, tri_abc)
			? [tri_abc[0], tri_abc[2], tri_abc[1]]
			: tri_abc
	;
	// listes d'indices de sommets
	// on construit les autres faces (listes d'indices de sommets)
	const face_A = [face_base_abc[2], face_base_abc[1], v_d];
	const face_B = [face_base_abc[1], face_base_abc[0], v_d];
	const face_C = [face_base_abc[0], face_base_abc[2], v_d];
	
	// liste d'indicaes de sommets du tétrahèdre abcd
	const tetrahedron_abcd = tri_abc.concat(v_d);

	// liste d'indices de sommets
	// ensemble de sommets 'outside_set' mais sans les sommets du tétrahèdre abcd
	const updated_outside_set = outside_set.filter(
		(v_curr) =>
			!is_defined(tetrahedron_abcd.find(
				(v_tetrahedron) => v_tetrahedron === v_curr
			))
	);

	return [
		// construction du tétrahèdre
		add_face_from_vertex_index_list(add_face_from_vertex_index_list(add_face_from_vertex_index_list(add_face_from_vertex_index_list([], face_base_abc), face_A), face_B), face_C),
		// on retourne également l'ensemble de points encore à l'extérieur du tétrahèdre
		updated_outside_set
	];
}

// dcel -> he -> int -> (dcel, he list)
const remove_visible_faces_from_vertex = (hull, source_incident_he, tested_vertex) =>
{
	// (dcel, he list) -> he ->  -> (dcel, he list)
	const remove_visible_faces2 = ([current_hull, deleted_he_list], previous_incident_he) =>
	{
		const oppo_he_index = opposite_he_index(previous_incident_he);

		if(oppo_he_index == -1)
		    return [current_hull, deleted_he_list];

		const oppo_he = current_hull[oppo_he_index];

		if(he_is_null(oppo_he))
			return [current_hull, deleted_he_list];

		if(!vertex_is_above_plane(tested_vertex, current_hull, oppo_he))
			return [current_hull, deleted_he_list];

		const updated_hull = remove_face(current_hull, oppo_he);
		const updated_deleted_he_list = deleted_he_list.concat(oppo_he);
		const curr_res = [updated_hull, updated_deleted_he_list];

		const left_res = remove_visible_faces2(curr_res, previous_he(current_hull, oppo_he));
		const right_res = remove_visible_faces2(left_res, next_he(current_hull, oppo_he));

		return right_res;
	}

	const updated_hull = remove_face(hull, source_incident_he);
	const new_deleted_he_list = new_empty_list().concat(source_incident_he);
	const curr_res = [updated_hull, new_deleted_he_list];

	const middle_res = remove_visible_faces2(curr_res, source_incident_he);
	const left_res = remove_visible_faces2(middle_res, previous_he(hull, source_incident_he));
	const right_res = remove_visible_faces2(left_res, next_he(hull, source_incident_he));

	return right_res;
}

const get_outside_point_of_face_based_on_condition = (v_l_set_per_face, face_index, condition) =>
{
	return v_l_set_per_face.reduce(
		([v_l_set_per_face_updated, set_detected], curr_outside_set, curr_face_index) =>
			{
				if(curr_face_index !== face_index)
					return [v_l_set_per_face_updated.concat([curr_outside_set]), set_detected]
				const result = curr_outside_set.reduce(
					([curr_outside_set_updated, set_detected], vertex) =>
					{
						return condition(vertex)
						? [curr_outside_set_updated.concat(vertex), set_detected]
						: [curr_outside_set_updated, set_detected.concat(vertex)]
					}
						
					,
					[[],[]]
				);
				return [
					v_l_set_per_face_updated.concat([result[0]]),
					set_detected.concat(result[1])
				];
			}
		,
		[[],[]]
	);
}

const get_outside_points_of_current_face = (he_l_faces_deleted, v_l_set_per_face, condition) =>
{
	return he_l_faces_deleted.reduce(
		([v_l_set_per_face_updated, set_detected], curr_he_face_deleted) => 
		{
			//console.log(curr_he_face_deleted, he_2_face_index(curr_he_face_deleted))
			const result = get_outside_point_of_face_based_on_condition(v_l_set_per_face_updated, face_index_from_he(curr_he_face_deleted), condition);
			return [result[0], set_detected.concat(result[1])];
		}
		,
		[v_l_set_per_face, []]
	);
}

const reconstruct = (he_l, he_l_faces_added, he_l_faces_deleted, v_l_set_per_face) =>
{
	const result = he_l_faces_added.reduce(
		(v_l_set_per_face_updated, curr_he_face_added) =>
		{
			const result = get_outside_points_of_current_face(
				he_l_faces_deleted,
				v_l_set_per_face_updated,
				(vertex_to_test) => !vertex_is_above_plane(vertex_to_test, he_l, curr_he_face_added)	
			);
			const curr = face_index_from_he(curr_he_face_added);
			//console.log(curr, result[1]);
			result[0][curr] = result[0][curr].concat(result[1])
			return result[0];
		}
		,
		v_l_set_per_face
			.concat(new_ordered_int_list(he_l_faces_added.length).map(() => []))
	);

	let mmm = he_l_faces_deleted.reduce(
		(v_l_set_per_face_updated, curr_he_face_deleted) =>
			{
				v_l_set_per_face_updated[face_index_from_he(curr_he_face_deleted)] = [];
				return v_l_set_per_face_updated;
			}
		,
		result
	)

	return mmm;
}

const remove_curr_v_furthest = (v_l_set_per_face, v_furthest) =>
{
	return v_l_set_per_face.map(
		(v_l_set_local) =>
			v_l_set_local.reduce(
				(v_l_set_local_updated, v_curr) =>
					v_curr === v_furthest
						? v_l_set_local_updated
						: v_l_set_local_updated.concat(v_curr)
				,
				[]
			)
	);
};

const quick_hull_3d_2 = (current_hull, set_per_face) =>
{
	const he_face_index_found = set_per_face.findIndex(
		(v_l_subset) => !list_is_empty(v_l_subset)
	);

	if(he_face_index_found === -1)
		return current_hull;

	const v_l_curr_set = set_per_face[he_face_index_found];
	const he_curr_face = he_by_face_index(current_hull, he_face_index_found);
	
	const v_furthest = v_l_curr_set.reduce(
		first_arg_if_true(
			(v_a, v_b) =>
				signed_dist_between_vertex_and_plane(v_a, current_hull, he_curr_face)
				> signed_dist_between_vertex_and_plane(v_b, current_hull, he_curr_face)
		)
	);

	GLOBAL_DISP.push_furthest_point_state(v_furthest);
	
	const [he_l_opened_hull, he_l_faces_deleted] = remove_visible_faces_from_vertex(current_hull, he_curr_face, v_furthest);

	const he_l_boundary = he_l_opened_hull.filter(
		(he) => he_is_boundary(he)
	);

	const [he_l_final_hull, he_l_faces_added] = he_l_boundary.reduce(
		([current_hull, he_l_face_added], he_opposite) =>
		{
			const l = add_face_from_vertex_index_list(
				current_hull, 
				[
					destination_vertex_index_of_he(current_hull, he_opposite),
					source_vertex_index_of_he(he_opposite),
					v_furthest
				]
			);
			return [
				l,
				he_l_face_added.concat(last_he_added(l))
			]
		}
		,
		[he_l_opened_hull, []]
	);

	GLOBAL_DISP.push_convex_hull_state(he_l_final_hull);

	const set_per_face_updated = remove_curr_v_furthest(set_per_face, v_furthest);

	let r = reconstruct(he_l_final_hull, he_l_faces_added, he_l_faces_deleted, set_per_face_updated);

	return quick_hull_3d_2(he_l_final_hull, r)
}

const quick_hull_3d = (vec3_list) =>
{
	// liste de sommets
	// ensemble de points initial
	const initial_set = new_ordered_int_list(list_length(vec3_list));
	
	// [dcel, vertex list]
	const [initial_hull, initial_set_updated] = get_initial_hull(initial_set);

	GLOBAL_DISP.push_convex_hull_state(initial_hull);

	// liste (indexée par face) de listes de sommets
	const v_l_set_per_face = initial_set_updated.reduce(
		(v_l_set_per_face_temp, v_curr) =>
		{
			// cherche la demi-arête d'une face pour laquelle le sommet v_curr est visible
			const he_found = initial_hull.find(
				(he_face) => vertex_is_above_plane(v_curr, initial_hull, he_face)
			);
			return is_defined(he_found)
				? v_l_set_per_face_temp.map(
					(sub_set, index) =>
						face_index_from_he(he_found) === index
						? sub_set.concat(v_curr)
						: sub_set
				)
				: v_l_set_per_face_temp
		},
		[[],[],[],[]]
	);

	const final_hull = quick_hull_3d_2(initial_hull, v_l_set_per_face);

	return final_hull === undefined ? initial_hull : final_hull;
}