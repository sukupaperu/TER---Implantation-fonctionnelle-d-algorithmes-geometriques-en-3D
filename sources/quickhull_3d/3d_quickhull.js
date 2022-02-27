"use strict";

// int list -> (int, int)
const get_min_max = (vertex_list) =>
{
	const [min_max_x, min_max_y, min_max_z] = vertex_list.reduce(
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

// int list -> (dcel, oset)
const get_initial_hull = (vertex_list) =>
{
	// deux sommets les plus éloignés
	const [v_a, v_b] = get_min_max(vertex_list);
	
	// sommet c, le plus éloigné du segment ab
	const v_c = vertex_list.reduce(
		first_arg_if_true(
			(kept_vertex, current_vertex) =>
				dist_from_3d_segment(kept_vertex, v_a, v_b)
				> dist_from_3d_segment(current_vertex, v_a, v_b)
		)
	);
	
	// sommet d, le plus éloigné du plan formé par le triangle abc
	const v_d = vertex_list.reduce(
		first_arg_if_true(
			(kept_vertex, current_vertex) =>
				absolute_dist_from_plane(kept_vertex, v_a, v_b, v_c)
				> absolute_dist_from_plane(current_vertex, v_a, v_b, v_c)
		)
	);

	GLOBAL_DISP.push_furthest_point_state(v_d);

	// construction du tétrahèdre
	const tetrahedron_hull =
		vertex_is_above_plane(v_d, v_a, v_b, v_c)
			?	add_face(
				add_face(
				add_face(
				add_face(
					new_empty_dcel(),
				v_a, v_c, v_b),
				v_b, v_c, v_d),
				v_c, v_a, v_d),
				v_a, v_b, v_d)
			:	add_face(
				add_face(
				add_face(
				add_face(
					new_empty_dcel(),
				v_a, v_b, v_c),
				v_c, v_b, v_d),
				v_b, v_a, v_d),
				v_a, v_c, v_d)
	;

	// calcul des sous-ensemble de points extérieurs pour chaque face du tétrahèdre
	const outside_set = vertex_list.filter(
		(v_curr) =>
			v_curr !== v_a
			&& v_curr !== v_b
			&& v_curr !== v_c
			&& v_curr !== v_d
	).reduce(
		(outside_set, current_vertex) =>
		{
			const he_found = find_among_dcel_faces(tetrahedron_hull,
				(incident_he_of_face) =>
					vertex_is_above_face_plane(current_vertex, tetrahedron_hull, incident_he_of_face)
			);
			
			return he_is_null(he_found)
				? outside_set
				: add_vertex_in_oset(outside_set, he_found, current_vertex)
			;
		}
		,
		add_empty_osubset(add_empty_osubset(add_empty_osubset(add_empty_osubset(
			new_empty_oset(), 0), 1), 2), 3)
	);

	return [
		tetrahedron_hull,
		remove_empty_osubset(outside_set)
	];
}

// dcel -> he -> int -> (dcel, int list)
const remove_visible_faces_from_vertex = (hull, source_incident_he, tested_vertex) =>
{
	// (dcel, int list) -> he -> (dcel, int list)
	const remove_visible_faces2 = ([current_hull, deleted_he_list], previous_incident_he) =>
	{
		if(he_is_boundary(previous_incident_he))
			return [current_hull, deleted_he_list];	    

		const oppo_he = get_he_by_he_index(
			current_hull,
			opposite_he_index(previous_incident_he)
		);

		if(he_is_null(oppo_he))
			return [current_hull, deleted_he_list];

		if(!vertex_is_above_face_plane(tested_vertex, current_hull, oppo_he))
			return [current_hull, deleted_he_list];

		const updated_hull = remove_face(current_hull, oppo_he);
		const updated_deleted_he_list = deleted_he_list.concat(face_index_from_he(oppo_he));
		const curr_res = [updated_hull, updated_deleted_he_list];

		const left_res = remove_visible_faces2(curr_res, previous_he(current_hull, oppo_he));
		const right_res = remove_visible_faces2(left_res, next_he(current_hull, oppo_he));

		return right_res;
	}

	const updated_hull = remove_face(hull, source_incident_he);
	const new_deleted_he_list = new_empty_list().concat(face_index_from_he(source_incident_he));
	const curr_res = [updated_hull, new_deleted_he_list];

	const middle_res = remove_visible_faces2(curr_res, source_incident_he);
	const left_res = remove_visible_faces2(middle_res, previous_he(hull, source_incident_he));
	const right_res = remove_visible_faces2(left_res, next_he(hull, source_incident_he));

	return right_res;
}

const quick_hull_3d_2 = (current_hull, outside_set) =>
{
	const current_subset = first_osubset(outside_set);

	if(!is_defined(current_subset))
		return current_hull;

	const he_of_current_face = he_by_face_index(current_hull, osubset_face_index(current_subset));

	const furthest_vertex = osubset_vertex_list(current_subset).reduce(
		first_arg_if_true(
			(vertex_a, vertex_b) => 
				signed_dist_from_face_plane(vertex_a, current_hull, he_of_current_face)
				> signed_dist_from_face_plane(vertex_b, current_hull, he_of_current_face)
		)
	);

	GLOBAL_DISP.push_furthest_point_state(furthest_vertex);
	
	const [opened_hull, removed_face_list] = remove_visible_faces_from_vertex(current_hull, he_of_current_face, furthest_vertex);
	
	const boundary_he_list = opened_hull.he_list.filter(
		(he) => he_is_boundary(he)
	);

	const [final_hull, added_face_list] = boundary_he_list.reduce(
		([current_hull, constructed_added_face_list], current_he_opposite) => {
			const updated_hull = add_face(
				current_hull,
				destination_vertex_of_he(current_hull, current_he_opposite),
				source_vertex_of_he(current_he_opposite),
				furthest_vertex
			);

			return [
				updated_hull,
				constructed_added_face_list.concat(
					face_index_from_he(last_he_added(updated_hull))
				)
			]
		},
		[opened_hull, new_empty_list()]
	);

	GLOBAL_DISP.push_convex_hull_state(final_hull);

	const updated_outside_set = remove_in_oset(outside_set, furthest_vertex);

	const [updated_outside_set_1, untreated_set] = 
		filter_oset_and_get_removed_list(
			updated_outside_set,
			(osubset_face_index) =>
				!is_defined(removed_face_list.find(
					(removed_face_index) => removed_face_index === osubset_face_index
				))
		);
	;

	const oset_temp = added_face_list.reduce(
			(constructed_oset, added_face_index) =>
				add_empty_osubset(constructed_oset, added_face_index),
			new_empty_oset()
		)
	;

	const final_final_outside_set = 
		untreated_set.reduce(
			(constructed_oset, current_vertex) =>
			{
				const face_index_found = added_face_list.find(
					(added_face) => vertex_is_above_face_plane(
						current_vertex,
						final_hull,
						he_by_face_index(final_hull, added_face)
					)
				);
				
				return is_defined(face_index_found)
					? add_vertex_in_oset(
						constructed_oset,
						he_by_face_index(final_hull, face_index_found), 
						current_vertex
					)
					: constructed_oset
				;
			},
			oset_temp
		)
	;

	const w = remove_empty_osubset(updated_outside_set_1.concat(final_final_outside_set));

	return quick_hull_3d_2(final_hull, w)
}

const quick_hull_3d = (vec3_list) =>
{
	// liste de tous les sommets
	const vertex_list = new_ordered_int_list(list_length(vec3_list));
	
	// [dcel, vertex list]
	const [initial_hull, outside_set] = get_initial_hull(vertex_list);

	GLOBAL_DISP.push_convex_hull_state(initial_hull);

	const final_hull = quick_hull_3d_2(initial_hull, outside_set);

	return final_hull === undefined ? initial_hull : final_hull;
}