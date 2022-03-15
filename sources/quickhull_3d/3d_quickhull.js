"use strict";

// int list -> (int, int)
const get_furthest_min_and_max = (vertex_list) =>
{
	const min_x = vertex_list.reduce(first_arg_if_true((min, v) => V(min).x < V(v).x));
	const max_x = vertex_list.reduce(first_arg_if_true((max, v) => V(max).x > V(v).x));
	const min_y = vertex_list.reduce(first_arg_if_true((min, v) => V(min).y < V(v).y));
	const max_y = vertex_list.reduce(first_arg_if_true((max, v) => V(max).y > V(v).y));
	const min_z = vertex_list.reduce(first_arg_if_true((min, v) => V(min).z < V(v).z));
	const max_z = vertex_list.reduce(first_arg_if_true((max, v) => V(max).z > V(v).z));

	const diff_x = minus3(max_x, min_x);
	const diff_y = minus3(max_y, min_y);
	const diff_z = minus3(max_z, min_z);
	
	return diff_x > diff_y
		? diff_x > diff_z
			? [min_x, max_x]
			: [min_z, max_z]
		: diff_y > diff_z
			? [min_y, max_y]
			: [min_z, max_z]
	;
};

// int list -> (dcel, oset)
const get_initial_hull = (vertex_list_0) =>
{
	// deux sommets les plus éloignés sur les 3 axes
	const [v_a, v_b] = get_furthest_min_and_max(vertex_list_0);
	const vertex_list_1 = vertex_list_0.filter((v_curr) => v_curr !== v_a && v_curr !== v_b);

	// sommet c, le plus éloigné du segment ab
	const v_c = vertex_list_1.reduce(
		first_arg_if_true(
			(kept_vertex, current_vertex) =>
				dist_from_3d_segment(kept_vertex, v_a, v_b)
				> dist_from_3d_segment(current_vertex, v_a, v_b)
		)
	);
	const vertex_list_2 = vertex_list_1.filter((v_curr) => v_curr !== v_c);

	// sommet d, le plus éloigné du plan formé par le triangle abc
	const v_d = vertex_list_2.reduce(
		first_arg_if_true(
			(kept_vertex, current_vertex) =>
				absolute_dist_from_plane(kept_vertex, v_a, v_b, v_c)
				> absolute_dist_from_plane(current_vertex, v_a, v_b, v_c)
		)
	);
	const vertex_list_3 = vertex_list_2.filter((v_curr) => v_curr !== v_d);

	GLOBAL_DISP.push_furthest_point_state(v_d);

	// construction du tétrahèdre
	const tetrahedron_hull =
		// en fonction de quel côté se trouve le sommet d de la face abc
		// l'orientation de cette dernière n'est pas la même
		vertex_is_above_plane(v_d, v_a, v_b, v_c)
			?	add_face(add_face(add_face(add_face(
				new_empty_dcel(),
				v_a, v_c, v_b),
				v_b, v_c, v_d),
				v_c, v_a, v_d),
				v_a, v_b, v_d)
			:	add_face(add_face(add_face(add_face(
				new_empty_dcel(),
				v_a, v_b, v_c),
				v_c, v_b, v_d),
				v_b, v_a, v_d),
				v_a, v_c, v_d)
	;
	
	// calcul des sous-ensemble de points externes pour chaque face du tétrahèdre
	const outside_set = vertex_list_3.reduce(
		(outside_set, current_vertex) =>
		{
			const he_found = find_among_dcel_faces(
				tetrahedron_hull,
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
	const remove_visible_faces2 = ([convex_hull, deleted_he_list], previous_incident_he) =>
	{
		if(he_is_boundary(previous_incident_he))
			return [convex_hull, deleted_he_list];	    

		const oppo_he = get_he_by_he_index(
			convex_hull,
			opposite_he_index(previous_incident_he)
		);

		if(he_is_null(oppo_he))
			return [convex_hull, deleted_he_list];

		if(!vertex_is_above_face_plane(tested_vertex, convex_hull, oppo_he))
			return [convex_hull, deleted_he_list];

		const updated_hull = remove_face(convex_hull, oppo_he);
		const updated_deleted_he_list = deleted_he_list.concat(face_index_from_he(oppo_he));
		const curr_res = [updated_hull, updated_deleted_he_list];

		const left_res = remove_visible_faces2(curr_res, previous_he(convex_hull, oppo_he));
		const right_res = remove_visible_faces2(left_res, next_he(convex_hull, oppo_he));

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

const update_outside_set_for_each_new_faces = (convex_hull, outside_set, added_face_list, removed_face_list) => 
{
	const [updated_outside_set, untreated_vertex_set] = 
		filter_oset_and_get_removed_list(
			outside_set,
			(osubset_face_index) =>
				!is_defined(removed_face_list.find(
					(removed_face_index) => removed_face_index === osubset_face_index
				))
		)
	;

	const newly_created_outside_set = added_face_list.reduce(
			(constructed_outside_set, added_face_index) =>
				add_empty_osubset(constructed_outside_set, added_face_index),
			new_empty_oset()
		)
	;

	const final_outside_set = 
		untreated_vertex_set.reduce(
			(constructed_outside_set, current_vertex) =>
			{
				const face_index_found = added_face_list.find(
					(added_face) => vertex_is_above_face_plane(
						current_vertex,
						convex_hull,
						he_by_face_index(convex_hull, added_face)
					)
				);
				
				return is_defined(face_index_found)
					? add_vertex_in_oset(
						constructed_outside_set,
						he_by_face_index(convex_hull, face_index_found), 
						current_vertex
					)
					: constructed_outside_set
				;
			},
			newly_created_outside_set
		)
	;

	return remove_empty_osubset(
		updated_outside_set.concat(final_outside_set)
	);
}

const recursive_quick_hull_3d = (convex_hull, outside_set) =>
{
	const current_subset = first_osubset(outside_set);
	//const current_subset = biggest_osubet(outside_set);

	// condition de terminaison
	if(!is_defined(current_subset))
		return convex_hull;

	// une arrête qui appartient à la face sélectionnée
	const he_of_current_face = he_by_face_index(convex_hull, osubset_face_index(current_subset));

	// on cherche le point le plus éloigné de la face
	const furthest_vertex = osubset_vertex_list(current_subset).reduce(
		first_arg_if_true(
			(vertex_a, vertex_b) => 
				signed_dist_from_face_plane(vertex_a, convex_hull, he_of_current_face)
				> signed_dist_from_face_plane(vertex_b, convex_hull, he_of_current_face)
		)
	);
	//const furthest_vertex = osubset_vertex_list(current_subset)[0];

	GLOBAL_DISP.push_furthest_point_state(furthest_vertex);
	
	const [opened_hull, removed_face_list] = remove_visible_faces_from_vertex(convex_hull, he_of_current_face, furthest_vertex);
	
	const boundary_he_list = opened_hull.he_list.filter(
		(he) => he_is_boundary(he)
	);

	const [final_hull, added_face_list] = boundary_he_list.reduce(
		([convex_hull, constructed_added_face_list], current_he_opposite) => {
			const updated_hull = add_face(
				convex_hull,
				destination_vertex_of_he(convex_hull, current_he_opposite),
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
	
	// mise à jour de l'ensemble de points externes à l'enveloppe convexe
	const final_outside_set = update_outside_set_for_each_new_faces(
		final_hull,
		remove_in_oset(outside_set, furthest_vertex),
		added_face_list,
		removed_face_list
	);

	return recursive_quick_hull_3d(final_hull, final_outside_set);
}

const quick_hull_3d = (vec3_list) =>
{
	// liste de tous les sommets
	const vertex_list = new_ordered_int_list(list_length(vec3_list));
	
	// on récupère une enveloppe initiale (tétrahèdre) et un ensemble de points externes à ses faces
	const [initial_hull, outside_set] = get_initial_hull(vertex_list);

	GLOBAL_DISP.push_convex_hull_state(initial_hull);

	return recursive_quick_hull_3d(initial_hull, outside_set);
}