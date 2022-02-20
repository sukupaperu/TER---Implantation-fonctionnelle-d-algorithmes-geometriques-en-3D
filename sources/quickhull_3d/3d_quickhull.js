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

	GLOBAL_DISP.push_furthest_point_state(v_d);
	
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

	// construction du tétrahèdre
	const tetrahedron =
		add_face_from_vertex_index_list(
			add_face_from_vertex_index_list(
				add_face_from_vertex_index_list(
					add_face_from_vertex_index_list(
						new_empty_dcel(), face_base_abc), face_A), face_B), face_C)
	;

	const final_outside_set = updated_outside_set.reduce(
		(constructed_oset, current_vertex) => {

			const he_found = find_among_face(tetrahedron,
				(he_from_current_face) => vertex_is_above_plane(current_vertex, tetrahedron, he_from_current_face)
			);
			
			return is_defined(he_found)
				? add_in_oset(constructed_oset, face_index_from_he(he_found), current_vertex)
				: constructed_oset
			;
		},
		new_empty_oset()
			.concat(new_empty_osubset(0))
			.concat(new_empty_osubset(1))
			.concat(new_empty_osubset(2))
			.concat(new_empty_osubset(3))
	);

	return [
		tetrahedron,
		// on retourne également l'ensemble de points encore à l'extérieur du tétrahèdre
		remove_empty_osubset(final_outside_set)
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

		//const oppo_he = current_hull[oppo_he_index];
		const oppo_he = get_he_by_he_index(current_hull, oppo_he_index);

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

const l1 = [], l2 = [];
const quick_hull_3d_2 = (current_hull, outside_set) =>
{
	const current_subset = first_osubset(outside_set);

	if(!is_defined(current_subset))
		return current_hull;

	l1.push(outside_set.map((x) => x.list.length).length)
	l2.push(outside_set.reduce((x,y) => x + y.list.length, 0))

	const he_of_current_face = he_by_face_index(current_hull, osubset_face_index(current_subset));

	const furthest_vertex = osubset_element_list(current_subset).reduce(
		first_arg_if_true(
			(vertex_a, vertex_b) => 
				signed_dist_between_vertex_and_plane(vertex_a, current_hull, he_of_current_face)
				> signed_dist_between_vertex_and_plane(vertex_b, current_hull, he_of_current_face)
		)
	);

	GLOBAL_DISP.push_furthest_point_state(furthest_vertex);
	
	const [opened_hull, removed_face_list] = remove_visible_faces_from_vertex(current_hull, he_of_current_face, furthest_vertex);
	
	const boundary_he_list = opened_hull.he_list.filter(
		(he) => he_is_boundary(he)
	);

	const [final_hull, added_face_list] = boundary_he_list.reduce(
		([current_hull, constructed_added_face_list], current_he_opposite) => {
			const updated_hull = add_face_from_three_vertex_indices(
				current_hull,
				destination_vertex_index_of_he(current_hull, current_he_opposite),
				source_vertex_index_of_he(current_he_opposite),
				furthest_vertex
			);

			return [
				updated_hull,
				constructed_added_face_list.concat(last_he_added(updated_hull))
			]
		},
		[opened_hull, new_empty_list()]
	);

	GLOBAL_DISP.push_convex_hull_state(final_hull);

	const updated_outside_set = remove_in_oset(outside_set, furthest_vertex);

	const [l,r] = added_face_list.reduce(
		([outside_set_0, added_outside_set_0], current_added_he) => {

			const [outside_set_1, removed_from_outside_set] = filter_and_part_oset(
				outside_set_0,
				(current_face_index) =>
					!is_defined(removed_face_list.find(
						(current_removed_he) =>
							face_index_from_he(current_removed_he)
							=== current_face_index
					))
						? () => true
						: (vertex_to_test) =>
							!vertex_is_above_plane(vertex_to_test, final_hull, current_added_he)
			);

			return [
				outside_set_1,
				add_osubset(added_outside_set_0,
					new_osubset(face_index_from_he(current_added_he), removed_from_outside_set)
				)
			];
		}
		,
		[updated_outside_set, new_empty_oset()]
	);

	let ll = remove_empty_osubset(l).filter(
		(current_subset) =>
			!is_defined(
				removed_face_list.find(
					(current_removed_he) =>
						face_index_from_he(current_removed_he)
						=== osubset_face_index(current_subset)
				)
			)
	);

	let rr = remove_empty_osubset(r);

	let w = ll.concat(rr)

	return quick_hull_3d_2(final_hull, w)
}

const quick_hull_3d = (vec3_list) =>
{
	// liste de sommets
	// ensemble de points initial
	const initial_set = new_ordered_int_list(list_length(vec3_list));
	
	// [dcel, vertex list]
	const [initial_hull, outside_set] = get_initial_hull(initial_set);

	GLOBAL_DISP.push_convex_hull_state(initial_hull);

	const final_hull = quick_hull_3d_2(initial_hull, outside_set);

	return final_hull === undefined ? initial_hull : final_hull;
	//return initial_hull;
}