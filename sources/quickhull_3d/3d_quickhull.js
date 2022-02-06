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
	const explore_and_remove_2 = ([he_l, he_l_deleted], he_opposite, p) =>
	{
		if(he_opposite == -1)
		    return [he_l, he_l_deleted];

		const he = he_l[he_opposite];

		if(he_is_null(he))
			return [he_l, he_l_deleted];

		if(!he_is_above_3d_plane(p, he_l, he))
			return [he_l, he_l_deleted];

		const he_left_opposite_index = he_opposite_index(he_prev(he_l, he));
		const he_right_opposite_index = he_opposite_index(he_next(he_l, he));

			const new_he_l = remove_face(he_l, he);
			const he_l_deleted_updated = he_l_deleted.concat(he);
		const left_res = explore_and_remove_2([new_he_l, he_l_deleted_updated], he_left_opposite_index, p);

		const right_res = explore_and_remove_2(left_res, he_right_opposite_index, p);

		return right_res;
	}

	const he_left_opposite_index = he_opposite_index(he_prev(he_l, he));
	const he_right_opposite_index = he_opposite_index(he_next(he_l, he));

	const new_he_l = remove_face(he_l, he);
	const he_l_deleted = [].concat(he);

	const middle_res = explore_and_remove_2([new_he_l, he_l_deleted], he_opposite_index(he), p);

	const left_res = explore_and_remove_2(middle_res, he_left_opposite_index, p);

	const right_res = explore_and_remove_2(left_res, he_right_opposite_index, p);

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
			const result = get_outside_point_of_face_based_on_condition(v_l_set_per_face_updated, he_2_face_index(curr_he_face_deleted), condition);
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
				(vertex_to_test) => !he_is_above_3d_plane(vertex_to_test, he_l, curr_he_face_added)	
			);
			const curr = he_2_face_index(curr_he_face_added);
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
				v_l_set_per_face_updated[he_2_face_index(curr_he_face_deleted)] = [];
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
		{
			const l = concat_face(
				he_l_hull, 
				[
					he_to_vert(he_l_hull, he_opposite),
					he_from_vert(he_opposite),
					v_furthest
				]
			);
			return [
				l,
				he_l_face_added.concat(he_last_face_added(l))
			]
		}
		,
		[he_l_opened_hull, []]
	);

	/*console.log("deleted:")
	console.table(he_l_faces_deleted.map((x)=>he_2_face_index(x)));
	console.table(he_l_faces_deleted);
	console.log("added:")
	console.table(he_l_faces_added.map((x)=>he_2_face_index(x)));
	console.table(he_l_faces_added);
	console.log("set per face:")
	console.table(v_l_set_per_face)*/
	//console.warn("next");

	const v_l_set_per_face_updated = remove_curr_v_furthest(v_l_set_per_face, v_furthest);
			
	/*let m = get_outside_point_of_face_based_on_condition(v_l_set_per_face, 3, (v) => Math.random()>.5)
	console.table(m[0])
	console.table(m[1])*/
	/*let m = get_outside_points_of_current_face(he_l_faces_deleted, v_l_set_per_face, (v) => Math.random()<.0);
	console.table(m[0])
	console.table(m[1])*/
	let r = reconstruct(he_l_final_hull, he_l_faces_added, he_l_faces_deleted, v_l_set_per_face_updated);
	
	/*console.log(v_l_set_per_face.reduce((x,y)=>x+y.length,0), r.reduce((x,y)=>x+y.length,0))
	console.table(he_l_final_hull)
	console.table(r)*/

	return quick_hull_3d_2(he_l_final_hull, r)
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

	const res = quick_hull_3d_2(he_l_initial_simplex, v_l_set_per_face);

	//console.table(he_l_initial_simplex)

	return res === undefined ? he_l_initial_simplex : res;
}