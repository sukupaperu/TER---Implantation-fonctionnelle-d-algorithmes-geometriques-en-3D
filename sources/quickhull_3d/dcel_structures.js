"use strict";

// he : half-edge ; demi-arête
// dcel : doubly connected edge list ; liste particulière de he

// --- Constructeurs ---

// int -> int -> int -> int -> he
const new_he = (he_index, opposite_he_index, source_vertex) =>
({
	index: he_index, 			// indice de 'he' dans sa 'dcel'
	opposite: opposite_he_index,// indice de l'arête opposée dans sa 'dcel'
	vertex: source_vertex	// indice du sommet source dans sa 'vertex_list'
});

// () -> he
const new_null_he = () =>
	new_he(-1, 0, 0)
	;

// he -> int -> he
const set_he_opposite = (he, new_opposite_index) =>
	new_he(
		he_index(he),
		new_opposite_index,
		source_vertex_of_he(he)
	)
	;

// he -> he
const set_he_to_boundary_he = (he) =>
	set_he_opposite(he, -1)
	;

// he list -> int -> dcel
const new_dcel = (he_list, available_he_index) =>
({
	he_list: he_list,
	available_he_index: available_he_index
})
	;

// () -> dcel
const new_empty_dcel = () =>
	new_dcel(new_empty_list(), 0)
	;

// --- Accesseurs ---

// he -> int
const he_index = (he) =>
	he.index
	;

// he -> int
const next_he_index = (he) =>
	(he_index(he) - he_index(he) % 3)
	+ (he_index(he) + 1) % 3
	;

// he -> int
const previous_he_index = (he) =>
	(he_index(he) - he_index(he) % 3)
	+ (3 + he_index(he) - 1) % 3
	;

// he -> int
const opposite_he_index = (he) =>
	he.opposite
	;

// he -> int
const source_vertex_of_he = (he) =>
	he.vertex
	;

// dcel -> he -> int
const destination_vertex_of_he = (dcel, he) =>
	source_vertex_of_he(next_he(dcel, he))
	;

// dcel -> int -> he
const get_he_by_he_index = (dcel, he_index_to_find) => {
	const he_found = dcel.he_list.find((he) => he_index(he) === he_index_to_find);
	return is_defined(he_found) ? he_found : new_null_he();
}
	;

// --- Propriétés ---

// he -> bool
const he_is_null = (he) =>
	he_index(he) === -1
	;

// he -> bool
const he_is_boundary = (he) =>
	opposite_he_index(he) === -1
	;

// dcel -> int
const n_faces_in_dcel = (dcel) =>
	dcel.he_list.reduce(
		(acc, he) =>
			acc + (he_is_null(he) ? 0 : 1),
		0
	) / 3
	;

// --- Accesseurs avancés ---

// dcel -> he -> he
const opposite_he = (dcel, he) =>
	get_he_by_he_index(dcel, opposite_he_index(he))
	;

// dcel -> he -> he
const next_he = (dcel, he) =>
	get_he_by_he_index(dcel, next_he_index(he))
	;

// dcel -> he -> he
const previous_he = (dcel, he) =>
	get_he_by_he_index(dcel, previous_he_index(he))
	;

// dcel -> int -> he
const he_by_face_index = (dcel, face_index) =>
	get_he_by_he_index(dcel, face_index * 3)
	;

// dcel -> he -> int list
const vertex_list_from_face = (dcel, he) =>
	new_empty_list()
		.concat(source_vertex_of_he(he))
		.concat(destination_vertex_of_he(dcel, he))
		.concat(destination_vertex_of_he(dcel, next_he(dcel, he)))
	;

// he -> int
const face_index_from_he = (he) =>
	Math.floor(he_index(he) / 3);

// dcel -> he
const last_he_added = (dcel) =>
	value_in_list_by_index(dcel.he_list, list_length(dcel.he_list) - 1);

// --- Opérations haut niveau pour dcel ---

// dcel -> int -> int -> int -> dcel
const add_face = (dcel, vert_A, vert_B, vert_C) => {
	GLOBAL_DISP.push_convex_hull_state(dcel);

	const he_AB_index = dcel.available_he_index;
	const he_BC_index = dcel.available_he_index + 1;
	const he_CA_index = dcel.available_he_index + 2;

	// dcel -> int -> int -> int
	const look_up_for_opposite_he_index = (dcel, src_vert_index, dest_vert_index) => {
		const res = dcel.he_list.find(
			(he) =>
				source_vertex_of_he(he) === dest_vert_index
				&& destination_vertex_of_he(dcel, he) === src_vert_index
		);
		return is_defined(res) ? he_index(res) : -1;
	}
		;

	const he_AB_opposite_index = look_up_for_opposite_he_index(dcel, vert_A, vert_B);
	const he_BC_opposite_index = look_up_for_opposite_he_index(dcel, vert_B, vert_C);
	const he_CA_opposite_index = look_up_for_opposite_he_index(dcel, vert_C, vert_A);

	const final_dcel = new_dcel(
		dcel.he_list.map((current_he) => {
			switch (he_index(current_he)) {
				case he_AB_opposite_index:
					return set_he_opposite(current_he, he_AB_index);
				case he_BC_opposite_index:
					return set_he_opposite(current_he, he_BC_index);
				case he_CA_opposite_index:
					return set_he_opposite(current_he, he_CA_index);
			}
			return current_he;
		})
			.concat(new_he(he_AB_index, he_AB_opposite_index, vert_A))
			.concat(new_he(he_BC_index, he_BC_opposite_index, vert_B))
			.concat(new_he(he_CA_index, he_CA_opposite_index, vert_C))
		,
		dcel.available_he_index + 3
	);

	GLOBAL_DISP.push_face_added_state(vertex_list_from_face(final_dcel, last_he_added(final_dcel)));

	return final_dcel;
};

// dcel -> he -> dcel
const remove_face = (dcel, he) => {

	if (he_is_null(he))
		return dcel;

	GLOBAL_DISP.push_face_removed_state(vertex_list_from_face(dcel, he));

	const he_A = he;
	const he_B = next_he(dcel, he);
	const he_C = previous_he(dcel, he);

	const he_A_index = he_index(he_A);
	const he_B_index = he_index(he_B);
	const he_C_index = he_index(he_C);

	const he_A_opposite_index = opposite_he_index(he_A);
	const he_B_opposite_index = opposite_he_index(he_B);
	const he_C_opposite_index = opposite_he_index(he_C);

	const final_dcel = new_dcel(
		dcel.he_list.reduce(
			(reduced_he_list, current_he) => {
				switch (he_index(current_he)) {
					case he_A_index:
					case he_B_index:
					case he_C_index:
						return reduced_he_list;
					case he_A_opposite_index:
					case he_B_opposite_index:
					case he_C_opposite_index:
						return reduced_he_list.concat(set_he_to_boundary_he(current_he));
					default:
						return reduced_he_list.concat(current_he);
				}
			},
			new_empty_dcel().he_list
		)
		,
		dcel.available_he_index
	);

	GLOBAL_DISP.push_convex_hull_state(final_dcel);

	return final_dcel;
};

const find_among_dcel_faces = (dcel, predicate) => {
	const find_among_dcel_faces_rec = (he_list) =>
		he_list.length === 0
			? new_null_he()
			: predicate(he_list.slice(-1)[0])
				? he_list.slice(-1)[0]
				: find_among_dcel_faces_rec(he_list.slice(0, -3))
		;

	return find_among_dcel_faces_rec(dcel.he_list);
}
	;