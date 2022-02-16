"use strict";

// he : half-edge ; demi-arête
// dcel : doubly connected edge list ; liste particulière de he

// --- Constructeurs ---

	// int -> int -> int -> int -> he
	const new_he = (he_index, next_he_index, opposite_he_index, source_vertex_index) => 
	({
		index: he_index, 			// indice de 'he' dans sa 'dcel'
		next: next_he_index,		// indice de l'arête suivante dans sa 'dcel'
		opposite: opposite_he_index,// indice de l'arête opposée dans sa 'dcel'
		vert: source_vertex_index	// indice du sommet source dans sa 'vertex_list'
	});

	// () -> he
	const new_null_he = () =>
		new_he(-1, -1, -1, -1)
	;

	// he -> int -> he
	const set_he_opposite = (he, new_opposite_index) =>
		new_he(he.index, he.next, new_opposite_index, he.vert)
	;

	// he -> he
	const set_he_to_boundary_he = (he) =>
		set_he_opposite(he, -1)
	;

	// () -> dcel
	const new_empty_dcel = () =>
		new_empty_list()
	;

// --- Accesseurs ---

	// he -> int
	const he_index = (he) =>
		he.index
	;

	// he -> int
	const next_he_index = (he) =>
		he.next
	;

	// he -> int
	const opposite_he_index = (he) =>
		he.opposite
	;

	// he -> int
	const source_vertex_index_of_he = (he) =>
		he.vert
	;

	// dcel -> he -> int
	const destination_vertex_index_of_he = (dcel, he) =>
		source_vertex_index_of_he(next_he(dcel, he))
	;

	// dcel -> int -> he
	const get_he_by_he_index = (dcel, he_index_to_find) =>
		{
			const res = dcel.find((he) => he_index(he) === he_index_to_find);
			return is_defined(res) ? res : new_null_he();
		}	
	;

// --- Propriétés ---

	// he -> bool
	const he_is_null = (he) =>
		he_index(he) === -1
	;

	// he -> bool
	const he_is_boundary = (he) =>//!he_is_null(he) && 
		opposite_he_index(he) === -1
	;
	
	// dcel -> int
	const n_faces_in_dcel = (dcel) =>
		dcel.reduce(
			(acc, he) => //acc + (he_is_null(he) ? 0 : 1),
				acc + (he_is_null(he) ? 0 : 1),
			0
		)/3
	;

// --- Accesseurs avancés ---

	// dcel -> he -> he
	const opposite_he = (dcel, he) =>
		get_he_by_he_index(dcel, opposite_he_index(he))
		//value_in_list_by_index(dcel, opposite_he_index(he))
	;

	// dcel -> he -> he
	const next_he = (dcel, he) =>
		get_he_by_he_index(dcel, next_he_index(he))
		//value_in_list_by_index(dcel, next_he_index(he))
	;

	// dcel -> he -> he
	const previous_he = (dcel, he) =>
		next_he(dcel, next_he(dcel, he))
	;

	// dcel -> int -> he
	const he_by_face_index = (dcel, face_index) =>
		get_he_by_he_index(dcel, face_index*3)
		//value_in_list_by_index(dcel, face_index*3)
	;

	// dcel -> he -> int list
	const vertex_index_list_from_face = (dcel, he) =>
		new_empty_list()
		.concat(source_vertex_index_of_he(he))
		.concat(destination_vertex_index_of_he(dcel, he))
		.concat(destination_vertex_index_of_he(dcel, next_he(dcel, he)))
	;

	// he -> int
	const face_index_from_he = (he) =>
		Math.floor(he_index(he)/3);

	// dcel -> he
	const last_he_added = (dcel) =>
		value_in_list_by_index(dcel, list_length(dcel) - 1);

	// decl -> int
	const next_new_he_index = (dcel) => 
		{
			const last_he = last_he_added(dcel);
			return is_defined(last_he)
				? he_index(last_he) + 1
				: 0
		}
	;

// --- Opérations haut niveau pour dcel ---

	// dcel -> int -> int -> int -> dcel
	const add_face_from_three_vertex_indices = (dcel, vert_A, vert_B, vert_C) =>
	{
		GLOBAL_DISP.push_convex_hull_state(dcel);

		const he_number = next_new_he_index(dcel);

		const he_AB_index = he_number;
		const he_BC_index = he_number + 1;
		const he_CA_index = he_number + 2;

		// dcel -> int -> int -> int
		const look_up_for_opposite_he_index = (dcel, src_vert_index, dest_vert_index) =>
			{
				const res = dcel.find(
					(he) =>
						source_vertex_index_of_he(he) === dest_vert_index
						&& destination_vertex_index_of_he(dcel, he) === src_vert_index
				);
				return is_defined(res) ? he_index(res) : -1;
			}
		/*look_up_index_in_list(
				dcel, 
				(he) =>
					source_vertex_index_of_he(he) === dest_vert_index
					&& destination_vertex_index_of_he(dcel, he) === src_vert_index
			)*/
		;

		const he_AB_opposite_index = look_up_for_opposite_he_index(dcel, vert_A, vert_B);
		const he_BC_opposite_index = look_up_for_opposite_he_index(dcel, vert_B, vert_C);
		const he_CA_opposite_index = look_up_for_opposite_he_index(dcel, vert_C, vert_A);

		const final_dcel = dcel
			.map((current_he) =>
			{
				switch(he_index(current_he))
				{
					case he_AB_opposite_index:
						return set_he_opposite(current_he, he_AB_index);
					case he_BC_opposite_index:
						return set_he_opposite(current_he, he_BC_index);
					case he_CA_opposite_index:
						return set_he_opposite(current_he, he_CA_index);
				}
				return current_he;
			})
			.concat(new_he(he_AB_index, he_BC_index, he_AB_opposite_index, vert_A))
			.concat(new_he(he_BC_index, he_CA_index, he_BC_opposite_index, vert_B))
			.concat(new_he(he_CA_index, he_AB_index, he_CA_opposite_index, vert_C))
		;

		GLOBAL_DISP.push_face_added_state(vertex_index_list_from_face(final_dcel, last_he_added(final_dcel)));

		return final_dcel;
	};

	// dcel -> int list -> dcel
	const add_face_from_vertex_index_list = (dcel, v_index_list) =>
		add_face_from_three_vertex_indices(
			dcel,
			value_in_list_by_index(v_index_list, 0),
			value_in_list_by_index(v_index_list, 1),
			value_in_list_by_index(v_index_list, 2)
		)
	;

	// dcel -> he -> dcel
	const remove_face = (dcel, he) => {

		if(he_is_null(he))
			return dcel;
		
		GLOBAL_DISP.push_face_removed_state(vertex_index_list_from_face(dcel, he));

		const he_A = he;
		const he_B = next_he(dcel, he);
		const he_C = previous_he(dcel, he);

		const he_A_index = he_index(he_A);
		const he_B_index = he_index(he_B);
		const he_C_index = he_index(he_C);

		const he_A_opposite_index = opposite_he_index(he_A);
		const he_B_opposite_index = opposite_he_index(he_B);
		const he_C_opposite_index = opposite_he_index(he_C);

		const final_dcel = dcel
			.reduce(
				(reduced_decl, current_he) => 
				{
					switch(he_index(current_he))
					{
						case he_A_index:
						case he_B_index:
						case he_C_index:
							return reduced_decl;
						case he_A_opposite_index:
						case he_B_opposite_index:
						case he_C_opposite_index:
							return reduced_decl.concat(set_he_to_boundary_he(current_he));
						default:
							return reduced_decl.concat(current_he);
					}
				},
				new_empty_dcel()
			);

		GLOBAL_DISP.push_convex_hull_state(final_dcel);

		return final_dcel;
	};

	// const reduce_on_face = (dcel, reducer, initial_value) =>
	// 	dcel.length === 0
	// 		? initial_value
	// 		: reducer(
	// 			reduce_on_face(dcel.slice(0, -3), reducer, initial_value),
	// 			dcel.slice(-1)[0],
	// 			face_index_from_he(dcel.slice(-1)[0])
	// 		)
	// ;

	const find_among_face = (dcel, predicate) =>
		dcel.length === 0
			? undefined
			: predicate(dcel.slice(-1)[0])
				? dcel.slice(-1)[0]
				: find_among_face(dcel.slice(0, -3), predicate)
	;