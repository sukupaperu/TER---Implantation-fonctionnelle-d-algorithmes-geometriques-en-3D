"use strict";

// ### osubset ###
// --- Constructeurs ---

	// int -> int list -> osubset
	const new_osubset = (face_index, vertex_list) =>
		({
			face_index: face_index,
			list: vertex_list
		})
	;

	// int -> osubset
	const new_empty_osubset = (face_index) =>
		new_osubset(face_index, new_empty_list())
	;

	// osubset -> int list -> osubset
	const set_osubset_vertex_list = (osubset, list) =>
		new_osubset(osubset_face_index(osubset), list)
	;

// --- Accesseurs ---

	// osubset -> int
	const osubset_face_index = (osubset) =>
		osubset.face_index
	;

	// osubset -> int list
	const osubset_vertex_list = (osubset) =>
		osubset.list
	;

// --- Modificateurs---

	// osubset -> int -> osubset
	const add_in_osubset = (osubset, vertex) =>
		set_osubset_vertex_list(osubset, osubset_vertex_list(osubset).concat(vertex))
	;



// ### oset ###
// --- Constructeurs ---

	// oset = osubset list
	// () -> oset
	const new_empty_oset = () =>
		new_empty_list()
	;

// --- Accesseurs ---

	// oset -> osubset
	const first_osubset = (oset) =>
		value_in_list_by_index(oset, 0)
	;

	const biggest_osubet = (oset) =>
		is_defined(oset[0])
		? oset.reduce(
				first_arg_if_true(
					(x,y) =>
						osubset_vertex_list(x).length
						> osubset_vertex_list(y).length
				)
			)
		: undefined
	;

// --- Modificateurs ---

	// oset -> osubset -> oset
	const add_osubset = (oset, osubset) =>
		oset.concat(osubset)
	;

	// oset -> int -> oset
	const add_empty_osubset = (oset, face_index) =>
		add_osubset(oset, new_empty_osubset(face_index))
	;

	// oset -> oset
	const remove_empty_osubset = (oset) =>
		oset.filter(
			(current_osubset) => is_defined(value_in_list_by_index(osubset_vertex_list(current_osubset), 0))
		)
	;

	// oset -> he -> int -> oset
	const add_vertex_in_oset = (oset, incident_he_of_face, vertex) =>
		oset.map(
			(current_osubset) =>
				osubset_face_index(current_osubset)
				=== face_index_from_he(incident_he_of_face)
					? add_in_osubset(current_osubset, vertex)
					: current_osubset
		)
	;

	// oset -> int -> oset
	const remove_in_oset = (oset, vertex) =>
		oset.map(
			(current_osubset) =>
				set_osubset_vertex_list(
					current_osubset,
					osubset_vertex_list(current_osubset).filter(
						(current_vertex) => current_vertex !== vertex
					)
				)
		)
	;

// --- Opérations haut-niveau ---
	const filter_oset_and_get_removed_list = (oset, predicate) =>
		oset.reduce(
			([reduced_oset, list_of_removed_vertices], current_osubset) =>
				predicate(osubset_face_index(current_osubset))
					? [
						add_osubset(reduced_oset, current_osubset),
						list_of_removed_vertices
					]
					: [
						reduced_oset,
						list_of_removed_vertices.concat(
							osubset_vertex_list(current_osubset)
						)
					]
			,
			[new_empty_oset(), new_empty_list()]
		)
	;