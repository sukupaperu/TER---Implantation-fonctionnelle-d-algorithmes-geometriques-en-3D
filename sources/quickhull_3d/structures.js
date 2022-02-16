"use strict";

// ---- Opérations sur les listes ----

	// int -> int list
	const new_ordered_int_list = (n) =>
		n === 0
			? []
			: n === 1
				? [0]
				: new_ordered_int_list(n - 1).concat(n - 1)
	;

	// any list -> (any -> bool) -> int
	const look_up_index_in_list = (list, condition) =>
		list.length === 0
			? -1
			: condition(list[list.length - 1])
				? list.length - 1
				: look_up_index_in_list(list.slice(0, -1), condition)
	;


// ---- Opérations sur les listes (ici volontairement en approche non-fonctionnelles) ----

	// () -> any list
	const new_empty_list = () =>
		[]
	;

	const new_tupple = (left_element, right_element) =>
		[left_element, right_element]
	;	

	// any list -> int
	const list_length = (list) =>
		list.length
	;

	// any list -> int -> any
	const value_in_list_by_index = (list, index) =>
		list[index]
	;

	// any list -> bool
	const list_is_empty = (list) =>
		list_length(list) === 0
	;

	const filter_and_part_list = (list, predicate) =>
		list.reduce(
			([reduced_list, removed_element_list], current_element) =>
				predicate(current_element)
					? [reduced_list.concat(current_element), removed_element_list]
					: [reduced_list, removed_element_list.concat(current_element)]
			,
			[new_empty_list(), new_empty_list()]
		)
	;

// ---- Fonctions diverses ----

	// (any -> any -> bool) -> (any -> any) -> any
	const first_arg_if_true = condition => 
		(a, b) => condition(a, b) ? a : b
	;

	// any -> bool
	const is_defined = (a) =>
		a !== undefined
	;

	const V = (index) =>
		value_in_list_by_index(GLOBAL_V_LIST, index);



const new_osubset = (face_index, element_list) =>
	({
		index: face_index,
		list: element_list
	})
;
const new_empty_osubset = (face_index) =>
	new_osubset(face_index, new_empty_list())
;
const set_osubset_list = (osubset, list) =>
	new_osubset(osubset_face_index(osubset), list)
;

const osubset_face_index = (osubset) =>
	osubset.index
;
const osubset_element_list = (osubset) =>
	osubset.list
;

const add_in_osubset = (osubset, element) =>
	set_osubset_list(osubset, osubset_element_list(osubset).concat(element))
;

const filter_and_part_osubset = (osubset, predicate) =>
	{
		const [reduced_osubset_element_list, removed_element_list] = filter_and_part_list(
			osubset_element_list(osubset),
			predicate
		);
		return [
			set_osubset_list(osubset, reduced_osubset_element_list),
			removed_element_list
		];
	}
;
//console.table(filter_and_part_osubset(add_in_osubset(add_in_osubset(add_in_osubset(new_empty_osubset(5), 4),2),8), (element) => element===2))

const new_empty_oset = () =>
	new_empty_list()
;

const add_osubset = (oset, osubset) =>
	oset.concat(osubset)
;

const filter_and_part_oset = (oset, predicate) =>
	oset.reduce(
		([reduced_oset, main_removed_element_list], current_osubset) => {

			const [updated_current_osubset, removed_element_list] = filter_and_part_osubset(
				current_osubset,
				predicate(osubset_face_index(current_osubset))
			);

			return [
				add_osubset(reduced_oset, updated_current_osubset),
				main_removed_element_list.concat(removed_element_list)
			];
		},
		[new_empty_oset(), new_empty_list()]
	)
;
/*console.table(
filter_and_part_oset(
	new_empty_list().concat(
		add_in_osubset(add_in_osubset(add_in_osubset(new_empty_osubset(5), 4),2),8)
	).concat(
		add_in_osubset(add_in_osubset(add_in_osubset(add_in_osubset(new_empty_osubset(6), 7),13),-2),12)
	),
	(face_index) => (vertex_index) => face_index === vertex_index
)
);*/




/*const add_in_oset = (oset, vertex_index) =>
	oset.concat(vertex_index)
;

const remove_in_oset = (oset, index_of_vertex_index) =>
	oset.filter((_, i) => i !== index_of_vertex_index)
;*/

const add_in_oset = (oset, face_index, element) =>
	oset.map(
		(current_osubset, current_face_index) =>
			current_face_index === face_index
				? add_in_osubset(current_osubset, element)
				: current_osubset
	)
;

const remove_in_oset = (oset, element) =>
	oset.map(
		(current_osubset) =>
			set_osubset_list(
				current_osubset,
				osubset_element_list(current_osubset).filter(
					(current_element) => current_element !== element
				)
			)
	)
;

const first_osubset = (oset) =>
	value_in_list_by_index(oset, 0)
;

const remove_empty_osubset = (oset) =>
	oset.filter(
		(current_osubset) => is_defined(value_in_list_by_index(osubset_element_list(current_osubset), 0))
	)
;