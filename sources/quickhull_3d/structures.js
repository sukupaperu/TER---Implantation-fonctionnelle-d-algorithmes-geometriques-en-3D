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




const new_empty_oset = () =>
	new_empty_list()
;

const add_in_oset = (oset, vertex_index) =>
	oset.concat(vertex_index)
;

const remove_in_oset = (oset, index_of_vertex_index) =>
	oset.filter((_, i) => i !== index_of_vertex_index)
;